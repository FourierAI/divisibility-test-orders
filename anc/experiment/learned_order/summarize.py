"""Recalculate timings, probe costs, checks and paired amortization from raw CSVs."""
import csv
import math
import sys
from collections import defaultdict
from pathlib import Path
from statistics import median

METHODS = ("flint", "packet", "increasing", "marginal_A", "joint_A", "joint_B")
LAWS = ("A", "B", "uniform-odd")
EDGES = {
    "A": [(0, 1), (2, 3), (4, 5), (6, 7), (8, 9), (10, 11)],
    "B": [(0, 2), (4, 6), (8, 10), (1, 3), (5, 7), (9, 11)],
}


def read(folder, filename):
    with (folder / filename).open(newline="") as stream:
        return list(csv.DictReader(stream))


def count_probes(order, mask):
    return next((rank for rank, index in enumerate(order, 1) if mask & (1 << index)), 12)


def decode(order):
    values = tuple(map(int, order.split("-")))
    assert sorted(values) == list(range(12))
    return values


def residual_greedy(freq):
    remaining = set(range(12))
    live = dict(freq)
    result = []
    while remaining:
        def gain(i):
            return sum(n for mask, n in live.items() if mask & (1 << i))
        best = min(remaining, key=lambda i: (-gain(i), i))
        result.append(best)
        remaining.remove(best)
        live = {mask: n for mask, n in live.items() if not mask & (1 << best)}
    return tuple(result)


def analyze(folder):
    timings = defaultdict(list)
    for row in read(folder, "timings.csv"):
        key = int(row["rep"]), row["law"], row["method"]
        timings[key].append(float(row["ns_per_word"]))
    costs = {k: median(data) for k, data in timings.items()}
    assert len(costs) == 54 and all(len(data) == 12 for data in timings.values())
    training = defaultdict(list)
    schedules = {}
    for row in read(folder, "training.csv"):
        rep, law = int(row["rep"]), row["law"]
        key = rep, law
        training[key].append(tuple(int(row[k]) for k in
                                   ("acquire_ns", "marginal_fit_ns", "joint_fit_ns")))
        observed = decode(row["marginal_order"]), decode(row["joint_order"])
        assert schedules.setdefault(key, observed) == observed
    assert len(training) == 6 and all(len(v) == 9 for v in training.values())
    histograms = defaultdict(dict)
    for row in read(folder, "histograms.csv"):
        key = row["partition"], int(row["rep"]), row["law"]
        histograms[key][int(row["mask"])] = int(row["count"])
    for (partition, rep, law), freq in histograms.items():
        assert sum(freq.values()) == (8192 if partition == "train" else 65536)
        if law in EDGES:
            assert set(freq) == {0} | {(1 << i) | (1 << j) for i, j in EDGES[law]}
        if partition == "train":
            # One fresh endpoint per edge, in empirical descending mass, is optimal.
            joint = schedules[rep, law][1]
            assert residual_greedy(freq) == joint
            edges = {sum(1 << i for i in edge) for edge in EDGES[law]}
            oracle = 12 * freq[0] + sum(r * w for r, w in enumerate(
                sorted((freq[mask] for mask in edges), reverse=True), 1))
            assert oracle == sum(count_probes(joint, mask) * v for mask, v in freq.items())
    probes = {}
    correct = {}
    for row in read(folder, "holdout.csv"):
        rep, law, method = int(row["rep"]), row["law"], row["method"]
        assert correct.setdefault((rep, law), int(row["primes"])) == int(row["primes"])
        if method in METHODS[2:]:
            order = {"increasing": tuple(range(12)), "marginal_A": schedules[rep, "A"][0],
                     "joint_A": schedules[rep, "A"][1], "joint_B": schedules[rep, "B"][1]}[method]
            freq = histograms["test", rep, law]
            expected = sum(count_probes(order, mask) * count for mask, count in freq.items())
            # The archived test seeds have no inputs <= UINT32_MAX.
            assert expected == int(row["total_leading_probes"])
            probes[rep, law, method] = expected / int(row["inputs"])

    print(folder, f"{sum(correct.values()):,} verified primes over 589,824 distinct input slots")
    print("law method median_of_seed_median_ns mean_heldout_probes_per_word")
    for law in LAWS:
        for method in METHODS:
            t = median(costs[rep, law, method] for rep in range(3))
            q = (f"{sum(probes[rep,law,method] for rep in range(3))/3:.4f}"
                 if method in METHODS[2:] else "-")
            print(f"{law:11s} {method:10s} {t:7.2f} {q}")
    print("Training on A, median times across the three replicate medians (ns)")
    profile = [list() for _ in range(4)]
    for rep in range(3):
        rows = training[rep, "A"]
        for j in range(3):
            profile[j].append(median(row[j] for row in rows))
        profile[3].append(median(a + j for a, m, j in rows))
    print("acquire, marginal_fit, joint_fit, acquire+joint:", *map(median, profile))
    print("A matched seed-wise saving ns, and break-even future calls (in rep order)")
    for method in METHODS[:4]:
        saving = [costs[rep, "A", method] - costs[rep, "A", "joint_A"] for rep in range(3)]
        thresholds = []
        for rep, benefit in enumerate(saving):
            rows = training[rep, "A"]
            # Full training vs zero-training fixed methods; marginal and joint
            # use identical census acquisition, so only the fit costs differ.
            overhead = median((j - m if method == "marginal_A" else a + j)
                              for a, m, j in rows)
            thresholds.append(str(math.ceil(overhead / benefit)) if benefit > 0 else "never")
        print(method, " ".join(f"{s:.3f}" for s in saving), ";", " ".join(thresholds))
    return histograms, schedules, probes, correct


def control(path):
    groups = defaultdict(list)
    method_names = []
    for row in read(path.parent, path.name):
        name = row["method"]
        if name not in method_names:
            method_names.append(name)
        groups[int(row["rep"]), row["law"], name].append(float(row["ns_per_word"]))
    assert len(groups) == 54 and all(len(rows) == 12 for rows in groups.values())
    print(path.name)
    for law in LAWS:
        print(law, " ".join(
            f"{name}={median(median(groups[r,law,name]) for r in range(3)):.2f}"
            for name in method_names))
    return {k: median(v) for k, v in groups.items()}


def cutoff_checks(base, first, detailed):
    histograms, schedules, _, _ = first
    for law in LAWS:
        found = [0] * 4
        for rep in range(3):
            orders = (tuple(range(12)), *schedules[rep, "A"], schedules[rep, "B"][1])
            freq = histograms["test", rep, law]
            for j, order in enumerate(orders):
                six = sum(1 << i for i in order[:6])
                found[j] += sum(n for mask, n in freq.items() if mask & six)
        print(f"Six-prefix hit percentages {law} (inc, marginal A, joint A, joint B):",
              *(f"{100 * n / (3 * 65536):.4f}" for n in found))
    greedy = defaultdict(list)
    for row in read(base, "greedy_cost.csv"):
        rep, law = int(row["rep"]), row["law"]
        assert decode(row["order"]) == schedules[rep, law][1]
        greedy[rep, law].append(tuple(int(row[k]) for k in ("acquire_ns", "greedy_fit_ns", "joint_fit_ns")))
    assert len(greedy) == 6 and all(len(v) == 9 for v in greedy.values())
    print("Checked greedy=DP complete schedules for all six training sets.")
    print("Greedy experiment A median-of-seed medians, ns: acquisition, greedy, DP, acquisition+greedy:",
          *(median(median(row[i] for row in greedy[rep, "A"]) for rep in range(3)) for i in range(3)),
          median(median(a+g for a,g,j in greedy[rep, "A"]) for rep in range(3)))
    for folder, name in (("results", "six_control.csv"), ("repeat", "six_repeat.csv")):
        timing = detailed[name]
        original = defaultdict(list)
        for row in read(base / folder, "training.csv"):
            if row["law"] == "A":
                original[int(row["rep"])].append(tuple(int(row[k]) for k in
                                  ("acquire_ns", "marginal_fit_ns", "joint_fit_ns")))
        for other in ("all_runtime", "six_marginal_A"):
            for fitter in ("joint", "greedy"):
                if fitter == "greedy" and other == "six_marginal_A":
                    # Their near-equal fit times were measured in different sessions.
                    continue
                threshold = []
                for rep in range(3):
                    delta = timing[rep, "A", other] - timing[rep, "A", "six_joint_A"]
                    if fitter == "joint":
                        added = median((a + j if other == "all_runtime" else j - m)
                                       for a, m, j in original[rep])
                    else:
                        added = median(a + g for a, g, j in greedy[rep, "A"])
                    threshold.append(math.ceil(max(0, added)/delta) if delta > 0 else "never")
                print(name, fitter, "vs", other, "paired amortization", *threshold)


if __name__ == "__main__":
    base = Path(__file__).resolve().parent
    locations = [Path(arg) for arg in sys.argv[1:]] or [base / "results", base / "repeat"]
    first = None
    for path in locations:
        data = analyze(path)
        if first is not None:
            assert data == first, "input or schedule differs between timing sessions"
        first = data
    if len(sys.argv) == 1:
        detailed = {}
        for name in ("batch_control.csv", "batch_repeat.csv", "six_control.csv", "six_repeat.csv"):
            path = base / name
            if path.exists():
                detailed[name] = control(path)
        if (base / "greedy_cost.csv").exists() and "six_repeat.csv" in detailed:
            cutoff_checks(base, first, detailed)
