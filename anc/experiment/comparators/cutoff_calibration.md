# Calibrating a divisibility cutoff using proper multiples

On an Apple M4, an added batch of divisibility tests avoided about 415 ns of FLINT work per newly rejected composite under a uniform odd 64-bit workload. The corresponding time was about 292 ns for odd 48-bit words with the high bit set. Estimating this difference from forced multiples selected the best of nine measured cutoffs in five of six held-out comparisons. In the sixth comparison the chosen cutoff cost an extra 0.20 ns per integer.

## Which backend cost governs the cutoff?

Fix an order and let \(S_i\) be the event of surviving its first \(i\) batches. The batch may be a simultaneous arithmetic test of several divisors, or a lookup table of admissible residues. Let \(c_\pi(n)\) be the screening work actually performed under plan \(\pi\), including early exits, and let \(b(n)\) be the cost of a common exact fallback. Moving from cutoff \(i\) to \(j>i\) changes expected cost by

$$
\mathbb E[c_j(N)-c_i(N)]-\mathbb E[b(N)\mathbf1_{S_i\setminus S_j}].
$$

Only the fallback costs of the newly discovered composites enter this expression. A large cost for certifying a prime disappears because every cutoff must certify it. The identity allows unequal batch widths and costs. Applying it to machine timing assumes that running the screen and the fallback in succession can be modeled by the sum of their separate costs.

There is also a bound against an unrestricted set of alternative orders, batchings and stops. Let \(\pi_0\) minimize expected cost in a model with constant fallback \(\lambda\) and the specified screening costs. Let \(H\) be the event that at least one menu prime is a proper divisor, and let \(A_0\subseteq H\) be the event rejected by \(\pi_0\). Its excess under the varying fallback \(b\) is at most

$$
\mathbb E[(b-\lambda)_+\mathbf1_{H\setminus A_0}]
{}+\mathbb E[(\lambda-b)_+\mathbf1_{A_0}].
$$

Indeed for a competitor rejecting \(A\) the cost difference changes by \(\mathbb E[(b-\lambda)(\mathbf1_A-\mathbf1_{A_0})]\) on moving from \(\lambda\) to \(b\). Under the constant model the original difference is nonpositive. This bound requires no independence or monotonicity and holds for any candidate plan family with the same fallback. It gives zero if the backend has constant cost on menu-detectable composites, regardless of its cost on primes and undetectable composites. The experiments below assess the narrower task of choosing cutoffs. Estimating this unrestricted-order bound would also require the positive parts of the individual backend costs.

## Sampling a newly exposed composite

Suppose the source is uniform on \(L\) odd integers in a finite interval above every divisor. For a band \(J\) of newly added primes in a fixed order, let \(L_p\) count its multiples in the interval and set \(H_J=\sum_{p\in J}L_p/L\). Draw a ticket \((p,n)\) uniformly from the \(\sum L_p\) such pairs, using integer arithmetic to select the multiple. Retain it when \(p\) is the first menu factor of \(n\), including all earlier bands and the initial wheel. Each newly rejected word has exactly one retained ticket. Consequently the retained words are uniform conditional on being newly rejected. This is the disjoint representative used in classical union-size sampling. [Karp, Luby and Madras, 1989, §2](https://www.math.cmu.edu/~af1p/Teaching/MCC17/Papers/KLM.pdf)

Write \(X=b(N)\mathbf1_{\{\text{new hit}\}}\) for an ordinary draw. On a ticket draw use \(Y=H_J b(n)\mathbf1_{\{\text{retained}\}}\). Counting the unique retained ticket for each word gives

$$
\mathbb E Y=\mathbb E X,\qquad
\mathbb E Y^2=H_J\,\mathbb E X^2 .
$$

For \(H_J\le1\), \(\operatorname{Var}(Y)\le H_J\operatorname{Var}(X)\). The statement also holds for random costs with the same conditional first two moments given the word. This controls variability per **proposal**; time to generate tickets and identify the first factor must be counted separately. For the band from 1181 through 1627, exclusive of 1181, \(H_J=0.0456\). Among 65,536 proposals roughly 10,000 were retained, while roughly 460 ordinary words out of the same number would land in this band. Exact enumeration on three small intervals verified both moment identities with a varying synthetic cost.

## Held-out native measurements

The initial common wheel screens 3, 5, 7, 11 and 13. The nine candidate cutoffs end at primes \(13,139,349,733,1181,1627,2663,3677,5857\), and use four-way grouped inverse multiplications after the wheel. The implementation calls FLINT 3.6.0's native odd-word fallback. Each calibration times the screening code on 131,072 ordinary training words and generates 65,536 tickets for each of the eight added bands. It times the backend on the stream of retained words, so every timed word in a band differs across draws except for random repeats. It uses the median of seven passes for backend time. Its estimated backend saving is the measured time per retained word multiplied by \(H_J\) and the fraction retained. Cumulative savings and the measured screen-only time determine the selected cutoff.

For validation, a separate 196,608-word stream is timed end to end at each cutoff. Nine rounds balance which cutoff is timed first. Each full decision is also compared with the ordinary FLINT function. All 1,179,648 held-out words agreed across every cutoff. The second workload covers odd integers in \([2^{47},2^{48})\). The first covers odd 64-bit integers above \(2^{32}-1\). The seeds are 1277623, 543697219 and 8442377.

| Workload | Selected cutoff by seed | Fastest held-out cutoff by seed | Median time at 13 | Median time at 1181 | Median time at 1627 |
|---|---|---|---:|---:|---:|
| Uniform odd 64-bit | 1627, 1627, 1627 | 1627, 1627, 1627 | 185.65 ns | 108.80 ns | 108.23 ns |
| High-bit-set odd 48-bit | 1181, 733, 1181 | 1181, 1181, 1181 | 137.71 ns | 88.48 ns | 89.08 ns |

The held-out loss from choosing 733 on the second 48-bit seed was 0.197 ns per word, or 0.22%. The additive model underestimated the actual improvement over the wheel by 2.35–4.21 ns at the selected cutoffs. Separate timing cannot reproduce the full execution context of a combined short-circuit function. The earlier benchmark had already examined cutoffs near 1627. This experiment tests the choice on the nine stated candidates and one CPU, without establishing a globally optimal cutoff or a reduction in total autotuning time. The “13” comparison still performs the exact FLINT backend after the wheel. It measures the gain from adding batches to that particular plan.

The raw results report proposal mass, hit probability, sample counts, observed backend cost, predicted change and end-to-end time for every candidate and seed. The build uses the existing screen's wheel and the same 64-bit FLINT ABI. [Measured data](cutoff_results.csv) · [Calibration and measurement program](cutoff_calibration.cpp)

### Reusing the first band's backend time

We recalculated all candidate scores from the stored measurements using the backend time of the first added band, primes 17 through 139, for every subsequent band of the same seed and workload. This keeps the measured screening time and estimated hit probability of each band. The single-time rule selected exactly the same six cutoffs as the eight-time model. Both selected five of the six held-out winners and incurred 0.1969 ns per word on the remaining seed. Across the eight bands and three seeds, backend times were 414.05–416.55 ns for 64-bit words and 291.22–292.82 ns for 48-bit words. The extra band-specific timing measurements therefore produced no observed change in the selections on these workloads.

Run this standard-library calculation from the directory containing `cutoff_results.csv`. The four values printed after each workload and seed are the selected prime using one backend time, the selected prime using all eight, the held-out winner, and the single-time rule's held-out loss in ns per word.

~~~sh
python3 - <<'PY'
import csv
from collections import defaultdict

groups = defaultdict(list)
with open("cutoff_results.csv", newline="") as stream:
    for row in csv.DictReader(stream):
        groups[row["workload"], row["seed"]].append(row)

for (workload, seed), rows in groups.items():
    rows.sort(key=lambda r: int(r["cutoff"]))
    first_time = float(rows[1]["backend_on_hit_ns"])
    cumulative_hit = 0.0
    scores = []
    for row in rows:
        cumulative_hit += float(row["new_hit"])
        scores.append(float(row["screen_ns"]) - first_time * cumulative_hit)
    one = rows[min(range(len(rows)), key=scores.__getitem__)]
    eight = min(rows, key=lambda r: float(r["predicted_delta_ns"]))
    winner = min(rows, key=lambda r: float(r["heldout_ns"]))
    loss = float(one["heldout_ns"]) - float(winner["heldout_ns"])
    print(workload, seed, one["largest"], eight["largest"], winner["largest"], f"{loss:.4f}")
PY
~~~

### Reproducing the native measurements

~~~sh
clang++ -std=c++17 -O3 -mcpu=native cutoff_calibration.cpp -o /tmp/prime-cutoff-calibrate
/tmp/prime-cutoff-calibrate /path/to/libflint.dylib 1277623 u64
/tmp/prime-cutoff-calibrate /path/to/libflint.dylib 1277623 odd48
~~~
