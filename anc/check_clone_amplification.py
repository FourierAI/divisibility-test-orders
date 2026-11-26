"""Finite checks of the grouped-clone ordering and arithmetic sampling identities."""

from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, prod
from random import Random


def clone_edges(active, g):
    return [(g * i + u, g * j + v)
            for i, j in combinations(active, 2) for u in range(g) for v in range(g)]


def check_orders(m, g, k):
    n = m * g
    subsets = list(combinations(range(m), k))
    hidden_edges = [clone_edges(s, g) for s in subsets]
    all_edges = clone_edges(range(m), g)
    best = None
    best_prior = None
    for order in permutations(range(n)):
        ranks = {v: i + 1 for i, v in enumerate(order)}
        active_score = sum(min(ranks[u], ranks[v]) for u, v in hidden_edges[0])
        prior_score = sum(min(ranks[u], ranks[v]) for u, v in all_edges)
        best = active_score if best is None else min(best, active_score)
        best_prior = prior_score if best_prior is None else min(best_prior, prior_score)
    hidden_pairs = g * g * comb(k, 2)
    total_pairs = g * g * comb(m, 2)
    known = g * F(k + 1, 3) - F(g - 1, 2)
    prior = g * F(m + 1, 3) - F(g - 1, 2)
    assert F(best, hidden_pairs) == known
    assert F(best_prior, total_pairs) == prior
    assert (prior - known) * hidden_pairs == F(g**3 * comb(k, 2) * (m - k), 3)


def check_cells():
    m, g, k = 4, 2, 3
    p = (1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049)
    n, length = len(p), 2**25
    assert 4 * length < min(p)**3
    cells = [()] + [(i,) for i in range(n)] + list(combinations(range(n), 2))
    q, eps = F(1, min(p)), F(1, 2)
    d, u = eps * q**2 / 100, q**2 / 2
    b = [1 - n * q + comb(n, 2) * q**2, q - (n - 1) * q**2, q**2]

    def progression(cell):
        v = prod(p[i] for i in cell)
        first = 0 if v == 1 else (-(2 * length + 1) * pow(2, -1, v)) % v
        return first, v, 1 + (length - 1 - first) // v

    def masses(active):
        law = {s: b[len(s)] for s in cells}
        for i, j in clone_edges(active, g):
            for s in ((), (i,), (j,), (i, j)):
                law[s] += (-1)**len(s) * d
        return law

    active, other = (0, 1, 2), (0, 1, 3)
    law, other_law = masses(active), masses(other)
    assert sum(law.values()) == 1
    assert all(sum(prob for s, prob in law.items() if i in s) == q for i in range(n))
    predicted = {s: b[len(s)] for s in cells}
    active_edges = set(clone_edges(active, g))
    for i, j in clone_edges(range(m), g):
        for s in ((), (i,), (j,), (i, j)):
            predicted[s] -= u
    assert all(mass >= 0 for mass in predicted.values())
    for i, j in clone_edges(range(m), g):
        for s in ((), (i,), (j,), (i, j)):
            signal = (-1)**len(s) * d / u if (i, j) in active_edges else 0
            predicted[s] += (4 * u) * (1 + signal) / 4
    assert predicted == law
    ell = len(set(active) & set(other))
    excess = sum((law[s] - b[len(s)]) * (other_law[s] - b[len(s)]) / b[len(s)]
                 for s in cells)
    expected = d**2 * (g**2 * comb(ell, 2) / b[2] + g**3 * (k - 1)**2 * ell / b[1]
                       + g**4 * comb(k, 2)**2 / b[0])
    assert excess == expected

    counts = {}
    for s in reversed(cells):
        counts[s] = progression(s)[2] - sum(cnt for t, cnt in counts.items()
                                              if set(s) < set(t))
    assert min(counts.values()) > 0 and sum(counts.values()) == length
    ratios = [law[s] * length / counts[s] for s in cells]
    assert min(ratios) >= 1 - eps and max(ratios) <= 1 + eps
    rng = Random(20261126)
    for s in cells:
        first, v, count = progression(s)
        for _ in range(30):
            for _ in range(100):
                word = 2 * length + 1 + 2 * (first + v * rng.randrange(count))
                assert 2 * length <= word < 4 * length and word % 2 == 1
                hits = tuple(i for i, pi in enumerate(p) if word % pi == 0)
                assert set(s) <= set(hits)
                if hits == s:
                    break
            else:
                raise AssertionError("rejection sampler exceeded the finite check cap")
    return float(min(ratios)), float(max(ratios))


if __name__ == "__main__":
    check_orders(3, 2, 2)
    check_orders(4, 2, 3)
    lower, upper = check_cells()
    print("Exhaustive block optima and prior gains, cell laws, and second moments passed.")
    print(f"Verified arithmetic word/uniform ratios on all cells: {lower:.6f} to {upper:.6f}")
