"""Exact checks of the arithmetic model in natural_window.tex.

The physical odd-word law is counted by congruences, without enumerating the
interval. All probability and cost comparisons use Fraction.
"""

from fractions import Fraction
from itertools import combinations, permutations
from math import comb, isqrt, prod


def subsets(values, degree=None):
    values = tuple(values)
    if degree is None:
        degree = len(values)
    for size in range(degree + 1):
        yield from combinations(values, size)


def invert_containment(containment):
    exact = containment.copy()
    for cell in sorted(exact, key=len, reverse=True):
        for smaller in subsets(cell, len(cell) - 1):
            exact[smaller] -= exact[cell]
    return exact


def containment_of(exact):
    containment = dict.fromkeys(exact, Fraction(0))
    for exact_cell, mass in exact.items():
        for cell in subsets(exact_cell):
            containment[cell] += mass
    return containment


def is_prime(n):
    return n > 1 and (n == 2 or n % 2 != 0 and
                       all(n % p for p in range(3, isqrt(n) + 1, 2)))


def first_primes(start, count):
    result = []
    n = start | 1
    while len(result) < count:
        if is_prime(n):
            result.append(n)
        n += 2
    return result


def physical_cells(primes, h, P, epsilon):
    needed = Fraction(1000 * (2 * P) ** h, epsilon)
    least_integer = -(-needed.numerator // needed.denominator)
    length = 1 << (least_integer - 1).bit_length()
    assert 4 * length < P ** (h + 1)
    containment = {}
    for cell in subsets(range(len(primes)), h):
        modulus = prod(primes[i] for i in cell)
        first = (-(2 * length + 1) * pow(2, -1, modulus)) % modulus if cell else 0
        count = 0 if first >= length else 1 + (length - 1 - first) // modulus
        containment[cell] = Fraction(count, length)
    return invert_containment(containment)


def reference_cells(primes, h):
    containment = {
        cell: Fraction(1, prod(primes[i] for i in cell))
        for cell in subsets(range(len(primes)), h)
    }
    return containment, invert_containment(containment)


def tilted_cells(baseline, anchors, signs, h, d):
    result = baseline.copy()
    for core in combinations(anchors, h - 1):
        for tail, sign in signs.items():
            for cell in subsets(tuple(sorted((*core, tail)))):
                result[cell] += (-1) ** len(cell) * d * sign
    return result


def check_admissible(law, actual_uniform, natural, h, epsilon):
    assert sum(law.values()) == 1
    for cell, p in law.items():
        assert p > 0 and actual_uniform[cell] > 0
        assert (1 - epsilon) * actual_uniform[cell] <= p <= (1 + epsilon) * actual_uniform[cell]
    moments = containment_of(law)
    assert all(moments[cell] == p for cell, p in natural.items() if len(cell) < h)
    return moments


def ranks(permutation):
    rank = [0] * len(permutation)
    for index, prime in enumerate(permutation, 1):
        rank[prime] = index
    return rank


def expected_cost(rank, law, cost_of_miss):
    m = len(rank)
    return sum(p * (min(rank[i] for i in cell) if cell else m + cost_of_miss)
               for cell, p in law.items())


def linear_coefficients(primes, h, law):
    # Running elementary symmetric polynomials of the primes before this bin.
    e = [Fraction(1)] + [Fraction(0)] * (h - 2)
    tops = [Fraction(0)] * len(primes)
    for cell, p in law.items():
        if len(cell) == h:
            tops[cell[-1]] += p
    totals = []
    for j, p in enumerate(primes):
        q = Fraction(1, p)
        totals.append(q * sum((-1) ** (t + 1) * value for t, value in enumerate(e))
                      + (-1) ** h * tops[j])
        for t in range(len(e) - 1, 0, -1):
            e[t] += q * e[t - 1]
    return totals


def check_cost_and_pair_kl(h):
    P = 1_000_000
    epsilon = Fraction(1, 2)
    primes = first_primes(P, 3) + first_primes(8 * P // 5, 3)
    m, anchors = len(primes), (0, 1, 2)
    signs = {3: 1, 4: -1, 5: 1}
    d = epsilon / (1000 * (2 * P) ** h)
    actual = physical_cells(primes, h, P, epsilon)
    natural, reference = reference_cells(primes, h)
    left = tilted_cells(reference, anchors, signs, h, d)
    right = tilted_cells(reference, anchors, {**signs, 3: -1, 4: 1}, h, d)
    moments = check_admissible(left, actual, natural, h, epsilon)
    check_admissible(right, actual, natural, h, epsilon)

    for cell in left:
        affected_tails = set(cell).intersection((3, 4))
        remaining = set(cell).difference(affected_tails)
        if len(affected_tails) == 1 and remaining.issubset(anchors):
            tail = affected_tails.pop()
            ell = len(remaining)
            expected = (2 * d * signs[tail] * (-1) ** len(cell)
                        * comb(len(anchors) - ell, h - 1 - ell))
        else:
            expected = 0
        assert left[cell] - right[cell] == expected, cell

    # Exact upper bound on KL, split into the shells used in the proof.
    chi_squared = sum((left[cell] - right[cell]) ** 2 / right[cell] for cell in left)
    shell_bound = sum(
        16 * d**2 * comb(len(anchors), ell)
        * comb(len(anchors) - ell, h - 1 - ell) ** 2 * (2 * P) ** (ell + 1)
        for ell in range(h)
    )
    assert 0 < chi_squared <= shell_bound
    assert shell_bound <= 32 * 2**h * d**2 * m ** (h - 1) * P**h

    weights = linear_coefficients(primes, h, left)
    independently_grouped = [sum((-1) ** len(cell) * p for cell, p in moments.items()
                                  if cell and cell[-1] == i) for i in range(m)]
    assert weights == independently_grouped
    reference_costs = {order: expected_cost(ranks(order), reference, 4 * P)
                       for order in permutations(range(m))}
    rates = [Fraction(1, p) for p in primes]
    prefix_factor = {}
    for prefix in subsets(range(m)):
        prefix_factor[frozenset(prefix)] = sum(
            (-1) ** len(cell) * natural[cell] for cell in subsets(prefix, h - 1)
        )
    integrated = rates.copy()
    for i in range(m - 2, -1, -1):
        gap = rates[i] - rates[i + 1]
        integrated[i] = integrated[i + 1] + gap * prefix_factor[frozenset(range(i))]
    for order, old_cost in reference_costs.items():
        for pos in range(m - 1):
            j, i = order[pos:pos + 2]
            if j <= i:
                continue
            after = order[:pos] + (i, j) + order[pos + 2:]
            common = prefix_factor[frozenset(order[:pos])]
            improvement = old_cost - reference_costs[after]
            assert improvement == (rates[i] - rates[j]) * common
            discrepancy = sum(
                (rates[k] - rates[k + 1]) * (common - prefix_factor[frozenset(range(k))])
                for k in range(i, j)
            )
            assert improvement == integrated[i] - integrated[j] + discrepancy
    w = 2
    close_cells = {cell for cell in moments if len(cell) >= 2 and cell[-1] - cell[-2] <= 2 * w}
    bound = 2 * w * sum(moments[cell] for cell in close_cells)
    coarse = 2 * w * sum(2 * w * m * comb(m, t - 2)
                         * max(p for cell, p in moments.items() if len(cell) == t)
                         for t in range(2, h + 1))
    assert bound <= coarse
    band_costs = []
    best_true = None
    for order in permutations(range(m)):
        rank = ranks(order)
        true_cost = expected_cost(rank, left, 4 * P)
        best_true = true_cost if best_true is None else min(best_true, true_cost)
        expansion = sum((-1) ** len(cell) * p * (m - max(rank[i] for i in cell))
                        for cell, p in moments.items() if cell)
        assert true_cost == m + 4 * P * left[()] + expansion
        if any(abs(rank[i] - (i + 1)) > w for i in range(m)):
            continue
        for cell in moments:
            if len(cell) >= 2 and cell not in close_cells:
                assert max(rank[i] for i in cell) == rank[cell[-1]]
        approximation = sum(weights[i] * (m - rank[i]) for i in range(m))
        assert abs(approximation - expansion) <= bound
        band_costs.append((approximation, true_cost))
    assert min(cost for _, cost in band_costs) == best_true
    best_surrogate = min(score for score, _ in band_costs)
    assert all(cost <= best_true + 2 * bound for score, cost in band_costs
               if score == best_surrogate)
    print(f"h={h}: 720 exact full-order costs, {len(band_costs)} banded "
          "approximations, cube signs and pair KL cancellation OK")


def survival(law, prefix):
    chosen = frozenset(prefix)
    return sum(p for cell, p in law.items() if chosen.isdisjoint(cell))


def check_interleaved_bins():
    # Enlarge d relative to the asymptotic theorem constant so genuine twin
    # primes land in one bin even with only 64 anchors. The pointwise condition
    # is still checked against the actual physical odd-word law.
    h, P = 2, 100_000
    epsilon = Fraction(1, 2)
    anchor_primes = first_primes(P, 64)
    anchors = tuple(range(len(anchor_primes)))
    d = Fraction(1, 6 * P**2)
    s = len(anchors) * d
    g = P**2 * s / 4
    low = 8 * P // 5
    twins = []
    for p in range(low + 1, 2 * P - 2, 2):
        bin_index = (p - low) // g
        if bin_index == (p + 2 - low) // g and is_prime(p) and is_prime(p + 2):
            if not twins or bin_index != twins[-1][0]:
                twins.append((bin_index, p, p + 2))
            if len(twins) == 2:
                break
    assert len(twins) == 2
    primes = anchor_primes + [p for _, first, second in twins for p in (first, second)]
    actual = physical_cells(primes, h, P, epsilon)
    natural, reference = reference_cells(primes, h)
    a, b, c, d_index = range(len(anchors), len(anchors) + 4)
    signs = {a: 1, b: -1, c: 1, d_index: -1}
    law = tilted_cells(reference, anchors, signs, h, d)
    check_admissible(law, actual, natural, h, epsilon)
    for p, q in ((a, b), (c, d_index)):
        assert (primes[p] - low) // g == (primes[q] - low) // g
        assert primes[q] - primes[p] <= g
    assert (primes[b] - low) // g < (primes[c] - low) // g

    order = [*anchors, a, c, b, d_index]  # Both bins are initially interleaved.
    before = expected_cost(ranks(order), law, 4 * P)
    for plus, minus in ((a, b), (c, d_index)):
        left, right = order.index(plus), order.index(minus)
        assert right - left > 1
        prior_order = order.copy()
        order[left], order[right] = order[right], order[left]
        for prefix_len in range(left + 1, right + 1):
            old_prefix = prior_order[:prefix_len]
            new_prefix = order[:prefix_len]
            reference_change = survival(reference, old_prefix) - survival(reference, new_prefix)
            law_change = survival(law, old_prefix) - survival(law, new_prefix)
            assert abs(reference_change) <= g / P**2
            assert law_change - reference_change == 2 * s
            assert law_change >= s
        other = {a, b, c, d_index}.difference((plus, minus))
        assert [i for i in prior_order if i in other] == [i for i in order if i in other]
    after = expected_cost(ranks(order), law, 4 * P)
    assert tuple(order[-4:]) == (b, d_index, a, c)
    assert before - after >= 2 * s
    print(f"interleaved bins {twins[0][1:]} and {twins[1][1:]}: "
          "two nonadjacent sign exchanges, four exact prefix gains OK")


if __name__ == "__main__":
    for degree in (2, 3, 4):
        check_cost_and_pair_kl(degree)
    check_interleaved_bins()
