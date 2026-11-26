"""Exact finite checks for menu_regret_certificate.tex.

The small-interval test counts native odd-word divisibility directly.
On the model's much longer dyadic intervals, exhaustive checks operate
on physical hit cells with exact rational masses.
"""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import isqrt, prod
from random import Random


def subsets(values, limit=None):
    values = tuple(values)
    if limit is None:
        limit = len(values)
    for size in range(min(limit, len(values)) + 1):
        yield from combinations(values, size)


def odd_multiple_count(length, divisor):
    """Count odd multiples of an odd divisor in [2L, 4L)."""
    lower = (2 * length + divisor - 1) // divisor
    upper = (4 * length - 1) // divisor
    return (upper + 1) // 2 - lower // 2


def check_native_counts():
    tests = 0
    for length in (1, 7, 17, 64):
        for divisor in (1, 3, 5, 7, 15, 35, 105):
            direct = sum(word % divisor == 0 for word in range(2 * length + 1, 4 * length, 2))
            assert odd_multiple_count(length, divisor) == direct
            tests += 1
    return tests


def first_primes(start, count):
    primes = []
    candidate = start | 1
    while len(primes) < count:
        if all(candidate % d for d in range(3, isqrt(candidate) + 1, 2)):
            primes.append(candidate)
        candidate += 2
    return tuple(primes)


def dyadic_length(P, h, epsilon):
    needed = 1000 * (2 * P) ** h / epsilon
    lower = -(-needed.numerator // needed.denominator)
    return 1 << (lower - 1).bit_length()


def exact_cells(moments):
    masses = defaultdict(F)
    for hits, value in moments.items():
        for cell in subsets(hits):
            masses[cell] += (-1) ** (len(hits) - len(cell)) * value
    return masses


def make_box(primes, P, h, epsilon, exact_low):
    length = dyadic_length(P, h, epsilon)
    assert 4 * length < P ** (h + 1)
    assert 8 * len(primes) <= P and all(P <= p <= 2 * P for p in primes)
    uniform_moments = {}
    box = {}
    for T in subsets(range(len(primes)), h):
        divisor = prod(primes[i] for i in T)
        uniform = F(odd_multiple_count(length, divisor), length)
        center = F(1, divisor)
        assert abs(uniform - center) <= F(1, length)
        uniform_moments[T] = uniform
        if len(T) == h:
            box[T] = (1 - epsilon) * uniform, (1 + epsilon) * uniform
        elif T:
            slack = F(0) if exact_low else F(1, length)
            box[T] = center - slack, center + slack
    physical = exact_cells(uniform_moments)
    assert sum(physical.values()) == 1
    assert all(probability > 0 and (probability * length).denominator == 1
               for probability in physical.values())
    return box, physical


def realize(moments, physical, epsilon):
    """Lift cell masses by assigning uniform density inside each cell."""
    cells = exact_cells({(): F(1), **moments})
    assert sum(cells.values()) == 1
    for cell, mass in cells.items():
        assert abs(mass - physical[cell]) <= epsilon * physical[cell]
    return cells


def direct_cost(order, cells, P):
    ranks = {test: rank for rank, test in enumerate(order, 1)}
    exhaustion = len(order) + 4 * P
    return sum(probability * min((ranks[i] for i in cell), default=exhaustion)
               for cell, probability in cells.items())


def survival_cost(order, cells, P):
    """Sum directly over exact physical cells that survive each prefix."""
    surviving = dict(cells)
    total = F(0)
    for i in order:
        total += sum(surviving.values())
        surviving = {cell: mass for cell, mass in surviving.items() if i not in cell}
    return total + 4 * P * sum(surviving.values())


def direct_witness(sigma, competitor, box, P):
    """Optimize the box by differentiating direct cell losses."""
    rank_sigma = {i: r for r, i in enumerate(sigma, 1)}
    rank_competitor = {i: r for r, i in enumerate(competitor, 1)}
    exhaustion = len(sigma) + 4 * P

    def loss_difference(cell):
        return (min((rank_sigma[i] for i in cell), default=exhaustion)
                - min((rank_competitor[i] for i in cell), default=exhaustion))

    witness = {}
    for T, (low, high) in box.items():
        derivative = sum((-1) ** (len(T) - len(cell)) * loss_difference(cell)
                         for cell in subsets(T))
        witness[T] = high if derivative > 0 else low
    return witness


def worst_regret(sigma, box, h):
    """Subset DP based on charging a moment when its last test enters."""
    m = len(sigma)
    ranks = {i: r for r, i in enumerate(sigma, 1)}
    last = {T: max(ranks[i] for i in T) for T in box}
    values = {(): F(0)}
    orders = {(): ()}
    for S in subsets(range(m)):
        if not S:
            continue
        choices = []
        for i in S:
            previous = tuple(j for j in S if j != i)
            increment = F(0)
            for smaller in subsets(previous, h - 1):
                T = tuple(sorted(smaller + (i,)))
                slope = (-1) ** len(T) * (len(S) - last[T])
                increment += max(slope * endpoint for endpoint in box[T])
            choices.append((values[previous] + increment, orders[previous] + (i,)))
        values[S], orders[S] = max(choices)
    full = tuple(range(m))
    return values[full], orders[full]


def robust_prefix_difference(R, A, box, h):
    """Minimum survival difference, with positive sign favoring A."""
    left, right = set(subsets(R, h)), set(subsets(A, h))
    return (sum(min((-1) ** len(T) * x for x in box[T]) for T in left - right)
            + sum(min(-(-1) ** len(T) * x for x in box[T]) for T in right - left))


def check_adjacent(exact_low):
    P, h, m = 1_000_003, 2, 11
    primes = first_primes(P, m)
    sigma = tuple(range(m))
    regimes = defaultdict(int)
    comparisons = 0
    rng = Random(20261126)
    for eps_numerator in range(4, 51, 4):
        epsilon = F(eps_numerator, 100)
        box, physical = make_box(primes, P, h, epsilon, exact_low)
        gains = []
        for t in range(1, m):
            prefix = tuple(range(t - 1))
            gains.append(robust_prefix_difference(prefix + (t,), range(t), box, h))
        if min(gains) >= 0:
            regimes["robust"] += 1
            assert min(gains) > 0
            for size in range(1, m):
                for R in combinations(range(m), size):
                    assert robust_prefix_difference(R, range(size), box, h) >= 0
                    comparisons += 1
        else:
            regimes["nonrobust"] += 1
            t = 1 + min(range(len(gains)), key=gains.__getitem__)
            swap = sigma[:t - 1] + (t, t - 1) + sigma[t + 1:]
            law = realize(direct_witness(sigma, swap, box, P), physical, epsilon)
            assert direct_cost(sigma, law, P) - direct_cost(swap, law, P) == -gains[t - 1] > 0
        for _ in range(5):
            realize({T: rng.choice(interval) for T, interval in box.items()}, physical, epsilon)
    assert regimes["robust"] and regimes["nonrobust"]
    return regimes, comparisons


def check_dp(P, m, h, epsilon, exact_low, every_corner=False):
    primes = first_primes(P, m)
    box, physical = make_box(primes, P, h, epsilon, exact_low)
    increasing = tuple(range(m))
    arbitrary = increasing[1::2] + increasing[::2]
    order_list = tuple(permutations(range(m)))
    comparisons = 0
    for sigma in (increasing, arbitrary):
        value, comparator = worst_regret(sigma, box, h)
        direct_maximum = F(0)
        for pi in order_list:
            law = realize(direct_witness(sigma, pi, box, P), physical, epsilon)
            difference = direct_cost(sigma, law, P) - direct_cost(pi, law, P)
            direct_maximum = max(direct_maximum, difference)
            if pi == comparator:
                assert difference == value
                assert survival_cost(sigma, law, P) - survival_cost(pi, law, P) == value
            comparisons += 1
        assert value == direct_maximum
        if sigma == arbitrary:
            assert value > 0
        if every_corner:
            corner_maximum = F(0)
            choices = [(low,) if low == high else (low, high) for low, high in box.values()]
            for corner in product(*choices):
                law = realize(dict(zip(box, corner)), physical, epsilon)
                regret = direct_cost(sigma, law, P) - min(
                    direct_cost(pi, law, P) for pi in order_list
                )
                corner_maximum = max(corner_maximum, regret)
            assert value == corner_maximum
    return comparisons


if __name__ == "__main__":
    print(f"{check_native_counts()} odd-multiple counts match direct word enumeration.")
    for exact_low in (False, True):
        label = "Exact lower moments" if exact_low else "Rounded lower moments"
        regimes, count = check_adjacent(exact_low)
        print(f"{label}: {regimes['robust']} robust and {regimes['nonrobust']} nonrobust "
              f"settings, {count} exact prefix comparisons.")
    total = sum(check_dp(P, m, h, epsilon, exact_low, every_corner)
                for P, m, h, epsilon, every_corner in (
                    (1_000_003, 4, 2, F(1, 2), True),
                    (1_000_003, 5, 2, F(1, 2), False),
                    (100_000_007, 6, 3, F(1, 5), False),
                ) for exact_low in (False, True))
    print(f"{total} exact order/witness comparisons agree with subset DP. "
          "All 1,088 four-prime box corners checked.")
