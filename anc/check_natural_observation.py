"""Exact finite checks of the largest-hit observation theorem.

The physical h=2 witness uses a finite stress amplitude and a small menu.
The independent signed-cube and bounded-rank checks cover h=2,3,4.
"""

from collections import Counter
from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, prod

from check_natural_window import (
    check_admissible, expected_cost, first_primes, is_prime, physical_cells,
    ranks, reference_cells, subsets,
)


def observed(cell, ell):
    return len(cell), cell[-ell:] if ell else ()


def project(law, ell):
    projected = Counter()
    for cell, mass in law.items():
        projected[observed(cell, ell)] += mass
    return {stat: mass for stat, mass in projected.items() if mass}


def add_cube(law, edge, coefficient):
    for cell in subsets(sorted(edge)):
        law[cell] += (-1) ** len(cell) * coefficient


def check_four_primes():
    primes = (3, 5, 7, 11)
    gains = {(3, 7), (5, 11)}
    losses = {(3, 11), (5, 7)}
    laws = [
        {pair: Fraction(2 + sign * (int(pair in gains) - int(pair in losses)), 12)
         for pair in combinations(primes, 2)}
        for sign in (1, -1)
    ]
    assert project(laws[0], 1) == project(laws[1], 1)
    best = [4, 4]
    for order in permutations(primes):
        cost = [
            sum(mass * (1 + min(order.index(p) for p in pair))
                for pair, mass in law.items())
            for law in laws
        ]
        assert sum(cost) == Fraction(10, 3)
        best = [min(previous, current) for previous, current in zip(best, cost)]
        if order[:2] == (3, 7):
            assert cost == [Fraction(7, 4), Fraction(19, 12)]
    assert best == [Fraction(19, 12)] * 2


def bin_trade(anchors, h, ell, g):
    """Unit signed trade and one order for each sign of the prefix sum."""
    s = ell + 1
    first = len(anchors)
    groups = [list(range(first+2*g*j, first+2*g*(j+1))) for j in range(s)]
    trade = Counter()
    for tail in product(*groups):
        tag = prod(1 if x in group[:g] else -1 for x, group in zip(tail, groups))
        for completion in combinations(anchors, h-s):
            add_cube(trade, (*completion, *tail), tag)
    positive = [i for tag in (0, 1) for group in groups for i in group[tag*g:(tag+1)*g]]
    negative = [groups[0][(i-first+g) % (2*g)] if i in groups[0] else i for i in positive]
    return trade, positive, negative


def check_cube(h, ell, g=2):
    s = ell + 1
    anchors = tuple(range(h-s+2))
    trade, pos, neg = bin_trade(anchors, h, ell, g)
    assert not project(trade, ell)
    assert project(trade, ell+1)
    low_changes = Counter()
    for cell, mass in trade.items():
        for lower in subsets(cell, min(h-1, len(cell))):
            low_changes[lower] += mass
    assert not any(low_changes.values())
    coefficient = comb(len(anchors), h-s)
    for direction, tail in ((1, pos), (-1, neg)):
        order = (*anchors, *tail)
        exact_shift = expected_cost(ranks(order), trade, 0)
        assert exact_shift == direction * coefficient * g**(s+1)


def check_rank_approximation():
    n, w = 6, 2
    checked = Counter()
    for order in permutations(range(n)):
        r = ranks(order)
        if any(abs(r[i]-(i+1)) > w for i in range(n)):
            continue
        for h in (2, 3, 4):
            for ell in range(1, h):
                for cell in combinations(range(n), h):
                    top = cell[-ell:]
                    exact = max(r[x] for x in cell)
                    approx = max(r[x] for x in top)
                    assert 0 <= exact-approx <= 2*w
                    if exact != approx:
                        assert cell[-1]-cell[-ell-1] <= 2*w
                    series = 0
                    for j in range(n):
                        in_prefix = all(r[x] <= j for x in top)
                        in_natural = top[-1] < j
                        if in_prefix != in_natural:
                            assert abs((top[-1]+1)-j) <= w
                        series += in_prefix-in_natural
                    assert series == (top[-1]+1)-approx
                    checked[h,ell] += 1
    return sum(checked.values())


def check_physical():
    # Enlarging the asymptotic cube budget permits a close prime quadruplet
    # even with 96 anchors. The physical density and low moments are checked.
    h, P, epsilon = 2, 100_000, Fraction(1, 2)
    anchors = tuple(range(96))
    base = next(x for x in range(180001, 199991, 2)
                if all(is_prime(x+offset) for offset in (0, 2, 6, 8)))
    primes = first_primes(P, len(anchors)) + [base+x for x in (0, 2, 6, 8)]
    tails = tuple(range(len(anchors), len(primes)))
    natural, reference = reference_cells(primes, h)
    physical = physical_cells(primes, h, P, epsilon)
    q = [Fraction(1, x) for x in primes]
    d = Fraction(1, 8*P**2)
    tied = reference.copy()
    for v in (1, 2):
        for tails_used in combinations(tails, v):
            anchor_factor = 1-sum(q[i] for i in anchors) if v == 1 else 1
            coefficient = ((-1)**v * (q[tails[1]]**v - prod(q[i] for i in tails_used))
                           * anchor_factor / comb(len(anchors), h-v))
            assert abs(coefficient) <= d/4
            for completion in combinations(anchors, h-v):
                add_cube(tied, (*completion, *tails_used), coefficient)
    check_admissible(tied, physical, natural, h, epsilon)
    exact_checks = 0
    for ell in (0, 1):
        g = len(tails) // (2*(ell+1))
        trade, pos, neg = bin_trade(anchors, h, ell, g)
        laws = [{cell: mass+direction*d/2*trade[cell] for cell, mass in tied.items()}
                for direction in (1, -1)]
        for law in laws:
            check_admissible(law, physical, natural, h, epsilon)
        assert project(laws[0],ell) == project(laws[1],ell)
        assert project(laws[0],ell+1) != project(laws[1],ell+1)
        # Anchor-only prefixes are common; count the within-tail costs directly.
        missed_anchors = lambda law: {cell: mass for cell,mass in law.items()
                                      if not cell or cell[0] >= len(anchors)}
        def after_anchors(order, law):
            lookup = {x:j for j,x in enumerate(order,1)}
            return sum(mass*(min(lookup[i] for i in cell) if cell else len(order)+4*P)
                       for cell,mass in law.items())
        common = missed_anchors(tied)
        conditioned = [missed_anchors(law) for law in laws]
        C0 = after_anchors(tails, common)
        effects = d/2*comb(len(anchors), h-ell-1)*g**(ell+2)
        costs = []
        for order in permutations(tails):
            assert after_anchors(order, common) == C0
            pair = [after_anchors(order, law) for law in conditioned]
            assert sum(pair) == 2*C0
            costs.append(pair)
        minima = list(map(min, zip(*costs)))
        assert after_anchors(pos,conditioned[1]) == C0-effects
        assert after_anchors(neg,conditioned[0]) == C0-effects
        assert all(sum(costs_for_order)-sum(minima) >= 2*effects for costs_for_order in costs)
        exact_checks += len(costs)
    return primes[-4:], exact_checks


if __name__ == '__main__':
    check_four_primes()
    for degree in (2, 3, 4):
        for keep in range(degree):
            check_cube(degree, keep)
    print('Nine signed-cube laws checked, including every smaller exact-hit layer.')
    print(f'{check_rank_approximation()} compressed rank/prefix identities checked.')
    primes, count = check_physical()
    print(f'Physical prime quadruplet {primes}: {count} paired-order identities, '
          'exact observed laws, natural low moments, and density bounds verified.')
