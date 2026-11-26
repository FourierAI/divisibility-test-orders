"""Exact finite checks of ordinary logs censored at the r-th hit.

An unsaturated log exhausts the trial order; a saturated log reports no
total hit count. Labels are zero-based and the logged priority is public.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import comb

from check_natural_observation import add_cube, bin_trade
from check_natural_window import (
    check_admissible, expected_cost, first_primes, physical_cells, ranks,
    reference_cells, subsets,
)


def pushforward(law, order, r):
    pos = {a: j for j, a in enumerate(order)}
    result = Counter()
    for cell, mass in law.items():
        hit = tuple(sorted(cell, key=pos.__getitem__)[:r])
        result[hit] += mass
    return {v: mass for v, mass in result.items() if mass}


def check_cube_image():
    cases = 0
    for h in (2, 3, 4):
        edge = tuple(range(h))
        cube = Counter()
        add_cube(cube, edge, (-1)**h)  # Unit change in the h-cell.
        for order in permutations(edge):
            for r in range(1, h+1):
                exact = pushforward(cube, order, r)
                target = {v: (-1)**(h-len(v)) for v in subsets(order, r-1)}
                target.update({v: (-1)**(h-r) for v in combinations(order, r)
                               if order[-1] in v})
                assert exact == target
                cases += 1
    return cases


def check_physical_inversion():
    h, m, P, epsilon = 4, 7, 1_000_000, Q(1, 2)
    primes = first_primes(P, m)
    natural, baseline = reference_cells(primes, h)
    uniform = physical_cells(primes, h, P, epsilon)
    tilted = baseline.copy()
    size = Q(1, 1000*(2*P)**h)
    edges = {edge: size * ((sum((j+1)*(i+1) for j, i in enumerate(edge)) % 9)-4)
             for edge in combinations(range(m), h)}
    for edge, weight in edges.items():
        add_cube(tilted, edge, (-1)**h*weight)
    check_admissible(tilted, uniform, natural, h, epsilon)
    checks = 0
    for order in (tuple(range(m)), tuple(reversed(range(m))), (2, 0, 6, 1, 5, 3, 4)):
        pos = {a: j for j, a in enumerate(order)}
        for r in range(1, h+1):
            null, actual = (pushforward(law, order, r) for law in (baseline, tilted))
            for j, a in enumerate(order):
                for B in subsets(order[:j], r-1):
                    target = sum(w for edge, w in edges.items()
                                 if max(edge, key=pos.__getitem__) == a and set(B) <= set(edge))
                    known = sum((actual[v]-null[v]) for v in actual
                                if len(v) == r and v[-1] == a and set(B) <= set(v))
                    assert (-1)**(h-r)*known == comb(h-1-len(B), r-1-len(B))*target
                    checks += 1
    return checks


def check_local_prefix():
    m, W = 6, 2
    checked = 0
    for order in permutations(range(m)):
        pos = ranks(order)
        if any(abs(j+1-pos[j]) > W for j in range(m)):
            continue
        for k in range(1, m):
            prefix = frozenset(order[:k])
            for h in (2, 3, 4):
                for H in combinations(range(m), h):
                    a = H[-1]
                    missing = sum(i not in prefix for i in H[:-1])
                    for r in range(1, h+1):
                        true = int(all(i in prefix for i in H))-int(a < k)
                        truncated = (a in prefix)*sum((-1)**j*comb(missing, j)
                                                      for j in range(r))-int(a < k)
                        if truncated != true:
                            assert a in prefix and missing >= r
                            assert sum(x >= a-2*W for x in H[:-1]) >= r
                        if abs((a+1)-k) > W:
                            assert truncated == true == 0
                        checked += 1
    return checked


def check_invisible_trades():
    cases = 0
    for h in (2, 3, 4):
        for r in range(1, h):
            g = 2
            anchors = tuple(range(h-r))
            trade, pos, neg = bin_trade(anchors, h, r, g)
            natural = (*anchors, *sorted(pos))
            assert not pushforward(trade, natural, r)
            assert pushforward(trade, natural, r+1)
            gain = comb(len(anchors), h-r-1)*g**(r+2)
            assert expected_cost(ranks((*anchors, *pos)), trade, 0) == gain
            assert expected_cost(ranks((*anchors, *neg)), trade, 0) == -gain
            # Varying the public order can distinguish even with r=1:
            # no prefix hit integrates the signed cubes whose edge is in it.
            firsts = (*anchors, *pos[:g*(r+1)])
            other = tuple(i for i in natural if i not in firsts)
            changed = pushforward(trade, (*firsts, *other), 1)
            assert sum(x for v, x in changed.items() if not v or v[0] in other) != 0
            cases += 1
    return cases


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def check_priority_chi_square():
    """Every priority of small menus, including anchor-only saturated records."""
    checks = 0
    for h in (2, 3, 4):
        a, P = h, 32
        labels = tuple(range(a+2))
        x, y = labels[-2:]
        # A fixed positive null with comparable k-cell mass at each level.
        # The separate arithmetic check above uses exact physical primes.
        _, null = reference_cells([P]*len(labels), h)
        d = Q(1, 64*P**h)
        shift = Counter()
        for core in combinations(range(a), h-1):
            add_cube(shift, (*core, x), 1)
            add_cube(shift, (*core, y), -1)
        assert all(value-d*abs(shift[cell]) >= Q(1, 2*P**len(cell))
                   for cell, value in null.items())
        anchor_only_signal = False
        for order in permutations(labels):
            for r in range(1, h+1):
                observed = pushforward(shift, order, r)
                base = pushforward(null, order, r)
                envelope = 0
                for k in range(r+1):
                    # If neither flipped tail is pinned then exact short
                    # records cancel. At saturation a cutoff may split them.
                    b_tail = choose(a-(k-1), h-k) if k else 0
                    b_anchor = choose(a-k, h-1-k) if k == r else 0
                    # Per strict or saturated record: at most this many
                    # completions per pinned tail. With neither pinned,
                    # the two tails' allowed anchor cores are nested.
                    envelope += (2*choose(a, k-1)*b_tail**2
                                 + choose(a, k)*b_anchor**2)*P**k
                chi = Q(0)
                for v, unit in observed.items():
                    k, n_tail = len(v), int(x in v)+int(y in v)
                    if n_tail:
                        assert n_tail == 1 and abs(unit) <= choose(a-(k-1), h-k)
                    else:
                        assert k == r and abs(unit) <= choose(a-k, h-1-k)
                        anchor_only_signal = True
                    qi = base[v]-d*unit
                    assert qi >= Q(1, 2*P**k)
                    chi += (2*d*unit)**2/qi
                assert chi <= 8*d*d*envelope
                checks += 1
        assert anchor_only_signal
    return checks


def rational_rank(columns):
    """Column elimination over the rationals for small sparse matrices."""
    pivots = {}
    for column in columns:
        v = {k: Q(a) for k, a in column.items() if a}
        while v:
            row = min(v)
            if row not in pivots:
                pivots[row] = {k: a/v[row] for k, a in v.items()}
                break
            scale = v[row]
            for k, a in pivots[row].items():
                v[k] = v.get(k, 0)-scale*a
                if not v[k]:
                    del v[k]
    return len(pivots)


def check_population_design():
    inversions = 0
    checked_ranks = 0
    for h in (2, 3, 4):
        for m in range(h, 8):
            labels = tuple(range(m))
            edges = list(combinations(labels, h))
            cubes = []
            shift = Counter()
            weights = {edge: 1+j*(-1)**j for j, edge in enumerate(edges)}
            for edge in edges:
                col = Counter()
                add_cube(col, edge, (-1)**h)
                cubes.append(col)
                add_cube(shift, edge, (-1)**h*weights[edge])
            for r in range(1, h+1):
                cols = [pushforward(col, labels, r) for col in cubes]
                full_rank = rational_rank(cols)
                saturated_rank = rational_rank([{k: w for k, w in col.items() if len(k) == r}
                                                for col in cols])
                predicted = sum(min(comb(x-1, r-1), comb(x-1, h-1))
                                for x in range(h, m+1))
                assert full_rank == saturated_rank == predicted
                assert (full_rank == len(edges)) == (r == h or m <= h+r-1)
                checked_ranks += 1
                summaries = {}
                for D in subsets(labels, h-r):
                    priority = (*[a for a in labels if a not in D], *D)
                    summaries[D] = pushforward(shift, priority, r)
                for edge in edges:
                    # Exercise every possible R containing the maximum.
                    for small in combinations(edge[:-1], r-1):
                        R = (*small, edge[-1])
                        J = tuple(i for i in edge if i not in R)
                        value = sum((-1)**(h-r+len(D))*summaries[D].get(R, 0)
                                    for D in subsets(J))
                        assert value == weights[edge]
                        inversions += 1
    return checked_ranks, inversions


if __name__ == "__main__":
    print(f"{check_cube_image()} signed-cube images checked.")
    print(f"{check_physical_inversion()} exact centered marginal inversions on a prime menu.")
    print(f"{check_local_prefix()} bounded-displacement truncation identities checked.")
    print(f"{check_invisible_trades()} hidden fixed-priority trades and cost gaps checked.")
    print(f"{check_priority_chi_square()} priority/depth pairwise information bounds checked.")
    num_ranks, inversions = check_population_design()
    print(f"{num_ranks} fixed-priority ranks and {inversions} preset-priority reconstructions checked.")
