"""Finite exact checks for the marginal regret and pair-order identities."""

from collections import Counter
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations
from math import comb


def check_two_cliques():
    cases = 0
    for size in range(2, 7):
        m = 2 * size
        for h in range(2, size + 1):
            known = comb(size + 1, h + 1)
            predicted = Fraction(known) - Fraction(comb(size, h), 2)
            best = None
            for left_positions in combinations(range(m), size):
                chosen = set(left_positions)
                left = right = size
                total = 0
                for index in range(m):
                    total += comb(left, h) + comb(right, h)
                    if index in chosen:
                        left -= 1
                    else:
                        right -= 1
                regret = Fraction(total, 2) - known
                best = regret if best is None else min(best, regret)
            assert best == predicted
            cases += 1
    return cases


def check_pair_cost_and_decoder():
    m = 7
    # A mix of positive and negative offsets from a common pair mass.
    weights = {(i, j): (13 * i + 7 * j + i * j) % 17 - 8
               for i, j in combinations(range(m), 2)}
    q = Fraction(1, 101)
    scale = q * q / 100
    law = {pair: q * q + scale * weight for pair, weight in weights.items()}
    for i in range(m):
        law[i,] = q - sum(mass for hit, mass in law.items()
                          if len(hit) == 2 and i in hit)
    law[()] = 1 - sum(law.values())
    assert min(law.values()) > 0
    reference_cost = sum(1 - j * q + comb(j, 2) * q * q for j in range(m))
    prefix_cost, prefix_weight = {}, {}
    for width in range(m + 1):
        for prefix in combinations(range(m), width):
            members = frozenset(prefix)
            prefix_cost[members] = sum(mass for hit, mass in law.items()
                                       if members.isdisjoint(hit))
            prefix_weight[members] = sum(weights[pair] for pair in combinations(prefix, 2))
    hidden = {0, 1, 2, 3}
    clique_edges = list(combinations(hidden, 2))
    optimal_cover = comb(len(hidden) + 1, 3)
    for order in permutations(range(m)):
        prefixes = [frozenset(order[:j]) for j in range(m)]
        direct = sum(prefix_cost[prefix] for prefix in prefixes)
        score = sum(prefix_weight[prefix] for prefix in prefixes)
        assert direct == reference_cost + scale * score
        # The same order is now viewed as a reverse order for a clique.
        ranks = {item: index for index, item in enumerate(order, 1)}
        cover = sum(min(ranks[i], ranks[j]) for i, j in clique_edges)
        missed = len(hidden.difference(order[:len(hidden)]))
        assert cover - optimal_cover >= comb(missed + 1, 3)


def check_rectangular_type_dp():
    m = 7
    rectangles = [(3, {0, 1, 2, 3}, {2, 3, 4, 5}),
                  (-7, {0, 1, 6}, {0, 1, 6}),
                  (2, {4, 5}, {2, 3, 4, 5, 6})]
    membership = [tuple((int(i in rows), int(i in cols))
                        for _, rows, cols in rectangles) for i in range(m)]
    sizes = Counter(membership)
    types = tuple(sizes)
    full = tuple(sizes[t] for t in types)
    matrix = [[sum(value for value, rows, cols in rectangles if i in rows and j in cols)
               for j in range(m)] for i in range(m)]

    @lru_cache(None)
    def solve(counts):
        if counts == full:
            return 0
        total = 0
        for index, (value, _, _) in enumerate(rectangles):
            row = sum(count * t[index][0] for count, t in zip(counts, types))
            col = sum(count * t[index][1] for count, t in zip(counts, types))
            total += value * row * col
        next_scores = []
        for index, (count, limit) in enumerate(zip(counts, full)):
            if count < limit:
                nxt = list(counts)
                nxt[index] += 1
                next_scores.append(solve(tuple(nxt)))
        return total + min(next_scores)

    expected = min(sum(sum(matrix[i][j] for i in order[:k] for j in order[:k])
                       for k in range(m)) for order in permutations(range(m)))
    assert solve((0,) * len(types)) == expected
    return len(types), solve.cache_info().currsize


def check_planted_channel():
    m, k = 8, 3
    q = Fraction(1, 101)
    d = q * q / 200
    reserved = q * q / 2
    baseline = [1 - m*q + comb(m, 2)*q*q, q - (m-1)*q*q, q*q]
    cells = [frozenset(s) for j in range(3) for s in combinations(range(m), j)]
    pairs = [s for s in cells if len(s) == 2]
    sets = [frozenset(s) for s in combinations(range(m), k) if 0 in s]
    laws = {}
    for group in sets:
        mass = {}
        for s in cells:
            size = len(s)
            residual = baseline[size] - reserved*comb(m-size, 2-size)
            assert residual >= 0
            received = [reserved + (d*(-1)**size if e <= group else 0)
                        for e in pairs if s <= e]
            mass[s] = residual + sum(received)
            assert mass[s] == baseline[size] + d*(-1)**size*sum(s <= e <= group for e in pairs)
        assert sum(mass.values()) == 1
        assert all(sum(p for hit, p in mass.items() if i in hit) == q for i in range(m))
        laws[group] = mass
    first = sets[0]
    for other in sets:
        overlap = len(first & other)
        explicit = sum(laws[first][s] * laws[other][s] / baseline[len(s)] for s in cells)
        predicted = 1 + d*d*(comb(overlap, 2)/baseline[2]
                             + (k-1)**2 * overlap/baseline[1]
                             + comb(k, 2)**2/baseline[0])
        assert explicit == predicted
    for repeats in range(13):
        fair = Fraction(1, 4)**repeats
        bit_zero_total = 0
        for positive in range(repeats + 1):
            planted = fair * (1+d/reserved)**positive * (1-d/reserved)**(repeats-positive)
            bit_zero = 2*fair - planted
            assert bit_zero >= 0 and (bit_zero + planted)/2 == fair
            bit_zero_total += bit_zero * comb(repeats, positive) * 2**repeats
        assert bit_zero_total == 1


def check_cutoff_choice():
    for m in range(3, 9):
        q = Fraction(1, 10000*m)
        d = q*q/200
        fallback = 1/q
        prefix = list(range(m))
        for sign in (-1, 1):
            p2 = q*q + sign*d
            pair = {group: p2 for group in combinations(prefix, 2)}
            singleton = {(i,): q-(m-1)*p2 for i in prefix}
            law = {**pair, **singleton, (): 1-m*q+comb(m, 2)*p2}
            survival = [sum(mass for hit, mass in law.items() if all(v >= t for v in hit))
                        for t in range(m+1)]
            costs = [sum(survival[:t]) + fallback*survival[t] for t in range(m+1)]
            predictions = [fallback + q*q*comb(t, 3)
                           + sign*d*(comb(t, 3)+fallback*comb(t, 2)) for t in range(m+1)]
            assert sum(law.values()) == 1 and costs == predictions
            optima = [t for t in range(m+1) if costs[t] == min(costs)]
            assert optima == ([m] if sign == -1 else [0, 1])


if __name__ == "__main__":
    print("Exact two-clique minimax values:", check_two_cliques(), "families passed")
    check_pair_cost_and_decoder()
    print("Pair objective and clique decoding inequality: all 5040 orders passed")
    types, states = check_rectangular_type_dp()
    print(f"Rectangle DP: {types} types, {states} states, matched all 5040 orders")
    check_planted_channel()
    print("Planted word-cell mixture, overlap likelihoods, and 0 to 12 repeated marks passed")
    check_cutoff_choice()
    print("Optional cutoff: both laws' costs and true optima passed for six menu sizes")
