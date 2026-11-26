"""Exact finite checks for recovering centered costs from first-hit traces."""

from collections import defaultdict
from fractions import Fraction as F
from itertools import combinations, permutations


def subsets(vertices, limit):
    for size in range(limit + 1):
        yield from combinations(vertices, size)


def make_tilings(m, w):
    half = 2 * w + 1
    tilings = []
    for shift in (0, half):
        boundaries = [0]
        boundaries.extend(cut for cut in range(shift, m, 2 * half) if cut)
        boundaries.append(m)
        tilings.append(tuple(tuple(range(lo, hi))
                             for lo, hi in zip(boundaries, boundaries[1:])))
    return tilings


def scan_order(tiling, marked):
    """Each tile scans marked indices before unmarked indices."""
    order = []
    for tile in tiling:
        order.extend(i for i in tile if marked & (1 << i))
        order.extend(i for i in tile if not marked & (1 << i))
    return order


def walsh(vertices, marked):
    """Product of marks with +1 for marked and -1 for unmarked."""
    return (-1) ** sum(not marked & (1 << i) for i in vertices)


def check_case(m, w, h):
    tilings = make_tilings(m, w)
    tile_at = [{j: tile for tile in tiling for j in tile} for tiling in tilings]
    selected = []
    for j in range(m):
        near = set(range(j, min(m, j + 2 * w + 1)))
        choices = [a for a in (0, 1) if near.issubset(tile_at[a][j])]
        assert choices
        selected.append(choices[0])
    if m > 4 * w + 2:
        assert set(selected) == {0, 1}

    cells = list(subsets(range(m), h))
    weights = {cell: 2 + (sum(i + 1 for i in cell) + 3 * len(cell)) ** 2 % 19
               for cell in cells}
    word_mass = sum(weights.values())
    mark_count = 1 << m
    joint_denominator = 2 * mark_count * word_mass
    outcomes = {}
    event_checks = 0
    for a, tiling in enumerate(tilings):
        for marked in range(mark_count):
            order = scan_order(tiling, marked)
            position = {j: i for i, j in enumerate(order)}
            counts = [0] * m
            for cell, weight in weights.items():
                if not cell:
                    continue
                first = min(cell, key=position.__getitem__)
                counts[first] += weight
                j = cell[0]
                local = set(cell).intersection(tile_at[a][j])
                expected = j if all(not marked & (1 << i) for i in local) else None
                revealed = first if not marked & (1 << first) else None
                assert revealed == expected
                event_checks += 1
            outcomes[a, marked] = counts

    local_probabilities = defaultdict(F)
    minimum_probabilities = defaultdict(F)
    for cell, weight in weights.items():
        if cell:
            j = cell[0]
            local = tuple(i for i in cell if i in tile_at[selected[j]][j])
            local_probabilities[local] += F(weight, word_mass)
            minimum_probabilities[j] += F(weight, word_mass)
    q = max(minimum_probabilities.values())

    table = {}
    fields = {}
    for j, a in enumerate(selected):
        available = tuple(i for i in tile_at[a][j] if i > j)
        fields[j] = tuple((j,) + rest for rest in subsets(available, h - 1))
        for T in fields[j]:
            correlation = sum(
                outcomes[a, marked][j] * walsh(T[1:], marked)
                for marked in range(mark_count) if not marked & (1 << j)
            )
            factor = 2 * 2 ** len(T) * (-1) ** (len(T) - 1)
            table[T] = F(factor * correlation, joint_denominator)
            expected = sum(F(1, 2) ** (len(U) - len(T)) * local_probabilities[U]
                           for U in fields[j] if set(T).issubset(U))
            assert table[T] == expected
        for U in fields[j]:
            recovered = sum(F(-1, 2) ** (len(T) - len(U)) * table[T]
                            for T in fields[j] if set(U).issubset(T))
            assert recovered == local_probabilities[U]

    cost_by_prefix = {}
    for t in range(m + 1):
        fixed = frozenset(range(max(0, t - w)))
        stop = min(m, t + w)
        boundary = range(len(fixed), stop)
        reference = set(range(t))
        for extra in combinations(boundary, t - len(fixed)):
            prefix = fixed.union(extra)
            population = 0
            for cell, weight in weights.items():
                direct = int(prefix.isdisjoint(cell)) - int(reference.isdisjoint(cell))
                local_delta = 0
                if cell and cell[0] in boundary:
                    j = cell[0]
                    local = set(cell).intersection(tile_at[selected[j]][j])
                    local_delta = int(prefix.isdisjoint(local)) - int(j >= t)
                assert local_delta == direct
                population += weight * direct
            population = F(population, word_mass)

            coefficients = {}
            for j in boundary:
                for T in fields[j]:
                    coefficients[T] = sum(
                        F(-1, 2) ** (len(T) - len(rest) - 1)
                        * (int(prefix.isdisjoint((j,) + rest)) - int(j >= t))
                        for rest in subsets(T[1:], len(T) - 1)
                    )
            reconstructed = sum(f * table[T] for T, f in coefficients.items())
            assert reconstructed == population
            cost_by_prefix[prefix] = reconstructed

            # Compute both moments from the actual first-hit experiment.
            mean, second = F(0), F(0)
            for a in (0, 1):
                for marked in range(mark_count):
                    for j in boundary:
                        if selected[j] != a or marked & (1 << j):
                            continue
                        value = 2 * sum(
                            coefficients[T] * 2 ** len(T) * (-1) ** (len(T) - 1)
                            * walsh(T[1:], marked) for T in fields[j]
                        )
                        probability = F(outcomes[a, marked][j], joint_denominator)
                        mean += probability * value
                        second += probability * value * value
            assert mean == population
            squared_field_weights = sum(
                (2 ** len(T) * coeff) ** 2 for T, coeff in coefficients.items()
            )
            assert second <= 2 * q * squared_field_weights

    # Optimize the recovered prefix costs and compare with direct costs.
    dp = {frozenset(): F(0)}
    for t in range(m):
        following = {}
        for prefix, cost in dp.items():
            for j in range(max(0, t - w), min(m, t + w + 1)):
                if j not in prefix:
                    next_prefix = prefix.union((j,))
                    if next_prefix in cost_by_prefix:
                        value = cost + cost_by_prefix[prefix]
                        if next_prefix not in following or value < following[next_prefix]:
                            following[next_prefix] = value
        dp = following
    optimum = dp[frozenset(range(m))]

    def direct_cost(order):
        ranks = {j: i for i, j in enumerate(order)}
        numerator = sum(weight * (min(ranks[j] for j in cell) - cell[0])
                        for cell, weight in weights.items() if cell)
        return F(numerator, word_mass)

    direct_optimum = min(direct_cost(order) for order in permutations(range(m))
                         if all(abs(j - i) <= w for i, j in enumerate(order)))
    assert optimum == direct_optimum
    return event_checks, len(table), len(cost_by_prefix), optimum


if __name__ == "__main__":
    for m, w, h in ((8, 1, 3), (7, 2, 3), (6, 1, 2)):
        events, fields, prefixes, optimum = check_case(m, w, h)
        print(f"m={m}, W={w}, h={h}: {events} first-hit events, {fields} inverted fields, "
              f"{prefixes} prefix moment checks, exact optimum {optimum}")
