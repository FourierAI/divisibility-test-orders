"""Exact finite checks for natural_low_rank.tex and natural_field_realization.tex.

The profile solver uses two vertices and two allowed labels per tile.
It enumerates the vertices of the resulting two-dimensional local LPs.
This is a finite regression check, with no asymptotic timing inference.
"""

from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction as F
from functools import lru_cache
from itertools import accumulate, combinations, permutations, product
from math import comb


@dataclass(frozen=True)
class Profile:
    count: F
    field: F
    vertices: tuple


def lp_vertices(rows):
    """Vertices of {x: a*x[0] + b*x[1] <= c for (a,b,c) in rows}."""
    vertices = set()
    for (a, b, c), (d, e, f) in combinations(rows, 2):
        determinant = a * e - b * d
        if determinant:
            x = F(c * e - b * f) / determinant
            y = F(a * f - c * d) / determinant
            if all(a0 * x + b0 * y <= c0 for a0, b0, c0 in rows):
                vertices.add((x, y))
    return tuple(sorted(vertices))


def source_profiles(features, grid):
    """Enumerate both guessed prefix coordinates at the one active cut."""
    unit_box = [(1, 0, 1), (0, 1, 1), (-1, 0, 0), (0, -1, 0)]
    low = sum(min(0, f) for f in features)
    high = sum(max(0, f) for f in features)
    states = []
    for count_step in range(int(2 / grid) + 1):
        count = count_step * grid
        for field_step in range(int(low / grid), int(high / grid) + 1):
            field = field_step * grid
            a, b = features
            inequalities = unit_box + [
                (1, 1, count + grid), (-1, -1, grid - count),
                (a, b, field + grid), (-a, -b, grid - field),
            ]
            vertices = lp_vertices(inequalities)
            if vertices:
                states.append(Profile(count, field, vertices))
    return states


def rank_score(scores, matrix, ranks):
    return sum(s * r for s, r in zip(scores, ranks)) + sum(
        a * max(ranks[i] - ranks[j], 0)
        for i, row in enumerate(matrix) for j, a in enumerate(row)
    )


def repair(scores, matrix, coordinates, degree):
    """Swap strong score inversions in provisional coordinates, then rank."""
    coordinates = list(coordinates)
    exchanges = 0
    while True:
        order = sorted(range(len(scores)), key=lambda i: (coordinates[i], i))
        inversion = next(
            ((i, j) for i, j in combinations(order, 2)
             if scores[j] - scores[i] > 2 * degree),
            None,
        )
        if inversion is None:
            return tuple(order.index(i) for i in range(len(order))), exchanges
        i, j = inversion
        assert coordinates[i] < coordinates[j]
        coordinates[i], coordinates[j] = coordinates[j], coordinates[i]
        exchanges += 1


def check_profiles(scores, signs, block_weights, first_labels):
    """Run profile enumeration, chain DP, LP rounding and rank repair."""
    n = len(scores)
    tile_count = n // 2
    grid = F(1, 2)
    representatives = tuple(range(0, n, 2))
    cuts = range(tile_count - 1)
    sources = [tuple(signs[2 * t:2 * t + 2]) for t in range(tile_count)]
    states = [source_profiles(f, grid) for f in sources]

    symmetric = [
        [block_weights[i // 2][j // 2] * signs[i] * signs[j] for j in range(n)]
        for i in range(n)
    ]
    matrix = [[0] * n for _ in range(n)]
    for i in range(n):
        matrix[i][i] = F(symmetric[i][i], 2)
        for j in range(i + 1, n):
            matrix[i][j] = symmetric[i][j]
    imbalance = [sum(matrix[i][j] - matrix[j][i] for j in range(n))
                 for i in range(n)]
    degree = max(sum(abs(matrix[i][j]) + abs(matrix[j][i])
                     for j in range(n) if j != i) for i in range(n))
    phi = [0, *accumulate(scores[:-1])]
    baseline = sum(i * score for i, score in enumerate(scores))

    def unary(i, coordinate):
        return scores[i] * (coordinate - i) - phi[coordinate] + phi[i]

    def provisional_coordinate(i, label):
        start = representatives[label]
        return min(max(i, start), start + 1)

    def bucket_cost(labels):
        coordinates = [representatives[a] for a in labels]
        unary_cost = sum(unary(i, provisional_coordinate(i, a))
                         for i, a in enumerate(labels))
        hinge = rank_score([0] * n, matrix, coordinates)
        symmetrized = F(1, 2) * sum(d * u for d, u in zip(imbalance, coordinates))
        symmetrized += F(1, 4) * sum(
            symmetric[i][j] * abs(coordinates[i] - coordinates[j])
            for i in range(n) for j in range(n)
        )
        assert symmetrized == hinge
        return unary_cost + hinge

    neighbors = [
        tuple(t for t, weight in enumerate(weights) if weight or u == t)
        for u, weights in enumerate(block_weights)
    ]

    @lru_cache(None)
    def local_solution(receiver, source_states):
        nearby = dict(zip(neighbors[receiver], source_states))
        state = nearby[receiver]
        lower_label = first_labels[receiver]
        costs = []
        for i in (2 * receiver, 2 * receiver + 1):
            row = []
            for label in (lower_label, lower_label + 1):
                u = representatives[label]
                cost = unary(i, provisional_coordinate(i, label))
                cost += F(imbalance[i] * u, 2)
                for source, guess in nearby.items():
                    left = representatives[first_labels[source]]
                    right = representatives[first_labels[source] + 1]
                    field = guess.field * abs(u - left)
                    field += (sum(sources[source]) - guess.field) * abs(u - right)
                    cost += F(block_weights[receiver][source] * signs[i], 4) * field
                row.append(cost)
            costs.append(row)
        value, point = min(
            (sum(x * lo + (1 - x) * hi for x, (lo, hi) in zip(p, costs)), p)
            for p in state.vertices
        )
        labels = []
        for x, (lo, hi) in zip(point, costs):
            use_low = x == 1 or (x > 0 and lo <= hi)
            labels.append(lower_label if use_low else lower_label + 1)
        rounded = sum(row[label - lower_label] for row, label in zip(costs, labels))
        assert rounded <= value
        return value, rounded, tuple(labels), sum(0 < x < 1 for x in point)

    # Each factor becomes evaluable when its rightmost source is known.
    capacity_scopes = []
    for boundary in cuts:
        scope = [t for t, label in enumerate(first_labels) if label == boundary]
        assert scope
        capacity_scopes.append((boundary, scope))

    def capacity_ok(boundary, scope, path):
        completed = 2 * sum(label < boundary for label in first_labels)
        estimate = completed + sum(path[t].count for t in scope)
        return abs(estimate - 2 * (boundary + 1)) <= grid

    memory = max(d[-1] - d[0] for d in neighbors + [s for _, s in capacity_scopes])
    dp = {(): (0, ())}
    for tile, options in enumerate(states):
        updated = {}
        for value, previous in dp.values():
            for guess in options:
                path = previous + (guess,)
                if any(
                    not capacity_ok(c, scope, path)
                    for c, scope in capacity_scopes if scope[-1] == tile
                ):
                    continue
                cost = value + sum(
                    local_solution(u, tuple(path[t] for t in near))[0]
                    for u, near in enumerate(neighbors) if near[-1] == tile
                )
                key = path[-memory:] if memory else ()
                if key not in updated or cost < updated[key][0]:
                    updated[key] = cost, path
        dp = updated
    value, path = min(dp.values(), key=lambda result: result[0])
    exhaustive_value = min(
        sum(local_solution(u, tuple(p[t] for t in near))[0]
            for u, near in enumerate(neighbors))
        for p in product(*states)
        if all(capacity_ok(c, scope, p) for c, scope in capacity_scopes)
    )
    assert value == exhaustive_value
    solutions = [local_solution(u, tuple(path[t] for t in near))
                 for u, near in enumerate(neighbors)]
    labels = sum((result[2] for result in solutions), ())
    predicted = sum(result[1] for result in solutions)
    split = sum(result[3] for result in solutions)
    assert value == sum(result[0] for result in solutions) and predicted <= value

    # Exact and predicted fields have the same final mass. For a single
    # active cut, their distance-potential error is bounded by its prefix
    # discrepancy times the distance between consecutive representatives.
    field_error_bound = 0
    for source, (f, profile) in enumerate(zip(sources, path)):
        low = first_labels[source]
        actual = sum(f[j] for j in range(2) if labels[2 * source + j] == low)
        difference = abs(actual - profile.field)
        field_error_bound += F(1, 4) * 2 * difference * sum(
            abs(block_weights[u][source] * signs[i])
            for u in range(tile_count) for i in (2 * u, 2 * u + 1)
        )
    assert abs(bucket_cost(labels) - predicted) <= field_error_bound

    coordinates = [provisional_coordinate(i, a) for i, a in enumerate(labels)]
    ranks, exchanges = repair(scores, matrix, coordinates, degree)
    discrepancy = max(abs(sum(a <= c for a in labels) - 2 * (c + 1)) for c in cuts)
    actual_cost = rank_score(scores, matrix, ranks)
    assert actual_cost <= baseline + bucket_cost(labels) + degree * n * (8 + 3 * discrepancy)
    assert all(ranks[i] < ranks[j] for i, j in combinations(range(n), 2)
               if scores[i] - scores[j] > 2 * degree)

    optimum, comparator = min(
        (rank_score(scores, matrix, rank), rank)
        for rank in permutations(range(n))
        if all(first_labels[i // 2] <= r // 2 <= first_labels[i // 2] + 1
               for i, r in enumerate(rank))
    )
    comparator_labels = tuple(r // 2 for r in comparator)
    assert value <= bucket_cost(comparator_labels)
    assert bucket_cost(comparator_labels) <= optimum - baseline + 2 * degree * n
    assert actual_cost - optimum <= (
        field_error_bound + degree * n * (10 + 3 * discrepancy)
    )
    return optimum, actual_cost, split, discrepancy, exchanges


def check_score_ties():
    """Verify targeted cross-pair entries and scalar score ties after cubes."""
    n, a, u = 16, 10, 2
    anchors = tuple(range(a))
    receivers = tuple(range(a, a + u))
    sources = tuple(range(a + u, a + 2 * u))
    active = receivers + sources
    primes = [101, 103, 107, 109, 113, 127, 131, 137,
              139, 149, 157, 163, 167, 173, 179, 181]
    q = [F(1, p) for p in primes]
    target_pairs = {(i, j): F((-1)**(i + j), 69_000_000)
                    for i in receivers for j in sources}
    weight_count = 0
    for h in (2, 3, 4):
        scores = [F(0)] * n
        scores[-1] = q[-1]
        for i in reversed(range(n - 1)):
            e = [F(1)] + [F(0)] * (h - 1)
            for rate in q[:i]:
                for degree in reversed(range(1, h)):
                    e[degree] += rate * e[degree - 1]
            scores[i] = scores[i + 1] + (q[i] - q[i + 1]) * sum(
                (-1)**degree * value for degree, value in enumerate(e)
            )
        tied_score = (scores[active[0]] + scores[active[-1]]) / 2
        weights = {}
        for (i, j), value in target_pairs.items():
            for completion in combinations(anchors, h - 2):
                weights[completion + (i, j)] = -value / comb(a, h - 2)
        for i in active:
            shift = sum(target_pairs.get((j, i), 0) for j in range(i))
            residual = tied_score - scores[i] - shift
            for completion in combinations(anchors, h - 1):
                weights[completion + (i,)] = -residual / comb(a, h - 1)
        cells = defaultdict(F)
        for edge, weight in weights.items():
            for k in range(h + 1):
                for cell in combinations(edge, k):
                    cells[cell] += (-1)**k * weight
        lower_moments = defaultdict(F)
        pair_coefficients = defaultdict(F)
        scalar_shifts = defaultdict(F)
        for cell, mass in cells.items():
            for k in range(min(h, len(cell) + 1)):
                for subset in combinations(cell, k):
                    lower_moments[subset] += mass
            if len(cell) == h:
                pair_coefficients[cell[-2:]] += (-1)**(h + 1) * mass
                scalar_shifts[cell[-1]] += (-1)**(h + 1) * mass
        assert not any(lower_moments.values())
        assert all(pair_coefficients[pair] == value for pair, value in target_pairs.items())
        assert all(scores[i] + scalar_shifts[i] ==
                   (tied_score if i in active else scores[i]) for i in range(n))
        assert all(not value or pair in target_pairs or pair[0] in anchors
                   for pair, value in pair_coefficients.items())
        weight_count += len(weights)
    return weight_count


def check_clone_rows():
    """Verify that a sparse lifted graph has the advertised row mass."""
    edges = [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)]
    n, g, h, a = 5, 3, 3, 4
    weight = F(1, 107)
    lifted = {}
    for i, j in edges:
        for left, right in product(range(g), repeat=2):
            pair = (a + g * i + left, a + g * j + right)
            for anchors in combinations(range(a), h - 2):
                lifted[anchors + pair] = weight
    assert len(lifted) == len(edges) * g * g * comb(a, h - 2)
    pairs = defaultdict(F)
    for edge, value in lifted.items():
        pairs[edge[-2:]] += value
    assert len(pairs) == len(edges) * g * g
    source_degrees = [sum(i in edge for edge in edges) for i in range(n)]
    coefficient = weight * comb(a, h - 2)
    for clone in range(a, a + n * g):
        mass = sum(abs(value) for pair, value in pairs.items() if clone in pair)
        assert mass == source_degrees[(clone - a) // g] * g * coefficient
        assert mass <= max(source_degrees) * g * coefficient
    return len(pairs), len(lifted)


if __name__ == "__main__":
    cases = [
        ((10, 7, 3, 0), (1, -1, 1, -1), ((1, -2), (-2, 1)), (0, 0)),
        ((12, 9, 7, 4, 2, 0), (1, -1, -1, 1, 1, -1),
         ((2, -3, 0), (-3, 1, 2), (0, 2, -1)), (0, 1, 1)),
    ]
    splits = 0
    for case in cases:
        optimum, cost, fractional, discrepancy, exchanges = check_profiles(*case)
        splits += fractional
        print(f"{len(case[0])} vertices: exhaustive eligible optimum {optimum}, profile output "
              f"{cost}, split rows {fractional}, cumulative discrepancy {discrepancy}, "
              f"{exchanges} repair exchanges")
    assert splits > 0
    print(f"{check_score_ties()} cube weights checked across h=2,3,4")
    pairs, lifted = check_clone_rows()
    print(f"{pairs} cloned pairs and {lifted} lifted edges checked against degree-row bounds")
