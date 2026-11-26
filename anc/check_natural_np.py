"""Exact physical-cell check of the graph encoding in natural_np.tex."""

from fractions import Fraction
from itertools import combinations, permutations, product
from math import comb, prod

from check_natural_window import (
    check_admissible, expected_cost, first_primes, is_prime,
    physical_cells, ranks, reference_cells, subsets, survival,
)


def check():
    h, P, b = 2, 100_000, 192
    epsilon = Fraction(1, 2)
    anchor_primes = first_primes(P, b)
    vertex_primes = [163481, 163483, 163487]
    assert all(is_prime(p) for p in vertex_primes)
    primes = anchor_primes + vertex_primes
    anchors = tuple(range(b))
    vertices = tuple(range(b, b + len(vertex_primes)))
    graph = ((vertices[0], vertices[1]), (vertices[1], vertices[2]))
    # The finite stress instance has a larger cube budget so that three
    # actual distinct primes fit in one nontrivial bin with only 192 anchors.
    d = Fraction(1, 6 * P**2)
    g = P**2 * d * comb(b, h - 1) / 4
    assert vertex_primes[-1] - vertex_primes[0] <= g

    uniform = physical_cells(primes, h, P, epsilon)
    natural, reference = reference_cells(primes, h)
    q = [Fraction(1, p) for p in primes]
    representative = q[vertices[0]]

    def k_anchor(degree):
        return sum((-1) ** len(J) * prod(q[i] for i in J)
                   for J in subsets(anchors, degree))

    def add_cube(law, edge, coeff):
        for cell in subsets(tuple(sorted(edge))):
            law[cell] += (-1) ** len(cell) * coeff

    tied = reference.copy()
    for use in range(1, h + 1):
        for tails in combinations(vertices, use):
            coeff = ((-1) ** use * (representative**use - prod(q[i] for i in tails))
                     * k_anchor(h - use) / comb(b, h - use))
            assert abs(coeff) <= d / 4
            for completion in combinations(anchors, h - use):
                add_cube(tied, (*tails, *completion), coeff)
    check_admissible(tied, uniform, natural, h, epsilon)

    # Check the deterministic conditional tie against all vertex subsets.
    for tails in subsets(vertices):
        expected = sum(comb(len(tails), t) * (-representative)**t * k_anchor(h - t)
                       for t in range(min(h, len(tails)) + 1))
        assert survival(tied, (*anchors, *tails)) == expected

    law = tied.copy()
    for edge in graph:
        for completion in combinations(anchors, h - 2):
            add_cube(law, (*edge, *completion), d / 2)
    check_admissible(law, uniform, natural, h, epsilon)
    delta = (d / 2) * comb(b, h - 2)
    case_count = 0
    for anchor_order in (anchors, anchors[::-1]):
        offsets = set()
        order_costs = []
        for tail_order in permutations(vertices):
            reverse_rank = {i: j for j, i in enumerate(reversed(tail_order), 1)}
            graph_cost = sum(min(reverse_rank[i], reverse_rank[j]) for i, j in graph)
            cost = expected_cost(ranks((*anchor_order, *tail_order)), law, 4 * P)
            offsets.add(cost - delta * graph_cost)
            order_costs.append((graph_cost, cost))
            case_count += 1
        assert len(offsets) == 1
        opt = min(cost for _, cost in order_costs)
        assert all(cost == opt or cost - opt >= delta for _, cost in order_costs)
    early_vertex = (vertices[0], *anchors, *vertices[1:])
    anchor_first = (*anchors, *vertices)
    assert expected_cost(ranks(early_vertex), law, 4 * P) > expected_cost(
        ranks(anchor_first), law, 4 * P
    )
    print(f"actual primes {vertex_primes}: conditional ties, {case_count} exact "
          "graph-order cost identities, and a strict anchor exchange OK")


def graph_cost(order, edges):
    rank = ranks(order)
    return sum(min(rank[i], rank[j]) for i, j in edges)


def order_by_positions(positions):
    return sorted(range(len(positions)), key=positions.__getitem__)


def clone_options(clone_order, n, g):
    rank = ranks(clone_order)
    return [tuple(rank[i * g + j] for j in range(g)) for i in range(n)]


def clone_cost(options, edges):
    return sum(min(left, right) for i, j in edges
               for left in options[i] for right in options[j])


def conditional_cost(options, edges):
    total = Fraction(0)
    for i, j in edges:
        edge_cost = Fraction(0)
        for left, right in product(options[i], options[j]):
            first_position = min(left, right)
            edge_cost += 1 + sum(
                Fraction(sum(position < first_position for position in choices), len(choices))
                for other, choices in enumerate(options) if other not in (i, j)
            )
        total += edge_cost / (len(options[i]) * len(options[j]))
    return total


def decode_by_conditional_expectation(options, edges):
    options = options.copy()
    for i, choices in enumerate(options):
        def cost_with(position):
            options[i] = (position,)
            return conditional_cost(options, edges)

        options[i] = (min(choices, key=cost_with),)
    return order_by_positions([choices[0] for choices in options])


def check_clone_blowup():
    checked = 0
    near_optimal = 0
    cases = (
        (3, 2, ((0, 1), (1, 2))),
        (3, 2, ((0, 1), (0, 2), (1, 2))),
        (2, 3, ((0, 1),)),
    )
    for n, g, edges in cases:
        shift = len(edges) * g**2 * (g - 1) // 2
        optimum = min(graph_cost(order, edges) for order in permutations(range(n)))
        expected_clone_optimum = g**3 * optimum - shift
        observed_clone_optimum = None
        for clone_order in permutations(range(n * g)):
            options = clone_options(clone_order, n, g)
            cost = clone_cost(options, edges)
            observed_clone_optimum = cost if observed_clone_optimum is None else min(
                cost, observed_clone_optimum
            )
            expected = Fraction(sum(graph_cost(order_by_positions(reps), edges)
                                    for reps in product(*options)), g**n)
            assert conditional_cost(options, edges) == expected
            assert expected <= Fraction(cost + shift, g**3)
            decoded = decode_by_conditional_expectation(options, edges)
            decoded_cost = graph_cost(decoded, edges)
            assert decoded_cost <= expected
            if cost - expected_clone_optimum < g**3:
                assert decoded_cost == optimum
                near_optimal += 1
            checked += 1
        assert observed_clone_optimum == expected_clone_optimum
        for order in permutations(range(n)):
            block_order = [i * g + j for i in order for j in range(g)]
            cost = clone_cost(clone_options(block_order, n, g), edges)
            assert cost == g**3 * graph_cost(order, edges) - shift
    print(f"clone blowup: {checked} exhaustive orders, {near_optimal} exact decodings "
          "below the additive gap, and all block identities OK")


if __name__ == "__main__":
    check()
    check_clone_blowup()
