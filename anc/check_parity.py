"""Exact finite checks for the parity channel and its low-coordinate-degree moments."""

from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, prod


def masks_of_size(m, size):
    return [sum(1 << i for i in group) for group in combinations(range(m), size)]


def size(mask):
    return bin(mask).count("1")


def sign(mask):
    return (-1) ** size(mask)


def build_laws(m, h, negative, q, eps):
    edges = masks_of_size(m, h)
    cells = [s for s in range(1 << m) if size(s) <= h]
    baseline = {}
    for s in cells:
        k = size(s)
        baseline[s] = q**k * sum((-q)**j * comb(m - k, j) for j in range(h - k + 1))
    a, gamma = q**h / 2, eps / 50
    d = a * gamma
    rho = 2**h * a * len(edges)
    signed = baseline.copy()
    residual = baseline.copy()
    for e in edges:
        for s in cells:
            if s & e == s:
                residual[s] -= a
                signed[s] -= d * sign(s) * sign(e & negative)
    assert min(residual.values()) >= 0 and sum(residual.values()) == 1 - rho
    assert min(signed.values()) > 0 and sum(signed.values()) == 1

    def simulate(bias):
        result = residual.copy()
        for e in edges:
            for y in (-1, 1):
                py = (1 + y * bias * sign(e & negative)) / 2
                allowed = [s for s in cells if s & e == s and sign(s) == -y]
                assert len(allowed) == 2**(h - 1)
                for s in allowed:
                    result[s] += rho / len(edges) * py / len(allowed)
        return result

    assert simulate(gamma) == signed and simulate(F(0)) == baseline
    return edges, signed, baseline, rho, gamma, d


def check_joint_histories(law, m, h, q):
    for k in range(h):
        for coordinates in masks_of_size(m, k):
            actual = {}
            for s, mass in law.items():
                observed = s & coordinates
                actual[observed] = actual.get(observed, 0) + mass
            for observed, prob in actual.items():
                ones = size(observed)
                assert prob == q**ones * (1 - q)**(k - ones)
            assert len(actual) == 2**k


def check_costs(m, h, q, negative, edges, law, baseline, d):
    fallback = 4 / q
    cost_differences = {}
    for order in permutations(range(m)):
        by_prefix, prefix = 0, 0
        for i in order:
            by_prefix += sum(sign(e & negative) for e in edges if prefix & e == e)
            prefix |= 1 << i
        ranks = {1 << v: r for r, v in enumerate(order, 1)}
        def charge(s):
            return min((rank for v, rank in ranks.items() if v & s), default=m + fallback)

        actual = sum((law[s] - baseline[s]) * charge(s) for s in law)
        assert actual == -d * (by_prefix + fallback * sum(sign(e & negative) for e in edges))
        cost_differences[order] = actual

    # Both orders share the first h-1 tests. Their h-prefixes have opposite hidden signs.
    first = tuple(range(m))
    second = list(first)
    second[h - 1], second[h] = second[h], second[h - 1]
    gap = cost_differences[tuple(second)] - cost_differences[first]
    assert gap == 2 * d
    return gap


def check_moments(m, h, edges, rho, gamma):
    count = len(edges)
    # Distinct samples can draw the same edge. XOR of incidence masks tracks odd degrees.
    parity_counts = {0: 1}
    probabilities = []
    for length in range(1, 7):
        next_counts = {}
        for parity, multiplicity in parity_counts.items():
            for edge in edges:
                dest = parity ^ edge
                next_counts[dest] = next_counts.get(dest, 0) + multiplicity
        parity_counts = next_counts
        probabilities.append(F(parity_counts.get(0, 0), count**length))
    assert probabilities[0] == 0 and probabilities[1] == F(1, count)
    if h % 2:
        assert all(probabilities[j] == 0 for j in range(0, 6, 2))
    # Exhibit a nonzero contribution with all edges distinct as well.
    witness = ((0b000111, 0b011001, 0b101010, 0b110100) if h == 3
               else (0b001111, 0b110011, 0b111100))
    parity = 0
    for edge in witness:
        assert edge in edges
        parity ^= edge
    assert parity == 0 and len(set(witness)) == len(witness)

    # Compute likelihood inner products directly over the inactive state and 2H active ones.
    # Uniform hidden signs make the distribution of a pairwise sign product uniform.
    states = [(0, 0, 1 - rho)]
    states += [(edge, y, rho / (2 * count)) for edge in edges for y in (-1, 1)]
    inner = []
    for theta in range(1 << m):
        value = F(0)
        for edge, y, null_mass in states:
            alt_theta = null_mass * (1 + gamma * y * sign(edge & theta))
            alt_plus = null_mass * (1 + gamma * y)
            value += (alt_theta - null_mass) * (alt_plus - null_mass) / null_mass
        inner.append(value)
    direct = [sum(x**j for x in inner) / (1 << m) for j in range(1, 7)]
    from_parity = [(rho * gamma**2)**j * prob for j, prob in enumerate(probabilities, 1)]
    assert direct == from_parity
    for N in range(1, 7):
        for D in range(1, N + 1):
            assert (sum(comb(N, j) * direct[j - 1] for j in range(1, D + 1))
                    == sum(comb(N, j) * from_parity[j - 1] for j in range(1, D + 1)))

    # N=D=2: a separate explicit null-state sum checks the mixture's projected chi-squared.
    signs = {edge: [sign(edge & theta) for theta in range(1 << m)] for edge, _, _ in states}
    measured = F(0)
    for edge1, y1, mass1 in states:
        for edge2, y2, mass2 in states:
            linear = y1 * sum(signs[edge1]) + y2 * sum(signs[edge2])
            quadratic = y1 * y2 * sum(a * b for a, b in zip(signs[edge1], signs[edge2]))
            mixture_ratio_minus_one = (gamma * linear + gamma**2 * quadratic) / (1 << m)
            measured += mass1 * mass2 * mixture_ratio_minus_one**2
    assert measured == direct[1] == (rho * gamma**2)**2 / count


def check_tagged_model(n, h, q, eps):
    """Encode XOR signs in plus/minus tags; enumerate every possible midpoint."""
    m = 2 * n
    group_sets = list(combinations(range(n), h))
    cells = [s for s in range(1 << m) if size(s) <= h]
    coefficients = {}
    baseline = {}
    groups = {}
    labels = {}
    theta = tuple(1 if i % 3 == 0 else -1 for i in range(n))
    parity_sign = (-1)**(h + 1)
    d = eps * q**h / 100
    bias = d / q**h
    rho = 2**h * len(group_sets) * q**h
    for s in cells:
        k = size(s)
        baseline[s] = q**k * sum((-q)**j * comb(m - k, j) for j in range(h - k + 1))
    for group in group_sets:
        for tags in product((1, -1), repeat=h):
            e = sum(1 << (2*i + int(z == -1)) for i, z in zip(group, tags))
            groups[e] = group
            labels[e] = parity_sign * prod(tags)
            coefficients[e] = prod(theta[i] for i in group) * prod(tags)

    # Build the signed perturbation by summing cubes, including every lower cell.
    increments = dict.fromkeys(cells, 0)
    for e, weight in coefficients.items():
        s = e
        while True:
            increments[s] -= sign(s) * weight
            if s == 0:
                break
            s = (s - 1) & e
    assert all(increments[s] == parity_sign * coefficients.get(s, 0) for s in cells)
    law = {s: baseline[s] + d * increments[s] for s in cells}
    assert min(law.values()) > 0 and sum(law.values()) == 1
    assert sum(law[s] for s in coefficients) == rho
    assert all(law[s] == baseline[s] for s in cells if s not in coefficients)
    check_joint_histories(law, m, h, q)

    # Integer -> XOR reads group and tag parity. XOR -> integer draws uniform matching tags.
    for group in group_sets:
        hidden = prod(theta[i] for i in group)
        for y in (-1, 1):
            same_fiber = [s for s in coefficients if groups[s] == group and labels[s] == y]
            xor_prob = (1 + y * bias * hidden) / (2 * len(group_sets))
            assert sum(law[s] for s in same_fiber) == rho * xor_prob
            assert len(same_fiber) == 2**(h - 1)
            assert all(rho * xor_prob / len(same_fiber) == law[s] for s in same_fiber)

    full = (1 << m) - 1
    prefix_val, overlap = [], []
    for mask in range(full + 1):
        # Exact survival cost shift for a prefix divided by d; fallback has zero shift.
        signed_survival = sum(increments[s] for s in coefficients if s & mask == 0)
        value = sum(weight for e, weight in coefficients.items() if e & mask == e)
        assert signed_survival == -value
        open_tags = [int(bool(mask & (1 << (2*i)))) - int(bool(mask & (2 << (2*i))))
                     for i in range(n)]
        aligned = [a * z for a, z in zip(open_tags, theta)]
        assert value == sum(prod(aligned[i] for i in group) for group in group_sets)
        k = size(mask)
        assert value <= comb(min(k, m - k), h)
        prefix_val.append(value)
        overlap.append(sum(aligned))

    # Forward and backward dynamic programs give the best order at every fixed midpoint.
    forward, backward = [0] * (full + 1), [0] * (full + 1)
    for mask in range(1, full + 1):
        prev = [mask ^ (1 << i) for i in range(m) if mask & (1 << i)]
        forward[mask] = max(forward[s] + prefix_val[s] for s in prev)
    for mask in reversed(range(full)):
        nxt = [mask | (1 << i) for i in range(m) if not mask & (1 << i)]
        backward[mask] = prefix_val[mask] + max(backward[s] for s in nxt)
    optimum = comb(n + 1, h + 1) + comb(n, h + 1)
    assert forward[full] == backward[0] == optimum
    profile = {s: forward[s] + backward[s] for s in masks_of_size(m, n)}
    lipschitz = 2 * comb(n - 1, h - 1)
    for s, best_score in profile.items():
        midpoint_deficit = comb(n, h) - prefix_val[s]
        assert 4 * lipschitz * (optimum - best_score) >= midpoint_deficit**2
    if n == 4 and h == 3:
        brute_profile = {s: -optimum - 1 for s in profile}
        for order in permutations(1 << i for i in range(m)):
            score, mask, middle = 0, 0, 0
            for j, bit in enumerate(order):
                if j == n:
                    middle = mask
                score += prefix_val[mask]
                mask |= bit
            brute_profile[middle] = max(brute_profile[middle], score)
        assert brute_profile == profile

    if n == h:
        # A single even XOR permits a balanced, perfectly scoring midpoint.
        assert any(score == optimum and overlap[s] == 0 for s, score in profile.items())
        return
    assert n >= h + 1
    best_correlations = {overlap[s] for s, score in profile.items() if score == optimum}
    assert best_correlations == ({n} if h % 2 else {-n, n})
    signed_overlap = (lambda x: x) if h % 2 else abs
    poor_best = max(score for s, score in profile.items() if signed_overlap(overlap[s]) <= n / 2)
    assert poor_best < F(3, 4) * optimum
    print(f"Tagged n={n}, h={h}: bidirectional channels exact, F*={optimum}, "
          f"best score at midpoint overlap <= n/2 is {poor_best}.")


def tagged_order_scores(n, h, order):
    opened = [0] * n
    scores = []
    for group, tag in order:
        correct, wrong = opened.count(1), opened.count(-1)
        scores.append(sum((-1)**k * comb(wrong, k) * comb(correct, h-k)
                          for k in range(h+1)))
        opened[group] += tag
    assert opened == [0] * n
    return scores


def check_midpoint_examples(h):
    n = 8 * h
    optimum = comb(n + 1, h + 1) + comb(n, h + 1)
    slope = 2 * comb(n - 1, h - 1)
    for r in range(1, n // 4 + 1):
        selected = [(i, 1) for i in range(n - r, n)]
        opposite = [(i, -1) for i in range(n - r, n)]
        order = ([(i, 1) for i in range(n - r)] + opposite + selected
                 + [(i, -1) for i in range(n - r)])
        scores = tagged_order_scores(n, h, order)
        deficit = optimum - sum(scores)
        midpoint_deficit = comb(n, h) - scores[n]
        assert midpoint_deficit**2 <= 4 * slope * deficit
        assert 0 < deficit <= 4 * r**2 * comb(n-1, h-1)
        spread = (opposite + [(i, 1) for i in range(n-r)]
                  + [(i, -1) for i in range(n-r)] + selected)
        assert set(order[:n]) == set(spread[:n])
        scores = tagged_order_scores(n, h, spread)
        deficit = optimum - sum(scores)
        lower = 2 * r * comb(n//4, h-1)
        for j in range(n//2, 3*n//4+1):
            assert comb(j, h) - scores[j] >= lower
        assert (n//4+1) * lower <= deficit <= 2*n*2*r*comb(n-1, h-1)


def main():
    m, q, eps = 6, F(1, 257), F(1, 2)
    for h in (3, 4):
        # The first h signs are positive and the next is negative.
        negative = 1 << h
        edges, law, baseline, rho, gamma, d = build_laws(m, h, negative, q, eps)
        check_joint_histories(law, m, h, q)
        flipped = 1 << (h - 1)
        _, other, _, _, _, _ = build_laws(m, h, flipped, q, eps)
        check_joint_histories(other, m, h, q)
        gap = check_costs(m, h, q, negative, edges, law, baseline, d)
        assert sum(mass for s, mass in law.items() if s & ((1 << h) - 1) == 0) \
            == (1 - q)**h - d
        assert sum(mass for s, mass in other.items() if s & ((1 << h) - 1) == 0) \
            == (1 - q)**h + d
        check_moments(m, h, edges, rho, gamma)
        print(f"h={h}: both channels, all low-order histories, all 720 orders, "
              f"degree 1-6 moments passed; example order gap = {gap} = 2d")
    check_tagged_model(4, 3, q, eps)
    check_tagged_model(5, 4, q, eps)
    check_tagged_model(4, 4, q, eps)
    for h in (3, 4):
        check_midpoint_examples(h)
    print("Both sharp midpoint envelopes passed for all swaps at h=3,4.")


if __name__ == "__main__":
    main()
