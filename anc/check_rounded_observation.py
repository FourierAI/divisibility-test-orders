"""Exact checks for rounded moments, hidden far witnesses, and thinning.

Physical cell counts come from congruences in the prescribed odd-word
interval. The small menus test the probability and cost identities; prime
density and large-menu statistical rates are asymptotic claims.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb, prod

from check_natural_observation import add_cube, observed, project
from check_natural_window import (
    containment_of, expected_cost, first_primes, is_prime, physical_cells,
    ranks, reference_cells, subsets,
)


def interval_length(P, h, epsilon):
    needed = Q(1000*(2*P)**h, epsilon)
    return 1 << ((-(-needed.numerator//needed.denominator))-1).bit_length()


def check_law(law, uniform, natural, h, L, epsilon):
    assert sum(law.values()) == 1
    assert all(0 < (1-epsilon)*uniform[c] <= value <= (1+epsilon)*uniform[c]
               for c, value in law.items())
    moments = containment_of(law)
    assert all(abs(moments[c]-prob) <= Q(1, L)
               for c, prob in natural.items() if len(c) < h)
    return moments


def check_degree_cubes():
    h, P, epsilon = 3, 1_000_000, Q(1, 2)
    primes = first_primes(P, 3)+first_primes(8*P//5, 4)
    anchors, tails = (0, 1, 2), (3, 4, 5, 6)
    uniform = physical_cells(primes, h, P, epsilon)
    natural, reference = reference_cells(primes, h)
    L = interval_length(P, h, epsilon)
    delta = Q(1, 4*L)
    checked = 0
    for degree in range(1, h+1):
        for bits in product((-1, 1), repeat=2):
            tags = dict(zip(tails, (bits[0], -bits[0], bits[1], -bits[1])))
            law = reference.copy()
            for tail in tails:
                for core in combinations(anchors, degree-1):
                    add_cube(law, (*core, tail), delta*tags[tail])
            moments = check_law(law, uniform, natural, h, L, epsilon)
            for c in natural:
                target = 0
                if len(c) == degree and c[-1] in tails and set(c[:-1]) <= set(anchors):
                    target = (-1)**degree*delta*tags[c[-1]]
                assert moments[c]-natural[c] == target
            shift = {c: law[c]-reference[c] for c in law if law[c] != reference[c]}
            for order in permutations(tails):
                r = ranks((*anchors, *order))
                true = expected_cost(r, shift, 4*P)
                predicted = -delta*comb(len(anchors), degree-1)*sum(tags[i]*r[i] for i in tails)
                assert true == predicted
                checked += 1
    return checked


def check_witnesses(h, P, primes, anchors, tails, witnesses, tied):
    epsilon = Q(1, 2)
    L = interval_length(P, h, epsilon)
    uniform = physical_cells(primes, h, P, epsilon)
    natural, null = reference_cells(primes, h)
    if tied:
        # The two-anchor and one-anchor terms implement tail exchangeability
        # before the later witnesses. Exact density checks below use the real
        # menu, including the witnesses. None of the tied terms touch them.
        assert h == 2
        q = [Q(1, prime) for prime in primes]
        for v in (1, 2):
            for group in combinations(tails, v):
                factor = 1-sum(q[i] for i in anchors) if v == 1 else 1
                coefficient = ((-1)**v*(q[tails[1]]**v-prod(q[i] for i in group))
                               * factor/comb(len(anchors), h-v))
                for core in combinations(anchors, h-v):
                    add_cube(null, (*core, *group), coefficient)
    check_law(null, uniform, natural, h, L, epsilon)
    # Absolute tie values need only the post-anchor cells and the rank-varying
    # term. All other cells have the same cost across these permutations.
    tail_rows = {c: v for c, v in null.items() if c and c[0] in tails}
    checked, ht_count = 0, 0
    for ell in range(h):
        k = ell+1
        number = comb(len(witnesses), ell)
        delta = Q(1, 4*L*number)
        t = delta*P**k
        records = project(null, ell)
        for bits in product((-1, 1), repeat=len(tails)//2):
            tags = dict(zip(tails, (z for bit in bits for z in (bit, -bit))))
            shift = {(i, *group): delta*z for i, z in tags.items()
                     for group in combinations(witnesses, ell)}
            law = {c: v+shift.get(c, 0) for c, v in null.items()}
            assert project(law, ell) == records
            assert project(law, ell+1) != project(null, ell+1)
            assert all(abs(shift[c]/null[c]) <= 2**(k+1)*t for c in shift)
            if bits == (1,)*(len(tails)//2):
                moments = check_law(law, uniform, natural, h, L, epsilon)
                null_moments = containment_of(null)
                for c in natural:
                    affected = [i for i in c if i in tails]
                    rest = [i for i in c if i in witnesses]
                    target = 0
                    if len(affected) == 1 and len(c) == len(rest)+1 and len(rest) <= ell:
                        target = delta*tags[affected[0]]*comb(len(witnesses)-len(rest), ell-len(rest))
                    assert moments[c]-null_moments[c] == target
            values, base_values = [], []
            for order in permutations(tails):
                r = ranks((*anchors, *order, *witnesses))
                raw = expected_cost(r, shift, 4*P)
                assert raw == delta*number*sum(tags[i]*r[i] for i in tails)
                values.append(raw)
                if tied:
                    base_values.append(expected_cost(r, tail_rows, 4*P))
                checked += 1
            assert min(values) == -(len(tails)//2)**2*delta*number == -max(values)
            assert not tied or len(set(base_values)) == 1
        # Use a genuinely nonuniform hit law. Test the conditional moments
        # of the transmitted score, analytically integrating the thinning coin.
        if not tied:
            theta = Q(len(primes), P)**ell
            small = sum(v for c, v in law.items() if 0 < len(c) <= ell)
            high = sum(v for c, v in law.items() if len(c) > ell)
            p1 = Q(len(primes), P)
            assert small <= 2*p1 and high <= 2*p1**k
            assert theta*high <= 2*p1**(2*k-1)
            # Only small hits cost no messages. For larger hits the score
            # is zero on silence and multiplied by 1/theta when disclosed.
            for order in permutations(tails):
                r = ranks((*anchors, *order, *witnesses))
                width = max(abs(i+1-pos) for i, pos in enumerate(r))
                variance_upper, expectation = 0, 0
                for c, mass in law.items():
                    gain = min((r[i] for i in c), default=0) - (c[0]+1 if c else 0)
                    assert abs(gain) <= width
                    if len(c) <= ell:
                        assert observed(c, ell)[1] == c
                        expectation += mass*gain
                        variance_upper += mass*gain**2
                    else:
                        expectation += mass*theta*(gain/theta)
                        variance_upper += mass*theta*(gain/theta)**2
                assert expectation == expected_cost(r, law, 4*P)-expected_cost(
                    list(range(1, len(primes)+1)), law, 4*P)
                assert variance_upper <= width**2*(small+high/theta) <= 4*width**2*p1
                ht_count += 1
    return checked, ht_count


def check_proxies():
    """Exhaust all words and linear extensions of a small overlapping-gap poset."""
    primes, gap = (31, 37, 41, 53, 59, 61, 79), 12
    n = len(primes)
    labels = tuple(range(n))
    forced = [(i, j) for i, j in combinations(labels, 2) if primes[j]-primes[i] > gap]
    width = max(sum(p <= q <= p+gap for q in primes) for p in primes)
    counter = Counter()
    for order in permutations(labels):
        r = ranks(order)
        if any(r[i] > r[j] for i, j in forced):
            continue
        # Store each subset's centered containment indicator at every prefix,
        # followed by its sum, the centered maximum-rank statistic.
        vectors = {}
        for e in subsets(labels, 4):
            if e:
                actual = max(r[i] for i in e)
                natural = e[-1]+1
                values = tuple(int(actual <= k)-int(natural <= k) for k in range(n+1))
                assert sum(values) == natural-actual
            else:
                values = (0,)*(n+1)
            vectors[e] = (*values, sum(values))
        zero = vectors[()]
        def total(edges):
            out = list(zero)
            for e, count in edges:
                for c, value in enumerate(vectors[e]):
                    out[c] += value*count
            return tuple(out)
        for h in (3, 4):
            for ell in range(h):
                for j in range(1, h+1):
                    cut = max(0, j+ell-h)
                    for word in subsets(labels, h):
                        if len(word) < j:
                            continue
                        _, kept = observed(word, ell)
                        d = len(word)-len(kept)
                        edges = list(combinations(word, j))
                        full = total((e, 1) for e in edges)
                        # Only public retained indices and the hidden count
                        # occur in either proxy computation on the right.
                        weights = [(v, comb(d, j-len(v))) for v in subsets(kept, j)
                                   if 0 <= j-len(v) <= d]
                        assert sum(c for _, c in weights) == comb(len(word), j)
                        if cut:
                            assert all(len(v) >= cut for v, _ in weights)
                        cheap = total((v[-cut:], c) for v, c in weights) if cut else zero
                        assert cheap == (total((e[-cut:], 1) for e in edges) if cut else zero)
                        if cut:
                            for e in edges:
                                if vectors[e] != vectors[e[-cut:]]:
                                    assert primes[e[-1]]-primes[e[-cut-1]] <= gap
                        fine = total(weights) if d < j else zero
                        gate = d >= j or (d > 0 and
                            primes[kept[j-d-1]]-primes[word[d-1]] <= gap)
                        if not gate:
                            assert fine == full
                            counter['outside gate'] += 1
                        for k in range(n+1):
                            if fine[k] != full[k]:
                                assert gate and any(k-width < v+1 <= k+width for v in word)
                                if 0 < d < j:
                                    # An overtaken retained hit and the
                                    # greatest unseen hit differ by at most one
                                    # local prime window in numerical rank.
                                    assert abs(word[d-1]+1-k) <= 2*width
                                counter['active prefixes'] += 1
                        counter['words/orders'] += 1
    assert counter['outside gate'] and counter['active prefixes']
    return counter


def check_padded(j, ell, h, g=2, physical=False):
    b = min(ell, h-j)
    s = max(0, j+ell-h)+1
    assert s+b == ell+1 and j+b == min(h, j+ell) and s <= j
    anchors = tuple(range(j-s+2))
    groups = [tuple(range(len(anchors)+2*g*k, len(anchors)+2*g*(k+1))) for k in range(s)]
    witnesses = tuple(range(groups[-1][-1]+1, groups[-1][-1]+b+3))
    local = tuple(i for group in groups for i in group)
    multiplier = comb(len(anchors), j-s)*comb(len(witnesses), b)
    if physical:
        P, epsilon = 1_000_000, Q(1, 2)
        primes = (first_primes(P, len(anchors))+first_primes(8*P//5, len(local))
                  +first_primes(19*P//10, len(witnesses)))
        natural, null = reference_cells(primes, h)
        uniform = physical_cells(primes, h, P, epsilon)
        L = interval_length(P, h, epsilon)
        delta = Q(1, 4*L*comb(len(witnesses), b))
    checks = 0
    for bits in product((-1, 1), repeat=g):
        tags = {v: (bits[a//2]*(-1)**(a%2) if k == 0 else (1 if a < g else -1))
                for k, group in enumerate(groups) for a, v in enumerate(group)}
        shift, target = Counter(), Counter()
        for chosen in product(*groups):
            sign = prod(tags[v] for v in chosen)
            for core in combinations(anchors, j-s):
                edge = (*core, *chosen)
                for far in combinations(witnesses, b):
                    for low in subsets(edge):
                        shift[(*low, *far)] += (-1)**len(low)*sign
                for seen_far in subsets(witnesses, b):
                    target[(*edge, *seen_far)] += ((-1)**j*sign
                        *comb(len(witnesses)-len(seen_far), b-len(seen_far)))
        shift = {c: weight for c, weight in shift.items() if weight}
        moments = Counter()
        for c, weight in shift.items():
            for sub in subsets(c):
                moments[sub] += weight
        assert {c: w for c, w in moments.items() if w} == dict(target)
        assert max(abs(w) for w in moments.values()) == comb(len(witnesses), b)
        assert not project(shift, ell) and project(shift, ell+1)
        if physical:
            law = {c: prob+delta*shift.get(c, 0) for c, prob in null.items()}
            measured = check_law(law, uniform, natural, h, L, epsilon)
            assert all(measured[c]-natural[c] == delta*target[c] for c in measured)
            t = delta*P**(j+b)
            assert all(abs(law[c]/null[c]-1) <= 2**(h+1)*t for c in law)
        def tag_order(direction):
            return tuple(v for z in (1, -1) for k, group in enumerate(groups)
                         for v in group if tags[v]*(direction if k == 0 else 1) == z)
        oracle = (tag_order(1), tag_order(-1))
        # Exhaust the smallest mixed model; include tag-oracle and interlaced
        # orders in every larger model without enumerating (2*g*s)! orders.
        alternatives = list(permutations(local)) if len(local) <= 4 else [
            local, tuple(reversed(local)), tuple(v for column in zip(*groups) for v in column)]
        for order in (*oracle, *alternatives):
            r = ranks((*anchors, *order, *witnesses))
            actual = expected_cost(r, shift, 0)
            sums = [0]*s
            prefix_sum = 0
            for v in order:
                sums[(v-local[0])//(2*g)] += tags[v]
                prefix_sum += prod(sums)
            assert actual == multiplier*prefix_sum
            if order in oracle:
                assert actual == (1 if order == oracle[0] else -1)*multiplier*g**(s+1)
            checks += 1
    return checks


if __name__ == '__main__':
    print(f'{check_degree_cubes()} signed-degree moment and post-anchor cost checks')
    P = 1_000_000
    menu = first_primes(P, 2)+first_primes(8*P//5, 4)+first_primes(19*P//10, 4)
    count, ht = check_witnesses(3, P, menu, range(2), range(2, 6), range(6, 10), False)
    print(f'{count} far-witness cost checks and {ht} exact thinning-moment checks (ell=0,1,2)')
    P = 100_000
    first = next(x for x in range(180001, 189991, 2)
                 if all(is_prime(x+d) for d in (0, 2, 6, 8)))
    menu = first_primes(P, 96)+[first+d for d in (0, 2, 6, 8)]+first_primes(195000, 3)
    count, _ = check_witnesses(2, P, menu, range(96), range(96, 100), range(100, 103), True)
    print(f'{count} tied-null, balanced-oracle cost checks on an admissible physical law (ell=0,1)')
    proxies = check_proxies()
    print(f'{proxies["words/orders"]} cheap/fine proxy checks, including '
          f'{proxies["outside gate"]} outside the gate and {proxies["active prefixes"]} active prefixes')
    count = sum(check_padded(j, ell, h) for h in (3, 4)
                for j in range(1, h+1) for ell in range(h))
    count += check_padded(3, 2, 4, g=1, physical=True)
    print(f'{count} padded-cube cost checks across all degrees; physical mixed model h=4,j=3,ell=2')
