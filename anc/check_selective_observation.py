"""Exact finite checks for the selective-message theorem in natural_messages.tex.

All probabilities are Fractions. The transcript tests use genuine CRT words
and a small signed-cube law, rather than an asymptotic density construction.
"""

from collections import Counter
from fractions import Fraction as Q
from itertools import combinations, permutations, product
from math import comb, prod

from check_natural_observation import add_cube, observed
from check_natural_window import first_primes, subsets


def check_extensions():
    primes = (31, 37, 41, 53, 59, 61, 79)
    n, gap = len(primes), 12
    labels = tuple(range(n))
    order_pairs = [(i, j) for i, j in combinations(labels, 2) if primes[j]-primes[i] > gap]
    width = max(sum(left <= x <= left+gap for x in primes) for left in primes)
    prefixes, rank_vectors = set(), []
    for pi in permutations(labels):
        r = tuple(pi.index(i)+1 for i in labels)
        if all(r[i] < r[j] for i, j in order_pairs):
            assert all(abs(position-i-1) <= width for i, position in enumerate(r))
            rank_vectors.append(r)
            prefixes.update(frozenset(pi[:k]) for k in range(n+1))
    # Every ideal occurs as some linear-extension prefix.
    assert prefixes == {frozenset(s) for s in subsets(labels)
                        if all(j not in s or i in s for i, j in order_pairs)}
    prefixes = sorted(prefixes, key=lambda s: (len(s), sorted(s)))
    signatures = {e: tuple(p.issuperset(e) for p in prefixes) for e in subsets(labels)}
    counts = Counter()
    for h in (3, 4):
        events = list(combinations(labels, h))
        for e in events:
            maximal = tuple(i for i in e if primes[e[-1]]-primes[i] <= gap)
            assert maximal == tuple(i for i in e if not any((i, j) in order_pairs for j in e))
            for subset in subsets(e):
                assert (signatures[subset] == signatures[e]) == set(maximal).issubset(subset)
            # In particular each claimed maximum is attained by a legal order.
            assert set(maximal) == {max(e, key=r.__getitem__) for r in rank_vectors}
        for ell in (0, 1, 2):
            theta = Q(1, 2**ell)
            for pi_rank in rank_vectors:
                for e in events:
                    maximal = tuple(i for i in e if primes[e[-1]]-primes[i] <= gap)
                    full = e[-1]+1-max(pi_rank[i] for i in e)
                    base = e[-1]+1-max(pi_rank[i] for i in e[-ell:]) if ell else 0
                    correction = full-base
                    eligible = len(maximal) > ell
                    assert not correction or eligible
                    assert max(pi_rank[i] for i in maximal) == max(pi_rank[i] for i in e)
                    assert abs(correction) <= 2*width
                    send = theta if eligible else Q(0)
                    on_send = base+Q(correction, theta)
                    assert (1-send)*base + send*on_send == full
                    counts['rank identities'] += 1
            nonzero = 0
            for R in prefixes:
                k = len(R)
                A = frozenset(labels[:k])
                assert frozenset(labels[:max(0, k-width)]) <= R <= set(labels[:k+width])
                support = []
                for e in events:
                    full = int(R.issuperset(e))-int(A.issuperset(e))
                    base = int(R.issuperset(e[-ell:]))-int(A.issuperset(e[-ell:])) if ell else 0
                    if full == base:
                        continue
                    support.append(e)
                    assert k-width < e[-1]+1 <= k+width
                    assert primes[e[-1]]-primes[e[-ell-1]] <= gap
                # Select the greatest index, ell nearby predecessors, and the rest.
                assert len(support) <= 2*width*comb(width-1, ell)*comb(n, h-ell-1)
                nonzero += len(support)
                counts['prefix supports'] += 1
            assert nonzero > 0
    return len(rank_vectors), len(prefixes), counts


def check_conditional_support():
    # Each three-prime window is an antichain before every later window.
    # Enumerate every ideal, including prefixes away from the interior of a
    # window, without enumerating the 6**15 linear extensions.
    h, blocks, width, gap = 3, 15, 3, 80
    primes = [p for k in range(blocks) for p in first_primes(10001+600*k, width)]
    n = len(primes)
    assert all((primes[j]-primes[i] <= gap) == (i//width == j//width)
               for i, j in combinations(range(n), 2))
    records = list(combinations(range(n), h))
    checks = 0
    for ell in (0, 1, 2):
        by_block = [[] for _ in range(blocks)]
        denominators = [0, 0]
        for e in records:
            last_block = e[-1]//width
            if sum(i//width == last_block for i in e) <= ell:
                continue
            # Two bounded, nonuniform positive h-cell weight systems.
            weights = (12+sum(e) % 5, 12+(3*e[0]+e[2]) % 7)
            by_block[last_block].append((e, weights))
            for t, mass in enumerate(weights):
                denominators[t] += mass
        for k, local in enumerate(by_block):
            first = width*k
            for segment in subsets(range(first, first+width)):
                prefix = set(range(first)).union(segment)
                boundary = len(prefix)
                numerators = [0, 0]
                for e, weights in local:
                    complete = int(prefix.issuperset(e))
                    proxy = int(prefix.issuperset(e[-ell:])) if ell else int(e[-1] < boundary)
                    if complete != proxy:
                        for t, mass in enumerate(weights):
                            numerators[t] += mass
                # Outside this block, every eligible set is either fully in
                # the prefix or has a largest index in a strictly later block.
                for affected, eligible in zip(numerators, denominators):
                    assert Q(affected, eligible) <= Q(2*h*width, n)
                    checks += 1
    return checks


def word_experiment(h, ell, bits):
    """The free-record kernel hides independent signs in disjoint first-group pairs."""
    k = ell+1
    anchors = tuple(range(h-k))
    first = len(anchors)
    groups = [tuple(range(first, first+2*bits))]
    for _ in range(1, k):
        groups.append(tuple(range(groups[-1][-1]+1, groups[-1][-1]+3)))
    trades = [Counter() for _ in range(bits)]
    for tail in product(*groups):
        offset = tail[0]-first
        sign = (-1)**((offset % 2)+sum(i == group[-1] for i, group in zip(tail[1:], groups[1:])))
        add_cube(trades[offset//2], (*anchors, *tail), sign)
    cells = sorted(set().union(*trades), key=lambda c: (len(c), c))
    weight = {c: 2+len(c)+(sum(c) % 3) for c in cells}
    total = sum(weight.values())
    prime_list = first_primes(31, groups[-1][-1]+1)
    modulus = prod(prime_list)
    null, cell_of = {}, {}
    delta = [Counter() for _ in range(bits)]
    for c in cells:
        # Odd, zero modulo exactly the menu primes in c, one modulo the rest.
        hits = prod(prime_list[i] for i in c)
        other = 2*(modulus//hits)
        first_word = hits*pow(hits, -1, other)
        assert sum(bool(trade[c]) for trade in trades) <= 1
        for offset in (1, 2):
            word = first_word + 2*modulus*offset
            assert word % 2 and tuple(i for i, p in enumerate(prime_list) if word % p == 0) == c
            cell_of[word] = c
            null[word] = Q(weight[c], 2*total)
            for i, trade in enumerate(trades):
                delta[i][word] = Q(trade[c], 2*total)
    base = {word: observed(c, ell) for word, c in cell_of.items()}
    assert sum(null.values()) == 1
    for trade in delta:
        projection = Counter()
        for word, change in trade.items():
            projection[base[word]] += change
        assert not any(projection.values())
    return null, base, delta


def transmitted(law, base, policy):
    out = Counter()
    for word, mass in law.items():
        b = base[word]
        send = policy(word, b)
        assert 0 <= send <= 1
        out[b, None] += mass*(1-send)
        out[b, word] += mass*send
    return {key: value for key, value in out.items() if value}


def chi2(p, q):
    assert p.keys() == q.keys()
    return sum((p[x]-q[x])**2/q[x] for x in q)


def supplement_mass(output):
    return sum(value for (_, mark), value in output.items() if mark is not None)


def local_comparison(p, q, base, policy, eta, low_ratio):
    out_p, out_q = transmitted(p, base, policy), transmitted(q, base, policy)
    free_p, free_q, marked_q, marked_chi = (Counter() for _ in range(4))
    for (b, mark), mass in out_q.items():
        change = out_p[b, mark]-mass
        assert low_ratio <= out_p[b, mark]/mass <= 1+eta
        free_p[b] += out_p[b, mark]
        free_q[b] += mass
        if mark is not None:
            marked_q[b] += mass
            marked_chi[b] += change**2/mass
    assert free_p == free_q
    silence_informs = False
    for b, free in free_q.items():
        silent = out_q.get((b, None), Q(0))
        change = out_p.get((b, None), Q(0))-silent
        assert silent+marked_q[b] == free
        assert abs(change) <= eta*min(marked_q[b], silent)
        assert marked_chi[b] <= eta**2*marked_q[b]
        assert not silent or change**2/silent <= eta**2*marked_q[b]
        silence_informs |= bool(change)
    div = chi2(out_p, out_q)
    assert div <= 2*eta**2*supplement_mass(out_q)
    assert div <= 2*eta**2*supplement_mass(out_p)/low_ratio
    return out_p, out_q, div, silence_informs


def policy_for(stage, history=None):
    if stage == 0:
        return lambda word, b: Q(0)
    if stage == 1:
        return lambda word, b: Q(1)
    salt = 1 if history is None else 1+history[0][0]+int(history[1] is None)*3+(history[1] or 0) % 5
    def policy(word, b):
        if not b[0]:
            return Q(salt % 2)
        return Q((word % 11 + salt*bin(word).count('1') + b[0]) % 9, 8)
    return policy


def check_channels(ell, bits):
    null, base, deltas = word_experiment(3, ell, bits)
    tau = Q(1, 5)
    def make_law(signs):
        law = {word: mass+tau*sum(sign*delta[word] for sign, delta in zip(signs, deltas))
               for word, mass in null.items()}
        assert sum(law.values()) == 1 and min(law.values()) > 0
        assert all(1-tau <= law[w]/null[w] <= 1+tau for w in null)
        return law
    signs_all = list(product((-1, 1), repeat=bits))
    laws = {signs: make_law(signs) for signs in signs_all}
    checks = 0
    for signs in signs_all:
        left = laws[signs]
        flipped = (-signs[0], *signs[1:])
        for right in (null, laws[flipped], laws[tuple(-s for s in signs)]):
            ratios = [left[w]/right[w] for w in null]
            lo, hi = min(ratios), max(ratios)
            eta = max(hi-1, 1-lo)
            for stage in (0, 1, 2):
                _, _, div, leaked = local_comparison(left, right, base, policy_for(stage), eta, lo)
                if stage == 0:
                    assert div == 0
                elif stage == 1:
                    assert div == chi2(left, right)
                else:
                    assert leaked, 'this test must exercise informative silence'
                checks += 1
        if signs not in signs_all[:1]:
            continue
        # A shared first-round public transcript selects a different raw-word
        # channel on round two. Test both a planted/null and a local sign flip.
        for right in (null, laws[flipped]):
            ratios = [left[w]/right[w] for w in null]
            lo, hi = min(ratios), max(ratios)
            eta = max(hi-1, 1-lo)
            a, b, first_div, _ = local_comparison(left, right, base, policy_for(2), eta, lo)
            chain_upper, chi_chain, budget = first_div, first_div, supplement_mass(a)
            exact_joint = Q(0)
            second_laws = set()
            for history in b:
                p2, q2, second_div, _ = local_comparison(left, right, base, policy_for(2, history), eta, lo)
                second_laws.add(supplement_mass(p2))
                budget += a[history]*supplement_mass(p2)
                chain_upper += a[history]*second_div
                chi_chain += a[history]**2/b[history]*second_div
                exact_joint += sum((a[history]*p2[y]-b[history]*q2[y])**2/(b[history]*q2[y]) for y in q2)
            assert len(second_laws) >= 2
            assert exact_joint == chi_chain
            # The KL chain rule bounds transcript KL by chain_upper; the raw
            # chi-squared transcript obeys a different likelihood-weighted identity.
            assert chain_upper <= 2*eta**2*budget/lo
            assert exact_joint <= 2*hi*eta**2*budget/lo
            checks += 1
    return checks


if __name__ == '__main__':
    extensions, prefixes, counts = check_extensions()
    print(f'{extensions} legal orders, {prefixes} distinct prefixes, '
          f'{counts["rank identities"]} HT expectations, {counts["prefix supports"]} support bounds')
    print(f'{check_conditional_support()} conditional prefix support bounds on a 45-prime menu')
    for ell in (0, 1, 2):
        checks = sum(check_channels(ell, bits) for bits in (2, 3))
        print(f'ell={ell}: {checks} exact channel checks, including two-step public adaptation')
