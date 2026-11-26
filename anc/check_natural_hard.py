"""Exact finite checks of the one-bin and many-bin noisy-parity construction.

The small menus check the algebra, physical word fibers and probability
channels. Their bin widths are chosen for enumeration, so they do not test
the asymptotic prime-count or pointwise-density bounds.
"""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from math import comb, prod

from check_natural_window import (
    containment_of, first_primes, invert_containment, reference_cells, subsets,
)


def equalize(primes, anchors, bins, h):
    moments, reference = reference_cells(primes, h)
    within_bin = {i: Fraction(1, primes[block[0]]) for block in bins for i in block}
    tails = sorted(within_bin)
    anchor_miss = [
        sum((-1)**len(cell) * moments[cell] for cell in subsets(anchors, k))
        for k in range(h + 1)
    ]
    null = reference.copy()
    for cell in subsets(tails, h):
        if not cell:
            continue
        k = h - len(cell)
        target = prod(within_bin[i] for i in cell)
        coef = ((-1)**len(cell) * anchor_miss[k] * (target - moments[cell])
                / comb(len(anchors), k))
        for core in combinations(anchors, k):
            for changed in subsets(core + cell):
                null[changed] += (-1)**len(changed) * coef
    assert min(null.values()) > 0 and sum(null.values()) == 1
    assert all(value == moments[j] for j, value in containment_of(null).items()
               if len(j) < h)
    return null


def active_edges(bins, h):
    edges = {}
    for b, block in enumerate(bins):
        for cell in combinations(block, h):
            offsets = [i - block[0] for i in cell]
            support = tuple(i // 2 for i in offsets)
            if len(set(support)) == h:
                tag_product = prod(1 if i % 2 == 0 else -1 for i in offsets)
                edges[cell] = (b, support, (-1)**(h + 1) * tag_product)
    return edges


def word_fibers(primes, h):
    # Every integer in this dyadic block has at most h of these prime divisors.
    # Count all fibers by counting odd multiples of each product and inversion.
    length = 1 << (prod(primes[:h + 1]).bit_length() - 3)
    assert 4 * length < prod(primes[:h + 1])
    counts = {}
    for cell in subsets(range(len(primes)), h):
        modulus = prod(primes[i] for i in cell)
        # Count odd k with 2L <= k * modulus < 4L.
        last = (4 * length - 1) // modulus
        first = (2 * length - 1) // modulus
        counts[cell] = (last + 1) // 2 - (first + 1) // 2
    fibers = invert_containment(counts)
    assert min(fibers.values()) > 0 and sum(fibers.values()) == length
    return length, fibers


def check_channels(primes, bins, null, gamma, h):
    theta = (1, -1, 1, -1)
    edges = active_edges(bins, h)
    q = [Fraction(1, primes[block[0]]) for block in bins]
    flags = [2**h * comb(len(block) // 2, h) * p**h for block, p in zip(bins, q)]
    inactive = 1 - sum(flags)
    assert inactive == sum(mass for cell, mass in null.items() if cell not in edges)
    length, fibers = word_fibers(primes, h)
    planted = null.copy()
    for cell, (b, support, y) in edges.items():
        assert null[cell] == q[b]**h
        modulus = prod(primes[i] for i in cell)
        multiplier = ((2 * length + modulus - 1) // modulus) | 1
        witness = multiplier * modulus
        assert 2 * length <= witness < 4 * length
        assert tuple(i for i, p in enumerate(primes) if witness % p == 0) == cell
        signal = prod(theta[j] for j in support)
        coef = (-1)**h * gamma * q[b]**h * signal * y
        for changed in subsets(cell):
            planted[changed] += (-1)**len(changed) * coef
    assert all(planted[cell] == null[cell] for cell in null if cell not in edges)
    assert min(planted.values()) > 0 and sum(planted.values()) == 1
    for bias, law in ((0, null), (gamma, planted)):
        aggregates = defaultdict(Fraction)
        for cell, mass in law.items():
            if cell in edges:
                b, support, y = edges[cell]
                ave = bias * prod(theta[j] for j in support)
                scope_mass = flags[b] / comb(len(bins[b]) // 2, h)
                generated = scope_mass * (1 + y * ave) / 2 / 2**(h - 1)
                aggregates[b, support, y] += mass
            else:
                generated = inactive * (null[cell] / inactive)
            # Both inverse kernels draw uniformly in the physical word fiber.
            assert mass / fibers[cell] == generated / fibers[cell]
        for (b, support, y), prob in aggregates.items():
            assert prob == (flags[b] * (1 + bias * y * prod(theta[j] for j in support))
                            / (2 * comb(len(bins[b]) // 2, h)))
    assert sum(fibers.values()) == length
    return planted, edges, theta, q


def check_prefixes(bins, null, planted, theta, q, gamma, h):
    tails = set(i for block in bins for i in block)
    # With all anchors pre-tested, tails-only exact cells determine survival.
    tail_cells = [j for j in null if set(j) <= tails]
    categories = {}
    # Test all prefixes in the one-bin model. In the two-bin model enumerate
    # all normalized prefixes plus genuinely mixed prefixes at both boundaries.
    prefixes = {frozenset()}
    done = frozenset()
    for block in bins:
        prefixes.update(done | frozenset(j) for j in subsets(block))
        done = done | frozenset(block)
    if len(bins) == 2:
        prefixes.update(frozenset((*a, *b)) for a in subsets(bins[0], 2)
                        for b in subsets(bins[1], 2))
    for prefix in prefixes:
        profile = tuple(len(prefix.intersection(block)) for block in bins)
        survivors = [j for j in tail_cells if prefix.isdisjoint(j)]
        base = sum(null[j] for j in survivors)
        assert categories.setdefault(profile, base) == base
        pert = sum(planted[j] - null[j] for j in survivors)
        predicted = 0
        for b, block in enumerate(bins):
            signed = [theta[i] * (int(block[2*i] in prefix) - int(block[2*i+1] in prefix))
                      for i in range(len(block) // 2)]
            score = sum(prod(values) for values in combinations(signed, h))
            predicted -= gamma * q[b]**h * score
        assert pert == predicted
    return len(prefixes)


def run(bin_starts):
    h, gamma, count = 3, Fraction(1, 20), 8
    anchor_primes = first_primes(10007, 22)
    primes = anchor_primes + [p for start in bin_starts for p in first_primes(start, count)]
    assert primes == sorted(set(primes))
    anchors = tuple(range(len(anchor_primes)))
    bins = [tuple(range(len(anchors) + i * count, len(anchors) + (i + 1) * count))
            for i in range(len(bin_starts))]
    null = equalize(primes, anchors, bins, h)
    planted, edges, theta, q = check_channels(primes, bins, null, gamma, h)
    n_prefixes = check_prefixes(bins, null, planted, theta, q, gamma, h)
    print(f"{len(bins)} bin(s), {len(null)} exact physical cells, "
          f"{len(edges)} active patterns, {n_prefixes} prefix checks passed")


if __name__ == "__main__":
    run([51407])
    run([51407, 65699])
