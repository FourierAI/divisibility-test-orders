"""Recompute released first-hit selections independently from the integer generator."""
import csv
import itertools
import statistics
from pathlib import Path

BASE = Path(__file__).resolve().parent
PRIMES = (1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733)
ALL = (1 << len(PRIMES)) - 1
U64 = (1 << 64) - 1
SIZES = (64, 256, 1024, 8192)
EDGES = (((0, 1), (2, 3), (0, 2), (0, 2), (1, 3), (1, 3)),
         ((0, 1), (2, 3), (0, 3), (0, 3), (1, 2), (1, 2)))
COVERS = tuple(sorted(sum(1 << x for x in group)
                      for group in itertools.combinations(range(12), 6)))


def stream(seed):
    while True:
        seed = (seed + 0x9e3779b97f4a7c15) & U64
        z = ((seed ^ (seed >> 30)) * 0xbf58476d1ce4e5b9) & U64
        z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & U64
        yield z ^ (z >> 31)


def bounded(rng, size):
    limit = (1 << 64) % size
    for value in rng:
        if value >= limit:
            return value % size


def words(law, seed, count):
    rng = stream(seed)
    for _ in range(count):
        if law == 2:
            yield next(rng) | 1
            continue
        product = 1
        if bounded(rng, 5):
            group = 4 * bounded(rng, 3)
            i, j = EDGES[law][bounded(rng, 6)]
            product = PRIMES[group+i] * PRIMES[group+j]
        lower = (((1 << 63) + product - 1) // product) | 1
        width = ((U64 // product - lower) // 2) + 1
        while True:
            cofactor = lower + 2 * bounded(rng, width)
            if all(cofactor % p for p in PRIMES):
                yield product * cofactor
                break


def first(mask):
    return mask & -mask


def best(hist):
    return max(COVERS, key=lambda selection:
               sum(count for mask, count in hist.items() if mask & selection))


def mask_of(word):
    return sum((1 << j) for j, p in enumerate(PRIMES) if word % p == 0)


def read_rows(root, name):
    with (root / (name + '.csv')).open() as file:
        return list(csv.DictReader(file))


def fit_check(rows):
    law, seed, mark_seed = (int(rows[0][k]) for k in ('law', 'word_seed', 'mark_seed'))
    marks = stream(mark_seed)
    fitted, fixed, complete = {}, {}, {}
    for n, word in enumerate(words(law, seed, max(SIZES)), 1):
        mask = mask_of(word)
        complete[mask] = complete.get(mask, 0) + 1
        j = first(mask)
        fixed[j] = fixed.get(j, 0) + 1
        positive = next(marks) & ALL
        # An unmarked hit can be logged only when no marked divisor hits.
        if j and not mask & positive:
            fitted[j] = fitted.get(j, 0) + 2
            for i in range(j.bit_length(), len(PRIMES)):
                bit = 1 << i
                change = -4 if positive & bit else 4
                fitted[j | bit] = fitted.get(j | bit, 0) + change
                fitted[j] -= change // 2
        if n in SIZES:
            row = next(r for r in rows if int(r['train_n']) == n)
            selected = best(fitted)
            assert selected == int(row['one_hit_mask'])
            for s, column in ((law, 'matching_tickets'), (1-law, 'shifted_tickets')):
                count = sum(bool(selected & (((1 << i) | (1 << j)) << offset))
                            for offset in (0, 4, 8) for i, j in EDGES[s])
                assert count == int(row[column])
    assert best(fixed) == int(rows[-1]['fixed_mask_8192'])
    assert best(complete) == int(rows[-1]['census_mask_8192'])


def run():
    roots = [BASE / name for name in ('stopped_results', 'stopped_repeat')]
    training = [read_rows(root, 'training') for root in roots]
    train_cols = [k for k in training[0][0] if not k.endswith('_ns_8192')]
    first_inputs, repeated_inputs = (
        [tuple(row[k] for k in train_cols) for row in session] for session in training)
    assert first_inputs == repeated_inputs
    held = read_rows(roots[0], 'heldout')
    assert held == read_rows(roots[1], 'heldout')
    for rep in range(5):
        for law in range(2):
            fit_check([r for r in training[0] if int(r['rep']) == rep and int(r['law']) == law])
        for law in range(3):
            subset = [r for r in held if int(r['rep']) == rep and int(r['law']) == law]
            census, fingerprint = {}, 14695981039346656037
            for word in words(law, int(subset[0]['test_seed']), int(subset[0]['words'])):
                fingerprint = ((fingerprint ^ word) * 1099511628211) & U64
                mask = mask_of(word) if word > (1 << 32)-1 else 0
                census[mask] = census.get(mask, 0) + 1
            for r in subset:
                assert fingerprint == int(r['hash'])
                assert sum(count for mask, count in census.items() if mask & int(r['menu_mask'])) == int(r['rejected'])
    for n in SIZES:
        recovered = sum(r['matching_tickets'] == '18' for r in training[0] if int(r['train_n']) == n)
        print(f'{n} one-hit records: {recovered}/10 selections cover all 18 positive tickets.')
    for root in roots:
        rows = read_rows(root, 'timings')
        print(root.name)
        for law in range(3):
            medians = {}
            for name in ('FLINT', 'packet', 'all12', 'fixed_log_A', 'full_A', 'first_A', 'first_B', 'full_B'):
                per_seed = [statistics.median(float(r['ns']) for r in rows if int(r['law']) == law
                            and r['method'] == name and int(r['rep']) == rep) for rep in range(5)]
                medians[name] = round(statistics.median(per_seed), 2)
            print(law, medians)


if __name__ == '__main__':
    run()
