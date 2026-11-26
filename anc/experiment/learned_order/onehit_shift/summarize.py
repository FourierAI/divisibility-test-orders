"""Recalculate per-seed inference medians, paired differences, and amortization."""
import csv
import math
import statistics as st
import sys
from collections import defaultdict
from pathlib import Path


def read(path):
    with path.open() as stream:
        return list(csv.DictReader(stream))


def summarize(root):
    counts = read(root / 'counts.csv')
    groups = defaultdict(list)
    rounds = defaultdict(set)
    seeds = defaultdict(set)
    for row in read(root / 'timings.csv'):
        key = row['law'], row['method'], int(row['rep'])
        groups[key].append(float(row['ns_per_word']))
        rounds[key].add((int(row['position']), int(row['round'])))
        seeds[row['law'], int(row['rep'])].add(row['seed'])
    for key, cells in rounds.items():
        assert len(cells) == 10
        assert len({p for p, r in cells}) == len({r for p, r in cells}) == 10
    assert all(len(v) == 1 for v in seeds.values())
    times = {key: st.median(v) for key, v in groups.items()}
    trained = defaultdict(list)
    tickets = {}
    for row in read(root / 'training.csv'):
        rep, source = int(row['rep']), int(row['source'])
        trained[source, rep].append(int(row['total_ns']))
        tickets[source, rep] = int(row['own_tickets']), int(row['shifted_tickets'])
    assert len(tickets) == 10 and all(len(v) == 7 for v in trained.values())
    training = {k: st.median(v) for k,v in trained.items()}
    order = ['flint','packet','all12','minimax6','first_A','first_B','cascade_A',
             'common9','oracle','targeted']
    laws = ['A','B','uniform','ABAB']
    assert len(times) == len(laws)*len(order)*5
    rejects = {(r['law'],r['method'],int(r['rep'])): int(r['all_rejects']) for r in counts}
    fingerprint = {}
    for row in counts:
        key=row['law'],int(row['rep'])
        value=(row['seed'],row['words'],row['hash'],row['primes'])
        assert fingerprint.setdefault(key,value)==value
    for law in laws:
        for rep in range(5):
            assert rejects[law,'all12',rep]==rejects[law,'cascade_A',rep]
            if law!='uniform':
                assert rejects[law,'all12',rep]==rejects[law,'common9',rep]==rejects[law,'oracle',rep]
    print(root)
    print('median ns/word', *order)
    for law in laws:
        print(law, *(f'{st.median(times[law,m,i] for i in range(5)):.2f}' for m in order))
    print('A matching tickets, shifted tickets', [tickets[0,i] for i in range(5)])
    print('B matching tickets, shifted tickets', [tickets[1,i] for i in range(5)])
    print('complete A training, us', [round(training[0,i]/1000,2) for i in range(5)])
    for comp in ['all12','common9','oracle','minimax6']:
        diff=[times['A',comp,i]-times['A','first_A',i] for i in range(5)]
        print('A paired',comp,'minus first_A',
              [round(x,3) for x in diff], 'break-even',
              [math.ceil(training[0,i]/v) if v>0 else None for i,v in enumerate(diff)])
    for law in laws:
        print(law, 'early rejection % A / minimax / common9 / targeted',
              *(round(100*sum(rejects[law,m,i] for i in range(5))/(32768*5),3)
                for m in ['first_A','minimax6','common9','targeted']))
        subset=[r for r in counts if r['law']==law and r['method']=='targeted']
        print(law,'targeted logs and certifications A/B',
              *(sum(int(r[k]) for r in subset) for k in ['diagnostic_logs','A_epochs','B_epochs']))
    return fingerprint, tickets


if __name__ == '__main__':
    roots=[Path(p) for p in sys.argv[1:]] or [Path(__file__).parent/f'session{i}' for i in (1,2)]
    expected=None
    for root in roots:
        found=summarize(root)
        if expected is not None:
            assert expected==found
        expected=found
