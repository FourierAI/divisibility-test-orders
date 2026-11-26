"""Reconstruct the ten fitted sets and 655360 inputs with direct integer division."""
from collections import Counter
from itertools import chain
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from summarize_stopped import ALL, U64, best, first, mask_of, read_rows, stream, words


def fit(r):
    histogram = Counter()
    marks = stream(int(r['mark_seed']))
    fingerprint = 14695981039346656037
    for n in words(int(r['source']), int(r['seed']), int(r['words'])):
        fingerprint = ((fingerprint ^ n)*1099511628211) & U64
        mask = mask_of(n)
        j = first(mask)
        sampled = next(marks) & ALL
        if j and not sampled & mask:
            histogram[j] += 2
            for k in range(j.bit_length(),12):
                bit=1<<k
                amount=-4 if sampled & bit else 4
                histogram[j|bit] += amount
                histogram[j] -= amount//2
    assert fingerprint==int(r['hash'])
    assert best(histogram)==int(r['mask'])
    return int(r['mask'])


def replay(root):
    training=read_rows(root,'training')
    sets={(r['rep'],int(r['source'])):fit(r) for r in training if r['round']=='0'}
    counts=read_rows(root,'counts')
    for rep in range(5):
        for law in ('A','B','uniform','ABAB'):
            subset={r['method']:r for r in counts if r['rep']==str(rep) and r['law']==law}
            r=subset['targeted']
            n=int(r['words'])
            seed=int(r['seed'])
            if law=='ABAB':
                seq=chain.from_iterable(words(j%2,seed+10000019*(j+1),k)
                                        for j,k in enumerate([8705,8676,8732,6655]))
            else:
                seq=words(('A','B','uniform').index(law),seed,n)
            fingerprint=14695981039346656037
            got=Counter()
            logs=cert_a=cert_b=0
            for i,num in enumerate(seq):
                fingerprint=((fingerprint^num)*1099511628211) & U64
                mask=mask_of(num)
                eligible=num>2**32-1
                for arm,choice in (
                    ('all12',ALL),('minimax6',0x333),('first_A',sets[str(rep),0]),
                    ('first_B',sets[str(rep),1]),('cascade_A',ALL),('common9',0x777)):
                    got[arm]+=bool(eligible and mask&choice)
                if i%2048==0:
                    mode=None
                    votes=[]
                if mode is None:
                    logs+=1
                    selected=(0x999,0x555)[i%2]
                    first_bit=first(mask&selected) or first(mask)
                    if first_bit and not (first_bit&selected):
                        vote='B' if selected==0x999 else 'A'
                        votes.append(vote)
                        if len(set(votes))>1: mode='packet'
                        elif len(votes)==2:
                            mode=vote
                            cert_a+=(vote=='A')
                            cert_b+=(vote=='B')
                    if i%2048==63 and mode is None: mode='packet'
                    got['targeted']+=bool(eligible and first_bit)
                else:
                    choice={'A':0x999,'B':0x555,'packet':0}[mode]
                    got['targeted']+=bool(eligible and mask&choice)
            assert fingerprint==int(r['hash'])
            for arm,count in got.items(): assert count==int(subset[arm]['all_rejects'])
            assert [logs,cert_a,cert_b]==[int(r[k]) for k in ('diagnostic_logs','A_epochs','B_epochs')]
    print('Ten first-hit fits and all 655,360 independently regenerated inputs and guard outcomes agree.')


if __name__=='__main__':
    replay(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).parent/'session1')
