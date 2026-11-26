"""Learn a two-hit ordering from actual odd integers on a finite physical block.

Run python3 raw_pair_experiment.py [--out raw_pair_experiment.csv] from here.
Only the Python standard library and the adjacent exact-check helpers are used.

Each source integer is odd and lies in [2L,4L). Increasing order and the
three fitted rules use the same natural-moment information, the same known
tied reference, and a common known region outside four possibly tilted
cells. The 384-prime case satisfies the theorem's P range; the 100-prime
case reproduces an earlier physical stress check outside that range. In
both, the cube coefficient D is 1000 times the proof construction's small
coefficient, and the actual resulting law satisfies the model's density,
hit cap and natural low moment conditions as checked exactly. For every
word the rule receives either the hit pair or just its cardinality and
largest index, obtained by dividing the actual integer by all menu primes.
On ordinary draws the latter rule has no access to informative-cell labels.
On the targeted arm both rules know that the sample is from that stratum.
The generator uses the hidden population to implement this conditional
oracle. Such draws are unavailable from a passive stream at unit raw cost.
Cell sampling and integer generation are exact. The four-cell histogram
times the known stratum probability is unbiased at fixed conditional K.
"""

import argparse
import csv
from fractions import Fraction as F
from itertools import combinations, permutations
from math import comb, lcm, log, prod, sqrt
from pathlib import Path
from random import Random
from statistics import mean, stdev

from check_natural_observation import add_cube, bin_trade
from check_natural_window import (
    check_admissible, first_primes, physical_cells, reference_cells,
)


H, EPS = 2, F(1, 2)
MENUS = ((100,100_000,187631), (384,43416,69491))
SEEDS = (7841, 31219, 406099, 760447)
REPEATS = 32
SIZES = (0, 4, 8, 16, 32, 64, 128, 256, 512)
DIRECT_N = 32768


def setup(m,P,first_tail):
    D = F(1,8*P**2)
    anchors = tuple(range(m-4))
    tails = tuple(range(m-4,m))
    quartet = [first_tail+i for i in (0,2,6,8)]
    assert first_primes(first_tail,4) == quartet
    primes = first_primes(P,len(anchors)) + quartet
    assert primes[m-5] <= F(6,5)*P and F(8,5)*P <= primes[m-4] < primes[-1] <= 2*P
    if m == 384:
        assert 10*m*log(m) <= P <= 20*m*log(m)
    q = [F(1,p) for p in primes]
    natural, reference = reference_cells(primes,H)
    uniform = physical_cells(primes,H,P,EPS)
    length = 1 << (int(1000*(2*P)**H/EPS)-1).bit_length()
    assert 4*length < P**3 and 2*length > 2*P
    tied = reference.copy()
    for size in (1,2):
        for tail in combinations(tails,size):
            anchor_part = 1-sum(q[:len(anchors)]) if size == 1 else 1
            copies = len(anchors) if size == 1 else 1
            value = (-1)**size*(q[tails[1]]**size-prod(q[i] for i in tail))*anchor_part/copies
            assert abs(value) <= D/4
            for completion in combinations(anchors,H-size):
                add_cube(tied,(*completion,*tail),value)
    trade,_,_ = bin_trade(anchors,H,1,1)
    laws = {s:{e:p+s*D/2*trade[e] for e,p in tied.items()} for s in (-1,1)}
    bins = tuple((i,j) for i in tails[:2] for j in tails[2:])
    mass = sum(tied[e] for e in bins)
    assert all(tied[e] == mass/4 for e in bins)
    assert all(laws[-1][e] == laws[1][e] for e in tied if e not in bins)
    for law in laws.values():
        check_admissible(law,uniform,natural,H,EPS)
        assert min(law[i,] for i in range(len(primes))) > F(1,4*P)
        # An anchor's signed pair corrections against each tail do not depend
        # on which anchor it is. This gives increasing order among anchors.
        resid = {e:law[e]-natural[e] for e in natural if len(e)==2}
        for t in tails:
            assert len({resid[i,t] for i in anchors}) == 1
        assert all(resid[i,j] == 0 for i,j in combinations(anchors,2))
        degree = [F(0) for _ in primes]
        for (i,j),v in resid.items():
            if v:
                degree[i] += abs(v)
                degree[j] += abs(v)
        # Uniform positive hazard gaps force every anchor before every tail.
        assert ((q[anchors[-1]]-q[tails[0]])*(1-sum(q)) >
                max(degree[:len(anchors)])+max(degree[len(anchors):]))
    # No other exact cell can vary with the hidden sign. Verify conditional
    # tails' costs directly from their exact physical masses.
    tail_laws = {s:{e:p for e,p in law.items() if e and e[0] in tails}
                 for s,law in laws.items()}
    tail_ref = {e:p for e,p in tied.items() if e and e[0] in tails}
    orders = list(permutations(tails))
    first = [[min(order.index(i)+1 for i in e) for e in bins] for order in orders]
    def tail_cost(order,law):
        return sum(p*min(order.index(i)+1 for i in e) for e,p in law.items())
    base = tail_cost(orders[0],tail_ref)
    assert all(tail_cost(o,tail_ref) == base for o in orders)
    losses = {}
    for s in laws:
        diffs = [tail_cost(o,tail_laws[s])-base for o in orders]
        assert min(diffs) == -D/2 and diffs[0] == 0
        assert all(diffs[k] == sum((laws[s][e]-tied[e])*first[k][j] for j,e in enumerate(bins))
                   for k in range(len(orders)))
        losses[s] = [int((v-min(diffs))/(D/2)) for v in diffs]
    assert all(a+b==2 for a,b in zip(losses[-1],losses[1]))
    return primes, length, uniform, laws, bins, mass, first, losses


def decode(n,primes):
    return tuple(i for i,p in enumerate(primes) if n%p == 0)


class TargetedWords:
    def __init__(self,primes,length,law,bins):
        self.primes, self.length = primes,length
        den = lcm(*(law[e].denominator for e in bins))
        weights = [int(law[e]*den) for e in bins]
        self.total = sum(weights)
        self.cells = []
        cum = 0
        for pair,w in zip(bins,weights):
            cum += w
            pq = prod(primes[i] for i in pair)
            first = ((2*length+pq-1)//pq) | 1
            count = ((4*length-1)//pq-first)//2+1
            assert count>0
            self.cells.append((cum,pq,first,count))

    def draw(self,rng):
        # Only the generator sees the cell. Every observation of a learner
        # is computed afresh from the returned integer.
        pick = rng.randrange(self.total)
        for upper,pq,first,count in self.cells:
            if pick < upper:
                return pq*(first+2*rng.randrange(count))
        raise AssertionError('unreachable ticket')


class OrdinaryWords:
    def __init__(self,primes,length,uniform,law):
        self.primes, self.length = primes,length
        self.accept = {}
        for e,physical in uniform.items():
            p = law[e]/((1+EPS)*physical)
            assert 0 < p <= 1
            full,rest = divmod(p.numerator << 64,p.denominator)
            self.accept[e] = full,rest,p.denominator

    def draw(self,rng):
        while True:
            n = 2*self.length+1+2*rng.randrange(self.length)
            hits = decode(n,self.primes)
            cut,rest,den = self.accept[hits]
            ticket = rng.getrandbits(64)
            if ticket < cut or (ticket == cut and rng.randrange(den) < rest):
                return n


def choose(coeff,first):
    return min(range(len(first)),key=lambda j:sum(x*a for x,a in zip(first[j],coeff)))


def fit(counts,first,right_imbalance):
    # Four edges in row-major order: (++),(+-),(-+),(--). Net true mass
    # outside these cells is supplied as a common, known control variate.
    K = sum(counts)
    maximum_only = choose([right_imbalance,-right_imbalance]*2,first)
    if not K:
        return [maximum_only,0,0]
    # Coefficients below are proportional to the empirical contrasts from
    # the reference uniform four-cell conditional distribution.
    unprojected = [4*x-K for x in counts]
    # Known physical low-moment constraints make the feasible residual a
    # 2x2 matrix of zero row and column sums, with just one free contrast.
    sign = (1,-1,-1,1)
    contrast = sum(x*a for x,a in zip(counts,sign))
    constrained = [contrast*x for x in sign]
    return [maximum_only,choose(unprojected,first),choose(constrained,first)]


def experiment(m,P,first_tail):
    D = F(1,8*P**2)
    primes,length,uniform,laws,bins,mass,first,losses = setup(m,P,first_tail)
    methods = ('max_only','two_hit_empirical','two_hit_fixed_margins')
    mask = {e:i for i,e in enumerate(bins)}
    target = {s:TargetedWords(primes,length,law,bins) for s,law in laws.items()}
    ordinary = {s:OrdinaryWords(primes,length,uniform,law) for s,law in laws.items()}
    right = (bins[0][1],bins[1][1])
    # Training exposes actual right maxima in all two-hit words, including
    # ordinary anchor-tail hits. Their reference column masses are known.
    def right_max_mass(law,j):
        return sum(p for e,p in law.items() if len(e)==2 and e[-1]==j)
    base_right = [right_max_mass(laws[-1],j) for j in right]
    assert base_right == [right_max_mass(laws[1],j) for j in right]
    rows = []
    def add(source,s,seed,repeat,words,right_counts,counts):
        contrast = right_counts[0]-right_counts[1]
        if source=='ordinary' and sum(right_counts):
            contrast -= words*(base_right[0]-base_right[1])
        selected = fit(counts,first,contrast)
        for name,index in zip(methods,selected):
            ratio = losses[s][index]
            rows.append(dict(menu_primes=m,P=P,source=source,hidden_sign=s,seed=seed,replicate=repeat,
                             observed_words=words,informative_words=sum(counts),
                             larger_index_first=right_counts[0],larger_index_second=right_counts[1],
                             pair_counts=';'.join(map(str,counts)),
                             method=name,regret_over_ascending=ratio,
                             regret_probes=float(D/2*ratio),order_index=index))
    for s in (-1,1):
        for seed in SEEDS:
            menu_seed = 0 if m == 100 else 10**15
            direct = Random(menu_seed+10**10+10*seed+(s+1)//2)
            counts = [0]*4
            right_counts = [0,0]
            for _ in range(DIRECT_N):
                n = ordinary[s].draw(direct)
                hits = decode(n,primes)
                if len(hits)==2 and hits[-1] in right:
                    right_counts[right.index(hits[-1])] += 1
                if hits in mask:
                    counts[mask[hits]] += 1
            add('ordinary',s,seed,0,DIRECT_N,right_counts,counts)
            for repeat in range(REPEATS):
                rng = Random(menu_seed+10**12+1000*seed+2*repeat+(s+1)//2)
                counts = [0]*4
                right_counts = [0,0]
                add('conditional',s,seed,repeat,0,right_counts,counts)
                for j in range(1,SIZES[-1]+1):
                    n = target[s].draw(rng)
                    assert 2*length < n < 4*length and n%2
                    hits = decode(n,primes)
                    right_counts[right.index(hits[-1])] += 1
                    counts[mask[hits]] += 1
                    if j in SIZES:
                        assert right_counts == [counts[0]+counts[2],counts[1]+counts[3]]
                        add('conditional',s,seed,repeat,j,right_counts,counts)
    print('Menu m=%d, P=%d, L=%d, informative mass=%.12g, ascending excess=%.12g probes.'
          % (m,P,length,float(mass),float(D/2)),flush=True)
    directs = [r for r in rows if r['source']=='ordinary' and r['method']==methods[0]]
    total = sum(r['observed_words'] for r in directs)
    hits = sum(r['informative_words'] for r in directs)
    print('%d ordinary words, %d informative, expectation %.6g.'%(total,hits,total*float(mass)))
    print('K    expected ordinary draws for K hits    max-only   empirical pair   fixed margins   exact fixed-margin mean')
    match = float(F(1,2)+D/mass)
    for K in SIZES:
        out = []
        for method in methods:
            observations = [r['regret_over_ascending'] for r in rows if
                            r['source']=='conditional' and r['observed_words']==K and r['method']==method]
            out.append('%.3f (%.3f)'%(mean(observations),stdev(observations)/sqrt(len(observations))))
        risk = sum(comb(K,k)*match**k*(1-match)**(K-k)*(2 if 2*k<K else 1)
                   for k in range(K//2+1))
        print('%-4d %-35.6g %s    %.6g' % (K,K/float(mass),'    '.join(out),risk))
    return rows


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,default=Path(__file__).with_suffix('.csv'))
    output = parser.parse_args().out
    result = []
    for menu in MENUS:
        result.extend(experiment(*menu))
    with output.open('w',newline='') as stream:
        writer = csv.DictWriter(stream,result[0].keys(),lineterminator='\n')
        writer.writeheader()
        writer.writerows(result)
