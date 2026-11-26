"""Exact finite checks for the perturbed arithmetic screening construction."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import permutations
from math import comb, prod


def make_case(primes, h, edges, epsilon=F(1, 4)):
    m = len(primes)
    p = min(primes)
    q = F(1, p)
    delta = epsilon * q**h / 100
    # Smaller than the conservative proof constant; exact bounds checked below.
    length = 1 << (16 * p**h).bit_length()
    assert 4 * length < p ** (h+1)
    masks = range(1 << m)
    count = {}
    for mask in masks:
        d = prod(primes[i] for i in range(m) if mask & (1 << i))
        first = (-(2*length+1) * pow(2, -1, d)) % d if d != 1 else 0
        count[mask] = 0 if first >= length else 1 + (length-1-first)//d
    for i in range(m):
        for mask in masks:
            if mask & (1 << i) == 0:
                count[mask] -= count[mask | (1 << i)]
    assert sum(count.values()) == length
    b, dlaw = {}, {}
    for mask in masks:
        s = mask.bit_count() if hasattr(int,'bit_count') else bin(mask).count('1')
        b[mask] = sum((-1)**j * comb(m-s,j) * q**(s+j) for j in range(h-s+1))
        offset = sum((mask & edge) == mask for edge in edges)
        dlaw[mask] = b[mask] + (-1)**s * delta * offset
        if s > h:
            assert count[mask] == dlaw[mask] == 0
        else:
            assert count[mask]>0
            ratio = dlaw[mask]*length/count[mask]
            assert 1-epsilon <= ratio <= 1+epsilon, (mask,ratio)
    assert sum(dlaw.values()) == 1
    for mask in masks:
        s=bin(mask).count('1')
        if s<h:
            assert sum(dlaw[other] for other in masks if (other & mask)==mask)==q**s
    B=4*p
    def nohit(law):
        return {prefix:sum(v for hit,v in law.items() if not (hit & prefix)) for prefix in masks}
    d_survival,b_survival=nohit(dlaw),nohit(b)
    @lru_cache(None)
    def best(prefix):
        # Compare authentic optional fallback and every possible next test.
        return min([B*d_survival[prefix]]+
                   [d_survival[prefix]+best(prefix|(1<<i)) for i in range(m)
                    if not (prefix & (1<<i))])
    low=None
    for order in permutations(range(m)):
        prefix=0
        real=base=F(0)
        for i in order:
            real += d_survival[prefix]
            base += b_survival[prefix]
            prefix |= 1 << i
        real += B*d_survival[prefix]; base += B*b_survival[prefix]
        cover = sum(1+next(j for j,i in enumerate(reversed(order)) if (1<<i)&edge)
                    for edge in edges)
        assert real-base == delta*((B-1)*len(edges)+cover)
        low=real if low is None else min(low,real)
    assert best(0)==low
    return length,dlaw,b,delta


if __name__ == '__main__':
    primes=[1009,1013,1019,1021,1031,1033]
    for h, edges in [(2,[3,6,12,24,48]),(3,[7,14,52]),(4,[15,60])]:
        length,law,baseline,delta=make_case(primes,h,edges)
        print(f'h={h}: {length} odd words via exact CRT cell counts, 720 orders, 64 optional-stop states: OK')
    _,left,_,_=make_case(primes,3,[7])
    _,right,_,_=make_case(primes,3,[56])
    assert left!=right
    assert all(sum((left[m]-right[m]) for m in left if (m&mask)==mask)==0
               for mask in left if bin(mask).count('1')<=2)
    print('Disjoint 3-edge alternatives have identical all one- and two-test laws: OK')
