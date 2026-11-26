"""Exact finite audits for the fair-sign, truncated first-hit design."""
from collections import Counter
from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import comb, prod
from random import Random


def subsets(pool, k):
    for size in range(k + 1):
        yield from combinations(pool, size)


def choose(n, k):
    return comb(n, k) if 0 <= k <= n else 0


def ref_first(m, h, q, position):
    return q * sum((-q)**k * choose(position, k) for k in range(h))


def check_scores(h, rounded, m=8, w=1):
    ids = tuple(range(m))
    denominator = (37,41,43,47,53,59,61,67)[:m] if w==1 else (43,)*m
    units = 16*prod(denominator)
    cells = list(subsets(ids,h))
    cellset = {z:frozenset(z) for z in cells}
    reference_mom = {z:units//prod(denominator[i] for i in z) for z in cells}
    delta_mom = {z:0 for z in cells}
    for z in cells:
        sign = (sum((j+1)**2 for j in z) + sum(z)**2)%3-1
        if len(z) == h:
            delta_mom[z] = sign*(reference_mom[z]//16)
        elif z and rounded:
            delta_mom[z] = sign     # true moment error at most 1/units
    assert any(delta_mom[z] for z in cells if 0 < len(z) < h) == rounded

    def mobius(moment):
        return {z:sum((-1)**(len(y)-len(z))*moment[y] for y in cells
                      if cellset[z] <= cellset[y]) for z in cells}
    reference, change = mobius(reference_mom), mobius(delta_mom)
    assert sum(reference.values()) == units and sum(change.values()) == 0
    assert all(reference[z]+change[z] > 0 for z in cells)
    for z in cells:
        assert sum(change[y] for y in cells if cellset[z] <= cellset[y]) == delta_mom[z]

    # Right-looking tilings of the actual minimum, including both edge tiles.
    end = 2*w+1
    blocks = []
    for offset in (0,end):
        cuts = [0]+[c for c in range(offset,m,2*end) if c]+[m]
        blocks.append([tuple(range(l,r)) for l,r in zip(cuts,cuts[1:])])
    at = [{j:t for t in tiling for j in t} for tiling in blocks]
    selected = {j:next(a for a in ((0,1) if j%2 else (1,0))
                       if set(range(j,min(m,j+2*w+1))) <= set(at[a][j])) for j in ids}
    assert set(selected.values()) == {0,1}
    fields = {j:[(j,)+t for t in subsets(tuple(i for i in at[selected[j]][j] if i>j),h-1)]
              for j in ids}
    local = Counter()
    for z in cells:
        if z:
            j=z[0]
            local[tuple(i for i in z if i in at[selected[j]][j])] += change[z]
    for j in ids:
        for u in fields[j]:
            # The lower-order rounded errors enter the local mass through this
            # exact restricted inclusion-exclusion formula, including words with
            # arbitrary later hits outside the selected tile.
            forbidden = (set(range(j)) | set(at[selected[j]][j])) - set(u)
            available = tuple(sorted(forbidden))
            terms = [((-1)**len(z),tuple(sorted(u+z))) for z in subsets(available,h-len(u))]
            assert local[u] == sum(sign*delta_mom[y] for sign,y in terms)
            majorant = sum(abs(delta_mom[y]) for sign,y in terms)
            assert abs(local[u]) <= majorant

    # Enumerate the signed difference between the two conditional laws of the
    # first hit, independently scanning every original exact cell and all signs.
    observed = {}
    for a,tiling in enumerate(blocks):
        for mask in range(1<<m):
            sign = lambda j: bool(mask & (1<<j))
            priority = tuple(j for t in tiling for status in (True,False)
                             for j in t if sign(j)==status)
            rank = {j:i for i,j in enumerate(priority)}
            ref,physical = Counter(),Counter()
            for z in cells:
                first = min(z,key=rank.__getitem__) if z else -1
                ref[first] += reference[z]
                physical[first] += reference[z]+change[z]
            assert sum(physical.values()) == sum(ref.values()) == units
            observed[a,mask] = [physical[j]-ref[j] for j in ids]

    walsh = {}
    for j in ids:
        a=selected[j]
        for t in fields[j]:
            signed=sum(observed[a,mask][j] *
                       (-1)**sum(not mask&(1<<i) for i in t[1:])
                       for mask in range(1<<m) if not mask & (1<<j))
            walsh[t]=F(signed*2**(len(t)+1)*(-1)**(len(t)-1),2*(1<<m))
            assert walsh[t] == sum(F(local[u],2**(len(u)-len(t)))
                                   for u in fields[j] if cellset[t] <= cellset[u])

    legal_orders = [pi for pi in permutations(ids) if all(abs(i-j)<=w for i,j in enumerate(pi))]
    prefixes = {frozenset(pi[:i]) for pi in legal_orders for i in range(m+1)}
    true, estimated = {}, {}
    nonzero_bias = set()
    for prefix in prefixes:
        pos=len(prefix)
        natural=set(range(pos))
        direct={z:int(prefix.isdisjoint(z))-int(natural.isdisjoint(z)) for z in cells}
        true[prefix]=sum((reference[z]+change[z])*d for z,d in direct.items())
        ref_term=sum(reference[z]*d for z,d in direct.items())
        coef={}
        for j in ids:
            for t in fields[j]:
                def f(z):
                    return int(prefix.isdisjoint(z))-int(j>=pos)
                full=sum(F(-1,2)**(len(t)-1-len(v))*f((j,)+v)
                         for v in subsets(t[1:],len(t)-1))
                closed=F(int(j not in prefix)*(-1)**len(prefix.intersection(t[1:]))
                         -int(j>=pos),2**(len(t)-1))
                assert full == closed
                if abs(j-pos)>w:
                    assert full == 0
                coef[t]=full
        for s in range(1,h+1):
            recovered=sum(coef[t]*field for t,field in walsh.items() if len(t)<=s)
            from_cells=0
            for j in ids:
                for u in fields[j]:
                    val=sum(coef[t]*F(1,2)**(len(u)-len(t)) for t in fields[j]
                            if len(t)<=s and cellset[t]<=cellset[u])
                    actual=int(prefix.isdisjoint(u))-int(j>=pos)
                    assert abs(actual-val) <= 1
                    if len(u)<=s or abs(j-pos)>w:
                        assert actual == val
                    from_cells += val*local[u]
            assert recovered == from_cells
            estimated[s,prefix]=ref_term+recovered
            large=sum(abs(local[u]) for j in ids if abs(j-pos)<=w for u in fields[j] if len(u)>s)
            assert abs(estimated[s,prefix]-true[prefix]) <= large
            if estimated[s,prefix] != true[prefix]:
                nonzero_bias.add(s)
            if s==h:
                assert estimated[s,prefix] == true[prefix]

    def physical_cost(pi):
        rank={j:i for i,j in enumerate(pi)}
        return sum((reference[z]+change[z])*(min(rank[j] for j in z)-z[0])
                   for z in cells if z)
    cost={pi:physical_cost(pi) for pi in legal_orders}
    assert nonzero_bias == set(range(1,h))
    if w==2:
        assert min(cost.values()) < cost[ids]    # genuine optimization on a tied reference
    for s in range(1,h+1):
        upper=(2*w+1)*sum(abs(local[u]) for j in ids for u in fields[j] if len(u)>s)
        proxy={}
        for pi in legal_orders:
            sequence=[frozenset(pi[:t]) for t in range(m)]
            assert sum(true[r] for r in sequence)==cost[pi]
            proxy[pi]=sum(estimated[s,r] for r in sequence)
            assert abs(proxy[pi]-cost[pi]) <= upper
        champion=min(legal_orders,key=proxy.__getitem__)
        assert cost[champion]-min(cost.values())<=2*upper
        if s==h:
            assert proxy==cost and cost[champion]==min(cost.values())
    return len(walsh),len(prefixes)*h,len(legal_orders)*h


def lower_check(h, s, g, kbin):
    w = 2*s*g
    a = 2*w
    anchors = tuple(range(a))
    bins = []
    pairs = []
    for k in range(kbin):
        groups = []
        for d in range(s):
            pair_group = []
            for u in range(g):
                first = a + k*w + d*2*g + 2*u
                pair_group.append((first, first+1))
                pairs.append((first, first+1))
            groups.append(pair_group)
        bins.append(groups)
    m = a+kbin*w
    if h-s>a:
        raise ValueError("too few anchors")
    edges = []
    for groups in bins:
        for tails in product(*[sum((list(pair) for pair in group), []) for group in groups]):
            for anc in combinations(anchors,h-s):
                edges.append((anc+tails,tails))
    target = {j: (k,d) for k,groups in enumerate(bins) for d,group in enumerate(groups)
              for pair in group for j in pair}
    rng = Random(401*h + 17*s + 11*g + kbin)
    orders = [tuple(range(m)),tuple(reversed(range(m)))]
    # These priorities put a single endpoint of each balanced pair before
    # selected anchors, so the cross-bin anchor endpoint terms are exercised.
    mask_first = tuple(x for x, _ in pairs)
    mask_last = tuple(y for _, y in pairs)
    cut = max(0,h-s-1)
    orders.append(anchors[:cut]+mask_first+anchors[cut:]+mask_last)
    for _ in range(3):
        pi = list(range(m))
        rng.shuffle(pi)
        orders.append(tuple(pi))

    checks = 0
    nonzero_anchor = False
    for pi in orders:
        rank = {j: i for i,j in enumerate(pi)}
        pred = {j: set(pi[:rank[j]]) for j in pi}
        coeff = []
        for e, tails in edges:
            # Directly pass all 2^h signed cells of a cube through a first-hit logger.
            events = Counter()
            for z in subsets(e,h):
                y = min(z,key=rank.__getitem__) if z else -1
                events[y] += (-1)**(h-len(z))
            last = max(e,key=rank.__getitem__)
            assert events[-1] == (-1)**h and events[last] == (-1)**(h-1)
            assert all(v == 0 for y,v in events.items() if y not in (last,-1))
            coeff.append((last,tails))
        second = Counter()
        max_absolute = Counter()
        signs_examined = 0
        for sig in product((-1,1),repeat=len(pairs)):
            tag = {j: z*mult for (l,r),z in zip(pairs,sig) for j,mult in ((l,1),(r,-1))}
            signed = Counter()
            for last,tails in coeff:
                signed[last] += prod(tag[v] for v in tails)
            assert sum(signed.values()) == 0   # no change to the empty symbol
            for j in pi:
                before = pred[j]
                anchors_before = len(before.intersection(anchors))
                def imbalance(group):
                    return sum(tag[v] for pair in group for v in pair if v in before)
                if j in target:
                    k,d = target[j]
                    formula = (tag[j]*choose(anchors_before,h-s) *
                               prod(imbalance(group) for e,group in enumerate(bins[k]) if e != d))
                else:
                    formula = (choose(anchors_before,h-s-1) *
                               sum(prod(imbalance(group) for group in block) for block in bins))
                    nonzero_anchor |= bool(formula)
                assert signed[j] == formula
                second[j] += signed[j]**2
                max_absolute[j] = max(max_absolute[j],abs(signed[j]))
                checks += 1
            signs_examined += 1
        prediction = {}
        for j in pi:
            before = pred[j]
            anchors_before = len(before.intersection(anchors))
            def split(group):
                return sum((l in before) != (r in before) for l,r in group)
            if j in target:
                k,d = target[j]
                v = choose(anchors_before,h-s)**2 * prod(
                    split(group) for e,group in enumerate(bins[k]) if e != d)
            else:
                v = choose(anchors_before,h-s-1)**2 * sum(
                    prod(split(group) for group in block) for block in bins)
            assert second[j] == signs_examined*v
            prediction[j] = v
        # q^h/16 is the top-cell amplitude; KL <= chi-square. Verify the
        # normalized mean chi-square and its scaling with q and the stage widths.
        for q in (F(1,4*m), F(1,11*m)):
            first = {j:ref_first(m,h,q,rank[j]) for j in pi}
            assert all((1-m*q)*q <= x <= q for x in first.values())
            mean_chi = q**(2*h)/256 * sum(F(second[j],signs_examined)/first[j] for j in pi)
            normalized = sum(F(v)/first[j] for j,v in prediction.items())*q
            assert mean_chi == q**(2*h-1)*normalized/256
            assert sum(prediction.values()) <= normalized <= sum(prediction.values())/(1-m*q)
            assert normalized <= 3*m**(2*(h-s)+1)*w**(s-1)
            # Flipping every paired sign of the first group in each bin
            # reverses every edge weight. The chi-square between opposite
            # signals therefore has four times the numerator, and its
            # denominator stays above half the null's for every endpoint.
            assert all(q**h*max_absolute[j]/16 <= first[j]/2 for j in pi)
    assert nonzero_anchor == (h>s)
    return checks


if __name__ == "__main__":
    for h in (2,3,4):
        runs = [check_scores(h,rounded,w=w) for w in (1,2) for rounded in (False,True)]
        counts = [lower_check(h,s,g,k) for s in range(1,h+1)
                  for g,k in ((1,2),(2,1))]
        print(f"h={h}: {sum(t[0] for t in runs)} Walsh fields, "
              f"{sum(t[1] for t in runs)} truncated prefix checks, "
              f"{sum(t[2] for t in runs)} full-order checks, "
              f"{sum(counts)} signed endpoint identities; exact and rounded laws passed")
