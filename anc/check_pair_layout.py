"""Exact finite regressions for the bucketed pair layout and rank repair."""

from collections import Counter
from fractions import Fraction
from itertools import accumulate, combinations, permutations, product


def ranks(order):
    result = [0] * len(order)
    for rank, index in enumerate(order, 1):
        result[index] = rank
    return result


def pair_cost(edges, x):
    return sum(a*max(x[i]-x[j], 0) for i,j,a in edges)


def rank_repair(scores, edges, bucket_sizes):
    n = len(scores)
    sigma = sorted(range(n), key=lambda i: (-scores[i], i))
    r0 = ranks(sigma)
    incident = Counter()
    for i,j,v in edges:
        incident[i] += abs(v)
        incident[j] += abs(v)
    D = max(incident.values(), default=0)
    ends = list(accumulate(bucket_sizes))
    starts = [1] + [x+1 for x in ends[:-1]]
    intervals = list(zip(starts, ends))
    reps = [(a+b)//2 for a,b in intervals]
    delta = max(bucket_sizes)
    phi = [0, 0] + list(accumulate(scores[i] for i in sigma[:-1]))
    H = [[0]+[scores[i]*(t-r0[i])-phi[t]+phi[r0[i]] for t in range(1,n+1)]
         for i in range(n)]
    coordinates = [[max(a, min(b, r0[i])) for a,b in intervals] for i in range(n)]
    minima = [[min(H[i][a:b+1]) for a,b in intervals] for i in range(n)]
    assert all(H[i][t] == minima[i][j] for i,row in enumerate(coordinates)
               for j,t in enumerate(row))
    base = sum(x*y for x,y in zip(scores, r0))
    true_cost = lambda r: sum(x*y for x,y in zip(scores,r)) + pair_cost(edges, r)
    def energy(labels):
        return (sum(minima[i][b] for i,b in enumerate(labels))
                + pair_cost(edges,[reps[b] for b in labels]))
    def potential(t):
        return sum(H[i][x] for i,x in enumerate(t)) + pair_cost(edges,t)
    for order in permutations(range(n)):
        r = ranks(order)
        labels = [next(b for b,end in enumerate(ends) if x <= end) for x in r]
        assert sum(H[i][x] for i,x in enumerate(r)) == true_cost(r)-pair_cost(edges,r)-base
        assert energy(labels) <= true_cost(r)-base+D*n*delta
    visited, exchanges, nonadjacent, strictly_one_sided = 0, 0, 0, 0
    for labels in product(range(len(ends)), repeat=n):
        t = [coordinates[i][b] for i,b in enumerate(labels)]
        initial_energy = energy(labels)
        assert potential(t) <= initial_energy+D*n*delta
        zeta = max(abs(sum(label <= b for label in labels)-end) for b,end in enumerate(ends))
        original_coordinates = sorted(t)
        while True:
            order = sorted(range(n), key=lambda i:(t[i], r0[i]))
            inversions = [(i,j) for i,j in combinations(order,2) if r0[i] > r0[j]]
            fix = next(((i,j) for i,j in reversed(inversions) if scores[j]-scores[i] > 2*D), None)
            if fix is None:
                break
            before = potential(t)
            i,j = fix
            nonadjacent += abs(order.index(i)-order.index(j)) > 1
            assert t[i] < t[j]
            t[i],t[j] = t[j],t[i]
            after_order = sorted(range(n), key=lambda i:(t[i], r0[i]))
            assert sum(r0[x]>r0[y] for x,y in combinations(after_order,2)) < len(inversions)
            assert potential(t) < before
            exchanges += 1
        assert sorted(t) == original_coordinates
        r = ranks(order)
        for i,x in enumerate(r):
            assert abs(x-t[i]) <= delta+zeta
            assert abs(scores[i]-scores[sigma[x-1]]) <= 2*D
            inc = H[i][x]-H[i][t[i]]
            linear = (x-t[i])*(scores[i]-scores[sigma[x-1]])
            assert inc <= linear <= 2*D*(delta+zeta)
            strictly_one_sided += inc < -2*D*(delta+zeta)
        assert true_cost(r) <= base+initial_energy+D*n*(4*delta+3*zeta)
        assert all(scores[j]-scores[i] <= 2*D for i,j in combinations(order,2))
        visited += 1
    return visited, exchanges, nonadjacent, strictly_one_sided


def tile_profiles(tile_count, width=8, radius=3):
    """Seven independent unit errors align at one cut for every menu length."""
    n = tile_count*width
    center = tile_count//2
    begin = center*width
    cut = begin+width//2
    exact = list(range(n))  # source vertex -> physical position, zero-based
    for shift in range(1,radius+1):
        i,j = begin+shift-1, (center+shift)*width
        exact[i],exact[j] = exact[j],exact[i]
    assert sorted(exact) == list(range(n))
    assigned = exact.copy()
    for tile in range(center-radius, center+radius+1):
        member = next(i for i in range(width*tile,width*(tile+1)) if exact[i] < cut)
        assigned[member] = cut
    for i in range(n):
        assert abs(i//width-exact[i]//width) <= radius
        assert abs(i//width-assigned[i]//width) <= radius
    largest = 0
    for boundary in range(1,n+1):
        errors = [
            sum(int(assigned[i]<boundary)-int(exact[i]<boundary)
                for i in range(tile*width,(tile+1)*width))
            for tile in range(tile_count)]
        assert max(map(abs,errors)) <= 1
        for tile,e in enumerate(errors):
            first = max(0, tile-radius)*width
            end = min(tile_count, tile+radius+1)*width
            if not first < boundary < end:
                assert e == 0
        discrepancy = sum(x<boundary for x in assigned)-boundary
        assert discrepancy == sum(errors)
        assert abs(discrepancy) <= 2*radius+1
        largest = max(largest, abs(discrepancy))
        if boundary == cut:
            assert discrepancy == -(2*radius+1)
    return largest


def row_multiscale():
    # Mixed orientations and signs occur together in a row. Rank knots are
    # the dyadic boundaries; use exact rational non-knots to check suprema.
    lo, length, depth = 4, 12, 3
    cols = [Fraction(x,2) for x in (8,13,17,24,32)]  # includes right endpoint
    directions = [1,-1,-1,1,1]
    weights = [2,-4,1,-3,5]
    def quantize(u,level):
        step = Fraction(length,2**level)
        return lo+step*min(2**level-1,(u-lo)//step)
    def kernel(j,t,u):
        return weights[j]*max(directions[j]*(t-u),0)
    N = len(cols)
    target = [Fraction(x,4) for x in range(0,85)]
    for t in target:
        exact = sum(kernel(j,t,cols[j]) for j in range(N))
        telescoped = sum(kernel(j,t,lo) for j in range(N))
        for level in range(1,depth+1):
            incs = [kernel(j,t,quantize(u,level))-kernel(j,t,quantize(u,level-1))
                    for j,u in enumerate(cols)]
            # Enumerate all length-two samples with replacement at this level.
            means = [Fraction(N,2)*(incs[i]+incs[j]) for i,j in product(range(N),repeat=2)]
            assert sum(means)/len(means) == sum(incs)
            telescoped += sum(incs)
        assert telescoped == sum(kernel(j,t,quantize(cols[j],depth)) for j in range(N))
        assert abs(exact-telescoped) <= sum(map(abs,weights))*Fraction(length,2**depth)
    for level in range(1,depth+1):
        knots = sorted({target[0],target[-1],*(quantize(u,k) for u in cols for k in (level-1,level))})
        for sample in product(range(N),repeat=2):
            def error(t):
                inc = [kernel(j,t,quantize(u,level))-kernel(j,t,quantize(u,level-1))
                       for j,u in enumerate(cols)]
                return Fraction(N,2)*sum(inc[j] for j in sample)-sum(inc)
            knot_sup = max(abs(error(t)) for t in knots)
            assert all(abs(error(t)) <= knot_sup for t in target)
    return len(target), 3*N*N


def check_profile_chain():
    """Exhaustive five-tile row-envelope assignment and two-state chain DP."""
    tiles, width = 5, 2
    n = tiles*width
    vertices = [range(t*width,(t+1)*width) for t in range(tiles)]
    coords = [2*t+1 for t in range(tiles)]
    home = [i//width for i in range(n)]
    # Each vertex can stay home or move to a neighbor, including both end tiles.
    alternatives = []
    for i,t in enumerate(home):
        direction = 1 if i%2 == 0 else -1
        neighbor = t + direction
        if not 0 <= neighbor < tiles:
            neighbor = t - direction
        alternatives.append((t,neighbor))
    edges = []
    kernel = {}
    for i,j in combinations(range(n),2):
        if abs(home[i]-home[j]) > 1:
            continue
        a = (3*i+5*j+2)%7-3
        if a:
            left,right = (i,j) if (i+j)%3 else (j,i)
            edges.append((left,right,a))
            kernel[left,right],kernel[right,left] = (1,a),(-1,a)
    unary = [{b: (i+1)*(b-home[i])*(-1)**i for b in alternatives[i]} for i in range(n)]
    options = [list(product(*(alternatives[i] for i in tile))) for tile in vertices]
    # One bit from each source specifies a guessed assignment. Feasibility
    # below allows the actual source assignment to differ from this guess.
    guesses = [[opts[0], opts[2] if t%2 == 0 else opts[1]] for t,opts in enumerate(options)]
    def local_field(i,t,b,assignment):
        value = 0
        for j,dest in zip(vertices[t],assignment):
            orient,weight = kernel.get((i,j),(1,0))
            value += weight*max(orient*(coords[b]-coords[dest]),0)
        return value
    def prefix_count(assignment,cut):
        return sum(label <= cut for label in assignment)
    # Double the objective so every signed comparison stays integral.
    fields, slack, allowed = {}, {}, {}
    variance_checks = 0
    for t,opts in enumerate(options):
        for p,guess in enumerate(guesses[t]):
            for i in range(n):
                for b in alternatives[i]:
                    fields[t,p,i,b] = local_field(i,t,b,guess)
            for choice in opts:
                allowed[t,p,choice] = all(abs(prefix_count(choice,c)-prefix_count(guess,c)) <= 1
                                          for c in range(tiles))
                slack[t,p,choice] = sum(max(abs(local_field(i,t,b,choice)-fields[t,p,i,b])
                                              for b in alternatives[i]) for i in range(n))
        # Independent categorical rounding in a source tile. Directly check
        # the complete second moment, including bias from its guessed table.
        probs = [Fraction(1,3),Fraction(2,3)]
        distribution = [((x,y), (probs[0] if x else 1-probs[0])*
                         (probs[1] if y else 1-probs[1])) for x,y in product(range(2),repeat=2)]
        for i in range(n):
            for b in alternatives[i]:
                evaluators = [lambda a,i=i,b=b:local_field(i,t,b,a),
                              lambda a,b=b:prefix_count(a,b)]
                for evaluate in evaluators:
                    values = {}
                    for bits,prob in distribution:
                        choice = tuple(alternatives[j][d] for j,d in zip(vertices[t],bits))
                        values[bits] = evaluate(choice)
                    mean = sum(prob*values[bits] for bits,prob in distribution)
                    diffs = [values[1,0]-values[0,0], values[0,1]-values[0,0]]
                    variance = sum(q*(1-q)*v*v for q,v in zip(probs,diffs))
                    center = evaluate(guesses[t][1])
                    assert sum(prob*(values[bits]-center)**2 for bits,prob in distribution) == (
                        variance+(mean-center)**2)
                    variance_checks += 1
    def local_key(t, prev, p, nex, choice):
        row = 2*sum(unary[i][b] for i,b in zip(vertices[t],choice))
        for source,profile in ((t-1,prev),(t,p),(t+1,nex)):
            if profile is not None:
                row += sum(fields[source,profile,i,b] for i,b in zip(vertices[t],choice))
        return row, slack[t,p,choice]
    def feasible_cut(t,p,nex):
        # Sources strictly before t cannot cross its right boundary.
        # Sources strictly beyond t+1 cannot reach it.
        count = prefix_count(guesses[t][p],t)-width
        if nex is not None:
            count += prefix_count(guesses[t+1][nex],t)
        return count == 0
    factors = {}
    for t in range(tiles):
        for prev,p,nex in product((0,1) if t else (None,), (0,1),
                                  (0,1) if t+1 < tiles else (None,)):
            factors[t,prev,p,nex] = min(
                (sum(local_key(t,prev,p,nex,choice)), choice) for choice in options[t]
                if allowed[t,p,choice])
    exact = {}
    for choices in product(*options):
        flat = [b for choice in choices for b in choice]
        exact[choices] = 2*(sum(unary[i][b] for i,b in enumerate(flat))
                            + pair_cost(edges,[coords[b] for b in flat]))
    envelope_checks, valid_profiles = 0, 0
    exhaustive_best = None
    for profile in product(range(2),repeat=tiles):
        padded = (None,*profile,None)
        feasible = all(feasible_cut(t,profile[t],padded[t+2]) for t in range(tiles))
        assert feasible == all(sum(prefix_count(guesses[t][profile[t]],c) for t in range(tiles))
                               == width*(c+1) for c in range(tiles))
        local = [[local_key(t,*padded[t:t+3],c) for c in options[t]] for t in range(tiles)]
        best_assignment = None
        for indices in product(range(4),repeat=tiles):
            choices = tuple(options[t][idx] for t,idx in enumerate(indices))
            prediction = sum(local[t][idx][0] for t,idx in enumerate(indices))
            allowance = sum(local[t][idx][1] for t,idx in enumerate(indices))
            assert abs(prediction-exact[choices]) <= allowance
            envelope_checks += 1
            if feasible and all(allowed[t,profile[t],choices[t]] for t in range(tiles)):
                value = prediction+allowance
                best_assignment = value if best_assignment is None else min(best_assignment,value)
        if feasible:
            assert best_assignment == sum(factors[(t,)+padded[t:t+3]][0] for t in range(tiles))
            valid_profiles += 1
            exhaustive_best = best_assignment if exhaustive_best is None else min(exhaustive_best,best_assignment)
    # At depth t only profiles from the last two tiles enter a later factor.
    dp = {(None,p):(0,()) for p in (0,1)}
    for t in range(tiles):
        advanced = {}
        for (prev,p),(value,choices) in dp.items():
            for nex in (0,1) if t+1 < tiles else (None,):
                if feasible_cut(t,p,nex):
                    key = (p,nex)
                    local_value, local_choice = factors[t,prev,p,nex]
                    candidate = (value+local_value, (*choices,local_choice))
                    advanced[key] = min(advanced.get(key,candidate),candidate)
        dp = advanced
    value, choices = min(dp.values())
    assert exact[choices] <= value == exhaustive_best
    for cut in range(tiles):
        count = sum(prefix_count(choice,cut) for choice in choices)
        assert abs(count-width*(cut+1)) <= 2
    assert 1 < valid_profiles < 2**tiles
    return envelope_checks, valid_profiles, exhaustive_best, exact[choices], variance_checks


if __name__ == '__main__':
    scores_and_edges = [
        ([37,4,38,4,-27,-28], [(0,1,2),(0,3,-1),(1,4,-2),(1,5,1),(3,2,1),(4,5,-1)]),
        ([10**7,10**7,-10**5,18,18,-92], [(2,0,2),(0,2,-1),(4,2,-2),(1,5,3),(5,3,-2)]),
        ([200,200,-300,100,100,-300], [])]
    totals = [0]*4
    for scores, edges in scores_and_edges:
        for buckets in ([2,2,2],[2,1,3],[1,3,2]):
            counts = rank_repair(scores, edges, buckets)
            totals = [x+y for x,y in zip(totals,counts)]
    assert all(totals)
    print(f'{totals[0]} bucket assignments, {totals[1]} repairs '
          f'({totals[2]} nonadjacent), {totals[3]} one-sided losses below the negative bound.')
    capacities = [tile_profiles(k) for k in (9,21,45)]
    print(f'Tiles 9, 21, 45 all attain the same sharp cumulative error {capacities[0]}.')
    locations, samples = row_multiscale()
    print(f'{locations} exact multiscale telescoping checks and {samples} mixed-sign knot extrema.')
    envelopes, feasible, best, realized, variances = check_profile_chain()
    print(f'{envelopes} row-envelope checks. Five-tile DP and exhaustive optimization '
          f'agree at doubled envelope {best} (realized objective {realized}), '
          f'with {feasible} admissible profiles. '
          f'{variances} independent-rounding second moments checked.')
