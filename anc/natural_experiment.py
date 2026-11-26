"""Finite pair-hit experiment for the clipped-score natural-window learner.

Run python3 natural_experiment.py [--out DIRECTORY]. Requires NumPy only.
The natural_experiment.csv and natural_experiment_instances.csv outputs contain
population regrets, not elapsed times. Rebuild with the same NumPy release
and seeds to reproduce the Monte Carlo values.
"""
import argparse
import csv
import math
from fractions import Fraction
from pathlib import Path

import numpy as np

from check_natural_window import first_primes


def physical_counts(moduli, length):
    """Counts odd multiples in [2L,4L) for odd integer moduli."""
    high = (4 * length - 1) // moduli
    low = (2 * length - 1) // moduli
    return (high + 1) // 2 - (low + 1) // 2


class Experiment:
    def __init__(self, m=1024, tail_percent=185, amplitude_multiplier=1000,
                 enumerate_cells=True):
        self.m = m
        self.a = m // 2
        self.P = math.ceil(10 * m * math.log(m))
        self.epsilon = 0.5
        anchors = first_primes(self.P, self.a)
        tails = first_primes((tail_percent * self.P + 99) // 100, m - self.a)
        assert anchors[-1] <= 1.2 * self.P and tails[-1] <= 2 * self.P
        self.p = np.array(anchors + tails, dtype=np.int64)
        self.q = 1.0 / self.p
        self.L = 1 << (2000 * (2 * self.P) ** 2 - 1).bit_length()
        assert 4 * self.L < self.P**3
        self.n_scale = m * math.log(m)**2
        self.a_scale = m / math.log(m)**3
        self.proof_amplitude = self.epsilon / (1000 * (2 * self.P)**2)
        self.amplitude = amplitude_multiplier * self.proof_amplitude
        self.lambda_ = self.epsilon * m / self.P**2
        self.band = 100 * self.P**2 * self.lambda_
        self.w = max(np.searchsorted(self.p, self.p + self.band, side="right")
                     - np.arange(m))
        self.reference_top = self.q * np.r_[0, np.cumsum(self.q[:-1])]
        self.reference_score = self.q - self.reference_top
        # Match each adjacent reference hazard difference after the
        # increasing-order prefix; only score differences affect a sort.
        prefix_mass = np.r_[0.0, np.cumsum(self.q[:-1])]
        adjacent_gaps = (self.q[:-1]-self.q[1:])*(1-prefix_mass[:-1])
        self.adjacent_score = self.q[-1] + np.r_[np.cumsum(adjacent_gaps[::-1])[::-1], 0.0]
        np.testing.assert_allclose(-np.diff(self.adjacent_score), adjacent_gaps,
                                   rtol=3e-9, atol=2e-20)
        if enumerate_cells:
            self.ij = np.triu_indices(m, 1)
            i, j = self.ij
            self.reference_pair = self.q[i] * self.q[j]
            physical_pair_count = physical_counts(self.p[i] * self.p[j], self.L)
            exact_single_count = physical_counts(self.p, self.L)
            np.subtract.at(exact_single_count, i, physical_pair_count)
            np.subtract.at(exact_single_count, j, physical_pair_count)
            empty_count = self.L - exact_single_count.sum() - physical_pair_count.sum()
            self.uniform = (empty_count / self.L, exact_single_count / self.L,
                            physical_pair_count / self.L)
            assert min(self.uniform[1]) > 0 and min(self.uniform[2]) > 0
        # For any two adjacent items the exchange comparison is a difference
        # of prefix-conditioned hazards. The anchor perturbation in a hazard
        # has magnitude <=d times the number of earlier tails; the tail
        # perturbation has magnitude <=d times the number of earlier anchors.
        self.anchor_margin = ((self.q[self.a-1] - self.q[self.a]) *
                              (1 - self.q.sum()) - m * self.amplitude)
        assert self.anchor_margin > 0

    def validate_law(self, signs):
        i, j = self.ij
        pair = self.reference_pair.copy()
        cross = (i < self.a) & (j >= self.a)
        pair[cross] += self.amplitude * signs[j[cross]]
        degree = np.bincount(i, weights=pair, minlength=self.m)
        degree += np.bincount(j, weights=pair, minlength=self.m)
        singleton = self.q - degree
        empty = 1 - singleton.sum() - pair.sum()
        # Including exact single-hit cells proves every omitted test is
        # profitable to append before the 4P fallback, on these populations.
        assert singleton.min() * 4 * self.P > 1
        ratios = [empty / self.uniform[0],
                  singleton / self.uniform[1], pair / self.uniform[2]]
        low = min(np.min(r) for r in ratios)
        high = max(np.max(r) for r in ratios)
        assert 1-self.epsilon + 1e-8 < low <= high < 1+self.epsilon-1e-8
        v = np.bincount(j, weights=pair, minlength=self.m)
        expected = self.reference_top + self.a*self.amplitude*signs
        np.testing.assert_allclose(v, expected, rtol=3e-13, atol=1e-19)
        assert v.min() >= 0 and v.sum() < 1
        return v, low, high

    def scores(self, observed_top, adjacent=False):
        deviations = np.clip(observed_top - self.reference_top,
                             -2*self.lambda_, 2*self.lambda_)
        return (self.adjacent_score if adjacent else self.reference_score) - deviations

    def objective(self, order, signs, d=None):
        """Exact population prefix formula up to an order-invariant constant."""
        if d is None:
            d = self.amplitude
        # Accumulate only order-dependent terms, before adding the last item.
        prefix = np.asarray(order)[..., :-1]
        q = self.q[prefix]
        mass = np.cumsum(q, axis=-1)
        squares = np.cumsum(q*q, axis=-1)
        na = np.cumsum(prefix < self.a, axis=-1)
        sign_sum = np.cumsum(signs[prefix], axis=-1)
        return np.sum(-mass + (mass*mass - squares)/2 + d*na*sign_sum, axis=-1)

    def difference_from_ascending(self, order, signs):
        """Subtract matched prefix terms before summation, for tiny signals."""
        ix = np.asarray(order)[..., :-1]
        natural = self.q[:-1]
        delta = np.cumsum(self.q[ix]-natural, axis=-1)
        delta2 = np.cumsum((self.q[ix]-natural)*(self.q[ix]+natural), axis=-1)
        na = np.cumsum(ix < self.a, axis=-1)
        natural_na = np.minimum(np.arange(1,self.m),self.a)
        pert = (na*np.cumsum(signs[ix], axis=-1) -
                natural_na*np.cumsum(signs[:-1]))
        return np.sum(-delta+(delta*(2*np.cumsum(natural)+delta)-delta2)/2 +
                      self.amplitude*pert, axis=-1)

    def oracle(self, signs, return_order=False):
        # Same-sign tail items have the same hazard perturbation after any
        # prefix, so their optimal within-list order is ascending prime.
        # The anchor-first and anchor-order exchanges are justified above.
        plus = np.flatnonzero(signs > 0)
        minus = np.flatnonzero(signs < 0)
        acc = lambda u: np.r_[0.0, np.cumsum(u)]
        q = self.q
        mass = (q[:self.a].sum() + acc(q[plus])[:, None] + acc(q[minus])[None, :])
        squares = ((q[:self.a]**2).sum() + acc(q[plus]**2)[:, None] +
                   acc(q[minus]**2)[None, :])
        npos, nneg = len(plus), len(minus)
        diff = np.arange(npos+1)[:, None] - np.arange(nneg+1)[None, :]
        stage = -mass + (mass*mass-squares)/2 + self.amplitude*self.a*diff
        cost = np.full((npos+2, nneg+2), np.inf)
        cost[npos, nneg] = 0
        for i in range(npos, -1, -1):
            for j in range(nneg, -1, -1):
                if i != npos or j != nneg:
                    cost[i,j] = stage[i,j] + min(cost[i+1,j], cost[i,j+1])
        chosen = list(range(self.a))
        i = j = 0
        while i < npos or j < nneg:
            if cost[i+1,j] <= cost[i,j+1]:
                chosen.append(plus[i])
                i += 1
            else:
                chosen.append(minus[j])
                j += 1
        ranks = np.array(chosen)
        optimum = self.objective(ranks, signs)
        # Independently score the anchor-only prefixes omitted by the DP.
        aq = q[:self.a-1]
        amass = np.cumsum(aq)
        anchor_cost = np.sum(-amass + (amass*amass - np.cumsum(aq*aq))/2)
        np.testing.assert_allclose(optimum, anchor_cost+cost[0,0], atol=2e-11, rtol=0)
        return (optimum, ranks) if return_order else optimum


def write_csv(path, rows):
    with path.open("w", newline="") as output:
        writer = csv.DictWriter(output, fieldnames=rows[0], lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def guarded_orders(exp, train, validation, n_train, n_valid, adjacent=False):
    """Fit on the training counters, then validate actual-cost upper bound."""
    order = np.argsort(-exp.scores(train/n_train, adjacent), axis=1, kind="stable")
    ascending = np.arange(exp.m)
    changes = np.argsort(order, axis=1) - ascending
    # If pair ij exchanges order, the surrogate upper-bounds the true cost
    # at its new rank. Each validation word only needs its greatest hit index.
    sur = np.sum((exp.q - validation/n_valid) * changes, axis=1)
    variance = np.sum(changes**2 * ((1 + exp.epsilon) *
                      (exp.reference_top + ascending / exp.L)), axis=1)
    absolute_bound = 2 * np.max(np.abs(changes), axis=1)
    log_term = math.log(20)  # one-sided 95% for one held-out proposal
    padding = (np.sqrt(2 * variance * log_term / n_valid) +
               2 * absolute_bound * log_term / (3*n_valid) +
               np.abs(changes).sum(axis=1)/exp.L)
    accepted = (sur + padding) < 0
    order[~accepted] = ascending
    return order, accepted


def run(output):
    exp = Experiment()
    rng = np.random.default_rng(20261126)
    gate_rng = np.random.default_rng(20261127)
    order0 = np.arange(exp.m)
    repeats = 128
    sample_sizes = [round(exp.n_scale), 2**20, 2**22, 2**24, 2**26, 2**28,
                    2**30, 2**32, 2**34, 2**36, 2**38]
    summary = []
    populations = []
    outcomes = {n: [] for n in sample_sizes}
    raw_outcomes = {n: [] for n in sample_sizes}
    safe_outcomes = {n: [] for n in sample_sizes}
    fractions_accepted = {n: [] for n in sample_sizes}
    adjacent_outcomes = {n: [] for n in sample_sizes}
    adjacent_cost = {n: [] for n in sample_sizes}
    adjacent_worse = {n: [] for n in sample_sizes}
    adjacent_safe = {n: [] for n in sample_sizes}
    for population in range(4):
        tail = rng.permutation(np.repeat([-1, 1], exp.a//2))
        signs = np.r_[np.zeros(exp.a, dtype=int), tail]
        v, low, high = exp.validate_law(signs)
        optimum, oracle_order = exp.oracle(signs, return_order=True)
        blind = exp.objective(order0, signs) - optimum
        assert blind > 0
        infinite_order = np.argsort(-exp.scores(v), kind="stable")
        floor = exp.objective(infinite_order, signs) - optimum
        assert -1e-11 <= floor <= blind
        adjacent_pop = np.argsort(-exp.scores(v, True), kind="stable")
        stable_blind = -exp.difference_from_ascending(oracle_order, signs)
        adjacent_floor = stable_blind + exp.difference_from_ascending(adjacent_pop, signs)
        # For these four populations the two orders differ by disjoint swaps.
        # Confirm their very small costs using exact fractions of a probe.
        swaps = np.flatnonzero(adjacent_pop != oracle_order).reshape(-1, 2)
        swap_excess = Fraction(0)
        d_exact = Fraction(1, 8 * exp.P**2)
        assert float(d_exact) == exp.amplitude
        for left, right in swaps:
            i, j = oracle_order[left], oracle_order[right]
            assert right == left + 1 and (adjacent_pop[left:right+1] == [j,i]).all()
            prefix = oracle_order[:left]
            remaining = 1 - sum(Fraction(1, int(exp.p[x])) for x in prefix)
            gap = Fraction(1, int(exp.p[i])) - Fraction(1, int(exp.p[j]))
            swap_excess += gap * remaining - exp.a * d_exact * int(signs[i] - signs[j])
        assert abs(float(swap_excess) - adjacent_floor) < 1e-19
        # Sufficiency of max-hit-index means one can sample the observed
        # counters without generating or pretending to generate N integers.
        probs = np.r_[v, 1-v.sum()]
        populations.append(dict(
            population=population, m=exp.m, P=exp.P, L=exp.L,
            first_anchor=exp.p[0], last_anchor=exp.p[exp.a-1],
            first_tail=exp.p[exp.a], last_tail=exp.p[-1], allowed_window=exp.w,
            d=exp.amplitude, proof_d=exp.proof_amplitude, min_ratio=low, max_ratio=high,
            total_pair_mass=v.sum(), anchor_hazard_margin=exp.anchor_margin,
            n_scale=exp.n_scale, a_scale=exp.a_scale, blind_regret=blind,
            population_score_regret=floor, population_score_fraction=floor/blind,
            adjacent_population_regret=adjacent_floor,
            adjacent_population_fraction=adjacent_floor/blind,
            adjacent_is_oracle=np.array_equal(adjacent_pop, oracle_order),
            adjacent_disjoint_swaps=len(swaps), adjacent_rational_swap_excess=float(swap_excess),
            tail_signs="".join("+" if x > 0 else "-" for x in tail)))
        for n in sample_sizes:
            counts = rng.multinomial(n, probs, size=repeats)[:, :-1]
            ranks = np.argsort(-exp.scores(counts/n), axis=1, kind="stable")
            assert np.max(np.abs(ranks-order0)) <= exp.w
            regret = exp.objective(ranks, signs) - optimum
            assert regret.min() > -1e-11
            outcomes[n].extend(regret / blind)
            raw_outcomes[n].extend(regret)
            new_order = np.argsort(-exp.scores(counts/n, True), axis=1, kind="stable")
            assert np.max(np.abs(new_order-order0)) <= exp.w
            new_delta = exp.difference_from_ascending(new_order, signs)
            new_regret = stable_blind + new_delta
            assert new_regret.min() >= -1e-18
            adjacent_outcomes[n].extend(new_regret/blind)
            adjacent_cost[n].extend(new_regret)
            adjacent_worse[n].extend(new_delta > exp.difference_from_ascending(ranks, signs) + 1e-18)
            fit_n = n//2
            train = gate_rng.multinomial(fit_n,probs,size=repeats)[:, :-1]
            validation = gate_rng.multinomial(n-fit_n,probs,size=repeats)[:, :-1]
            safe_order, passed = guarded_orders(exp, train, validation, fit_n, n-fit_n)
            assert np.max(np.abs(safe_order-order0)) <= exp.w
            safe_outcomes[n].extend((exp.objective(safe_order, signs)-optimum)/blind)
            fractions_accepted[n].extend(passed)
            new_safe, _ = guarded_orders(exp, train, validation, fit_n, n-fit_n, True)
            adjacent_safe[n].extend((stable_blind+exp.difference_from_ascending(new_safe,signs))/blind)
    for n in sample_sizes:
        x = np.asarray(outcomes[n])
        safe = np.asarray(safe_outcomes[n])
        summary.append(dict(N=n, N_over_n_scale=n/exp.n_scale,
                            expected_two_hit_words=n*np.mean([v["total_pair_mass"] for v in populations]),
                            repetitions=len(x),
                            mean_regret=np.mean(raw_outcomes[n]),
                            mean_fraction=x.mean(), median_fraction=np.median(x),
                            q95_fraction=np.quantile(x,0.95),
                            fraction_beating_ascending=np.mean(x<1),
                            fraction_below_one_tenth=np.mean(x<0.1),
                            guarded_mean_fraction=safe.mean(),
                            guarded_q95_fraction=np.quantile(safe,0.95),
                            guarded_acceptance=np.mean(fractions_accepted[n]),
                            guarded_fraction_worse_than_ascending=np.mean(safe>1+1e-9),
                            adjacent_mean_regret=np.mean(adjacent_cost[n]),
                            adjacent_mean_fraction=np.mean(adjacent_outcomes[n]),
                            adjacent_q95_fraction=np.quantile(adjacent_outcomes[n],.95),
                            adjacent_paired_fraction_worse=np.mean(adjacent_worse[n]),
                            adjacent_guarded_mean_fraction=np.mean(adjacent_safe[n])))
    output.mkdir(parents=True, exist_ok=True)
    write_csv(output/"natural_experiment.csv", summary)
    write_csv(output/"natural_experiment_instances.csv", populations)
    print("m=%d, P=%d, w=%d, %d laws x %d training draws per N" %
          (exp.m, exp.P, exp.w, len(populations), repeats))
    for row in summary:
        print("N=%11d  mean/blind=%.4g  q95/blind=%.4g  guarded/blind=%.4g" %
              (row["N"], row["mean_fraction"], row["q95_fraction"],
               row["guarded_mean_fraction"]))


def run_literal(output):
    exp = Experiment(m=8192, tail_percent=180, amplitude_multiplier=1,
                     enumerate_cells=False)
    rng = np.random.default_rng(20261128)
    m, a, d, q, L = exp.m, exp.a, exp.amplitude, exp.q, exp.L
    ascending = np.arange(m)
    two_sign_gap = 2*a*d
    assert 2/exp.p[a]**2 < two_sign_gap < 4*(1-q.sum())/exp.p[-1]**2
    twins = a + np.flatnonzero(np.diff(exp.p[a:]) == 2)
    assert np.min(np.diff(twins)) >= 2
    # Every physical containment count has absolute error <=1/L.
    # Invert the pair/singleton/empty counts and bound all signs at once.
    pairs = m*(m-1)//2
    u2 = 1/(2*exp.P)**2 - 1/L
    u1 = q[-1]*(1-q.sum()) - m/L
    u0 = 1-q.sum()-m/L
    density_deviation = max((d+1/L)/u2, m*(d+1/L)/u1,
                            (pairs*d+(m+pairs)/L)/u0)
    assert density_deviation < exp.epsilon and (u1-m*(d+1/L))*4*exp.P > 1
    sizes = [round(exp.n_scale), 2**32, 2**40, 2**48, 2**52, 2**54,
             2**56, 2**58, 2**60]
    outcomes = {n: [] for n in sizes}
    raw = {n: [] for n in sizes}
    adjacent_outcomes = {n: [] for n in sizes}
    adjacent_cost = {n: [] for n in sizes}
    adjacent_worse = {n: [] for n in sizes}
    instances = []
    reps = 32
    for population in range(4):
        tail = rng.permutation(np.repeat([-1,1],a//2))
        signs = np.r_[np.zeros(a,dtype=int),tail]
        wrong = twins[(signs[twins]>0) & (signs[twins+1]<0)]
        prefix_factor = 1-np.r_[0.,np.cumsum(q[:-1])]
        blind = np.sum(two_sign_gap-(q[wrong]-q[wrong+1])*prefix_factor[wrong])
        best = ascending.copy()
        best[wrong],best[wrong+1] = wrong+1,wrong
        assert np.isclose(exp.difference_from_ascending(best,signs),-blind,
                          rtol=1e-9,atol=1e-21)
        v = exp.reference_top+a*d*signs
        probs = np.r_[v,1-v.sum()]
        pop_order = np.argsort(-exp.scores(v),kind="stable")
        floor = 1+exp.difference_from_ascending(pop_order,signs)/blind
        assert abs(floor)<1e-8
        adjacent_pop = np.argsort(-exp.scores(v,True),kind="stable")
        adjacent_floor = blind+exp.difference_from_ascending(adjacent_pop,signs)
        instances.append(dict(population=population,m=m,P=exp.P,L=L,
                              first_anchor=exp.p[0],last_anchor=exp.p[a-1],
                              first_tail=exp.p[a],last_tail=exp.p[-1],
                              w=exp.w,d=d,upper_density_deviation=density_deviation,
                              twins=len(twins),inverted_twins=len(wrong),
                              blind_regret=blind,true_score_achieves_oracle=np.array_equal(pop_order,best),
                              adjacent_is_oracle=np.array_equal(adjacent_pop,best),
                              adjacent_population_regret=0.0 if np.array_equal(adjacent_pop,best) else adjacent_floor,
                              adjacent_population_fraction=0.0 if np.array_equal(adjacent_pop,best) else adjacent_floor/blind,
                              pair_mass=v.sum(),n_scale=exp.n_scale,a_scale=exp.a_scale,
                              sign_mask=hex(int("".join("1" if z>0 else "0" for z in tail),2))))
        for n in sizes:
            counts = rng.multinomial(n,probs,size=reps)[:, :-1]
            order = np.argsort(-exp.scores(counts/n),axis=1,kind="stable")
            assert np.max(np.abs(order-ascending))<=exp.w
            regret = blind+exp.difference_from_ascending(order,signs)
            assert regret.min() >= -1e-19
            outcomes[n].extend(regret/blind)
            raw[n].extend(regret)
            new_order = np.argsort(-exp.scores(counts/n,True),axis=1,kind="stable")
            assert np.max(np.abs(new_order-ascending))<=exp.w
            new_regret = blind+exp.difference_from_ascending(new_order,signs)
            assert new_regret.min() >= -1e-19
            adjacent_outcomes[n].extend(new_regret/blind)
            adjacent_cost[n].extend(new_regret)
            adjacent_worse[n].extend(new_regret > regret + 1e-18)
    summary = []
    for n in sizes:
        x = np.asarray(outcomes[n])
        summary.append(dict(N=n,N_over_n_scale=n/exp.n_scale,
                            expected_two_hit_words=n*exp.reference_top.sum(),
                            repetitions=len(x),mean_regret=np.mean(raw[n]),
                            mean_fraction=np.mean(x),median_fraction=np.median(x),
                            q95_fraction=np.quantile(x,.95),
                            fraction_beating_ascending=np.mean(x<1),
                            adjacent_mean_regret=np.mean(adjacent_cost[n]),
                            adjacent_mean_fraction=np.mean(adjacent_outcomes[n]),
                            adjacent_q95_fraction=np.quantile(adjacent_outcomes[n],.95),
                            adjacent_paired_fraction_worse=np.mean(adjacent_worse[n])))
    write_csv(output/"natural_experiment_literal.csv",summary)
    write_csv(output/"natural_experiment_literal_instances.csv",instances)
    print("Literal proof amplitude: m=%d, %d disjoint twin pairs." % (m,len(twins)))
    for row in summary:
        print("N=%19d  mean/blind=%.4g  q95/blind=%.4g" %
              (row["N"],row["mean_fraction"],row["q95_fraction"]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=Path(__file__).resolve().parent)
    destination = parser.parse_args().out
    run(destination)
    run_literal(destination)
