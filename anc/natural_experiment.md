# Finite learning experiment with natural prime hit rates

The clipped-score learner eventually recovers most of the available ordering gain on the constructed workloads. Its finite-sample behavior is nonmonotone. With 4,194,304 word-equivalent observations, it incurred **42.76 times the regret of simply testing primes in increasing order**. By 1,073,741,824 observations, that ratio had fallen to 0.403. An independently validated fallback to increasing order avoids the intermediate loss, at a cost in statistical efficiency.

## Arithmetic instance and population optimum

There are \(m=1024\) tests, \(h=2\), \(P=\lceil10m\log m\rceil=70{,}979\), \(\epsilon=1/2\), and \(B=4P\). Take the first 512 primes at or above \(P\) as anchors and the first 512 primes at or above \(1.85P\) as tail items. Their ranges are 70,979–76,667 and 131,317–137,273. The uniform reference consists of \(L=2^{46}\) odd integers in \([2L,4L)\). Every word has at most two hits.

Give each pair its reference mass \(q_iq_j\), where \(q_i=1/p_i\). For every anchor–tail pair add \(d\theta_j\) to the pair and empty cells and subtract it from both singleton cells, with \(d=1/(8P^2)\) and hidden tail sign \(\theta_j\in\{-1,1\}\). The exact singleton marginal stays \(q_i\). Lift each cell uniformly over its physical words. Four seeded random balanced sign vectors define four populations. Direct counts of odd multiples determine the physical uniform cell sizes. The density ratios of the four laws range from 0.73880 to 1.26120, safely inside the required interval \([0.5,1.5]\).

The perturbation is **1,000 times the specific conservative amplitude in the asymptotic lower-bound proof**. At that proof amplitude, the smallest possible tail-prime gap already dominates the opposing sign effects here. Indeed the natural pairwise hazard gap is at least \(2(1-\sum q_i)/(2P)^2\), while the perturbation between opposite-sign tail hazards is at most \(1024d_{\rm proof}\). Increasing order is then optimal at this size. The reported experiment instead uses a larger admissible signal to produce a genuine ordering problem.

All singleton cells have probability above \(1/B\), so appending any omitted prime improves a plan. Each anchor dominates each tail after every common prefix, since the baseline hazard gap exceeds the maximum tilt \(md\) by at least \(5.34\cdot10^{-6}\). Among anchors and separately among tails of each common sign, the tilt cancels and increasing prime order dominates. The unrestricted population optimum is therefore an increasing anchor block followed by an optimal merge of the two increasing sign lists. A dynamic program evaluates all 66,049 merge states using exact population prefix probabilities, in double precision. An additional test on an eight-prime instance matched the oracle against all 40,320 orders for each of six sign allocations.

## What the learner sees

Every word with two menu factors records its larger prime index \(j\), and other words increment no counter. The known reference mass of index \(j\) is \(v_j^0=q_j\sum_{i<j}q_i\). With \(\lambda=\epsilon m/P^2\) and empirical frequency \(\widehat v_j\), the learner sorts by decreasing score \(q_j-v_j^0-\operatorname{clip}(\widehat v_j-v_j^0,-2\lambda,2\lambda)\), breaking ties by prime order. The theorem's finite rank window is 512 and every reported output satisfied it. Signs and population coefficients are available only for generating and evaluating the experiment.

The histogram, including its no-counter category, is sampled directly from the multinomial law induced by \(N\) independent complete words. \(N\) is the **equivalent number of original words**. This compression reproduces the learners' input distributions; the program does not generate that many integers or measure input-processing time. Pair hits occur with probability \(5.7775\cdot10^{-5}\). Each row pools 128 fresh training draws on each of the four fixed populations. Ratios divide each draw's population excess by increasing-order excess for the *same* population.

| Equivalent words \(N\) | Expected two-hit words | Mean regret / increasing | 95th percentile | Mean ratio with validation |
|---:|---:|---:|---:|---:|
| 49,198 | 2.84 | 1.763 | 2.928 | 1.000 |
| 4,194,304 | 242 | 42.757 | 48.587 | 1.000 |
| 268,435,456 | 15,509 | 1.544 | 1.696 | 1.000 |
| 1,073,741,824 | 62,036 | 0.403 | 0.444 | 0.995 |
| 4,294,967,296 | 248,143 | 0.105 | 0.116 | 0.205 |
| 17,179,869,184 | 992,571 | 0.0306 | 0.0341 | 0.0551 |
| 274,877,906,944 | 15,881,135 | 0.00776 | 0.00846 | 0.00921 |

Increasing-order excess was only \(6.016\cdot10^{-5}\) to \(6.261\cdot10^{-5}\) expected probes per word. The population-score learner, given noiseless frequencies, retained 0.649%–0.672% of that excess because its ordering objective is linearized. At \(N=\operatorname{round}(m\log^2m)=49{,}198\), fewer than three pair hits are expected. As intermediate samples reveal sparse categories, noisy empirical scores can displace many nearly equivalent primes. The theorem's accuracy scale here is \(m/\log^3m=3.075\) probes, far larger than the available gain on these instances. The experiment measures finite constants at a fixed size and does not establish a growth rate.

## A second instance at the lower-bound proof's literal amplitude

We also used \(m=8192\), \(P=738{,}175\), \(L=2^{52}\), 4096 anchors starting at \(P\), and 4096 tails starting at \(1.8P\). We use the literal \(d=\epsilon/[1000(2P)^2]\), with no strengthening of the signal. Bounding containment rounding by \(1/L\) and inverting the pair, singleton and empty cells certifies a pointwise density deviation below 0.000985 on every law. The signed pair perturbations still preserve all individual hit marginals.

Only twin primes are close enough to invert here. Let \(s=4096d\) and \(K(S)=1-\sum_{i\in S}q_i\). After all anchors, interchanging opposite-sign tail items trades \(2s\) against their natural hazard gap \(|q_i-q_j|K(S)\). The actual menu satisfies

$$
\frac{2}{p_{\rm first\,tail}^2}<2s<
\frac{4(1-\sum_iq_i)}{p_{\rm last\,tail}^2}.
$$

Hence every tail pair with gap at least four must retain its natural order. In a twin pair, a positive-sign lower prime followed by a negative-sign higher prime must be reversed. There are 418 disjoint twin pairs, of which 89–118 need reversal across the four hidden sign populations. This determines a global optimum, since anchors are again forced in increasing order before the tail and all singleton cells justify full screening. Matched prefix differences allow evaluation of very small excesses without subtracting two nearly equal total costs.

| Equivalent words \(N\) | Mean excess in probes | Mean regret / increasing | 95th percentile of ratio |
|---:|---:|---:|---:|
| 665,162 | \(2.35\cdot10^{-4}\) | \(2.94\cdot10^6\) | \(4.29\cdot10^6\) |
| \(2^{52}\) | \(1.32\cdot10^{-10}\) | 1.644 | 1.989 |
| \(2^{54}\) | \(3.83\cdot10^{-11}\) | 0.475 | 0.587 |
| \(2^{58}\) | \(6.97\cdot10^{-12}\) | 0.0860 | 0.141 |
| \(2^{60}\) | \(2.87\cdot10^{-13}\) | 0.00351 | 0.0164 |

Each row averages 32 independent histogram simulations on each of four populations. Increasing-order excess is only \(7.12\cdot10^{-11}\) to \(9.44\cdot10^{-11}\) probes per query. At \(N=\operatorname{round}(m\log^2m)\) the expected two-hit count is 23.27. All four noiseless score orders equal their exact population optima. At this finite size the theorem's nominal accuracy scale is 11.20 probes, making accuracy measured as a fraction of the tiny available gain a much stronger target. The large sample sizes are counters generated by a multinomial sampler. [Second learning curve](natural_experiment_literal.csv) · [Second instance and oracle diagnostics](natural_experiment_literal_instances.csv)

## Matching adjacent reference hazards

For two hits, consider a second score with the same clipped empirical correction. Set \(c_m=q_m\) and \(c_i-c_{i+1}=(q_i-q_{i+1})(1-\sum_{j<i}q_j)\). Sort by \(c_i-\operatorname{clip}(\widehat v_i-v_i^0,[-2\lambda,2\lambda])\). The original reference score has an additional \(q_iq_{i+1}\) in each adjacent gap. Removing it matches the population exchange comparison after the natural prefix and makes empirical noise more likely to exchange nearby primes.

Each row below compares both scores on the very same multinomial draws. Both mean columns divide each draw's excess by its own population's increasing-order excess before averaging. The last column counts draws where the adjacent-gap score costs more by over \(10^{-18}\) expected probes. The complete curves, including absolute excess and 95th percentiles, are in the two learning-curve CSVs.

| Menu size | Equivalent words | Original mean | Adjacent-gap mean | Paired draws costing more |
|---:|---:|---:|---:|---:|
| 1024 | 49,198 | 1.763 | 1.833 | 60.7% |
| 1024 | \(2^{30}\) | 0.4032 | 0.4671 | 100% |
| 1024 | \(2^{32}\) | 0.1050 | 0.1167 | 100% |
| 1024 | \(2^{34}\) | 0.03057 | 0.02898 | 11.9% |
| 1024 | \(2^{38}\) | 0.007760 | 0.001680 | 0% |
| 8192 | 665,162 | \(2.937\cdot10^6\) | \(3.233\cdot10^6\) | 100% |
| 8192 | \(2^{52}\) | 1.644 | 2.843 | 100% |
| 8192 | \(2^{54}\) | 0.4753 | 0.6110 | 93.8% |
| 8192 | \(2^{56}\) | 0.2519 | 0.09510 | 0% |
| 8192 | \(2^{58}\) | 0.08604 | 0.02162 | 0.8% |
| 8192 | \(2^{60}\) | 0.003513 | 0.001911 | 35.2% |

Given exact frequencies at \(m=1024\), the adjacent-gap score attained the oracle in two populations. The other two orders differed by one or two disjoint adjacent swaps. Exact rational evaluation of those swaps gave excesses of \(4.861\cdot10^{-13}\) and \(4.987\cdot10^{-13}\) probes, respectively. These correspond to \(7.84\cdot10^{-9}\) and \(8.10\cdot10^{-9}\) of increasing-order excess, down from the original score's range of 0.00649–0.00672. At \(m=8192\), both noiseless scores attained the oracle on all four populations. The adjacent-gap score cost more on average at the lower budgets for both menus. Its first lower mean among the tested budgets occurred at \(2^{34}\) and \(2^{56}\), respectively. [1024-item paired results](natural_experiment.csv) · [8192-item paired results](natural_experiment_literal.csv)

## A held-out check that preserves the increasing-order fallback

For pairs, the max-index statistic can certify improvement against increasing order. Use the first half of the total sample to learn a proposal with ranks \(r_i\), write \(x_i=r_i-i\), and let \(w_{ij}\) be the true pair mass. An exact expansion about increasing order gives

$$
C(r)-C(\mathrm{ascending})=
\sum_i(q_i-v_i)x_i-\sum_{i<j}w_{ij}(r_i-r_j)_+.
$$

Thus the first term is an upper bound. A fresh validation word contributes \(Y=x_{\max Z}\) if it has two hits and zero otherwise. The upper bound equals \(\sum_i q_i x_i-\mathbb E Y\). Under the finite uniform-block density promise, \(\mathbb E Y^2\le(1+\epsilon)\sum_i x_i^2[v_i^0+(i-1)/L]\) using one-based indices. Condition on the fitted proposal and apply one-sided Bernstein to the validation average with this variance bound and \(|Y-\mathbb E Y|\le2\max|x_i|\). The code also adds \(\sum_i|x_i|/L\) for the allowed marginal rounding. Keep the proposal only when the resulting upper confidence bound is strictly negative. The probability of paying more than increasing order is at most 5% for each fixed sample budget and law. At every tested budget none of the 512 guarded repetitions exceeded increasing-order cost. The same total \(N\) is used for the split and unsplit columns, with independent Monte Carlo runs.

Run the script with Python and NumPy (2.0.2 used here). [Source and oracle](natural_experiment.py) · [All sample budgets and success frequencies](natural_experiment.csv) · [Per-population constants and checks](natural_experiment_instances.csv)

~~~sh
python3 natural_experiment.py
~~~
