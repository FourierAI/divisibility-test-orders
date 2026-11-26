# Learning the divisor order for one 64-bit primality call

On a synthetic workload with six equiprobable pairs of divisors, learning which divisors occur together reduced the mean number of leading checks from 7.203 to 5.207 per input. This was a **27.7% reduction in probes**. On an Apple M4 the complete exact call took 33.41 ns with the learned order and 33.87 ns with a marginal-frequency order. A second timing session on the same words gave 33.42 and 33.64 ns. The larger speedup came from placing the known 12-prime menu before the backend. Even its fixed increasing order took 33.63 ns in the first session, against 91.14 ns for the frozen packet backend alone. [First timing session](results/timings.csv) · [Second timing session](repeat/timings.csv)

Batching changed the engineering result. Checking all 12 divisors with one final branch took 29.17 ns on the same workload in a separate session. With a budget of **six divisors before exact fallback**, training identified six that screened every planted pair. That call took 26.59 ns, versus 62.54 ns for the six most frequent divisors and 28.82 ns for the full batch of 12 in that session. When the pairing changed but each divisor's frequency stayed fixed, the previously learned six rose to 62.06 ns and the full batch took 28.63 ns. [Full-batch control](batch_control.csv) · [Six-divisor cutoff](six_control.csv)

Standard residual greedy produced exactly the same ordered tables as the exact dynamic program on all six training sets. In a separate fit-cost run on A, it took 2.08 microseconds to fit from the observed histogram, versus 71.13 microseconds for the dynamic program. [Verified orders and fit costs](greedy_cost.csv)

## Matched arithmetic workloads

The menu contains the first 12 primes above the packet screen's largest divisor, 1627, in increasing order. Use zero-based indices into \((1637,1657,1663,1667,1669,1693,1697,1699,1709,1721,1723,1733)\). Both planted distributions choose no menu divisor with probability \(1/5\). Otherwise they choose one of six equiprobable pairs.

| Law | Allowed index pairs |
|---|---|
| A | (0,1), (2,3), (4,5), (6,7), (8,9), (10,11) |
| B | (0,2), (4,6), (8,10), (1,3), (5,7), (9,11) |

Every individual menu prime divides a word with probability \(2/15\) under both laws. Both have the same hit-count distribution. To turn the selected set into an integer, take its product \(d\), using \(d=1\) for the empty set. Sample an odd cofactor uniformly from the range that places \(d\) times the cofactor in \([2^{63},2^{64})\), rejecting cofactors that contain any menu prime. Rejection occurs **after** selecting the pair and repeats only the cofactor draw. Other small factors are allowed. The null uses uniform odd words over the full unsigned 64-bit range. This is a controlled test of changes in dependence among the 12 selected divisors. The planted frequency is much higher than their natural hit rates.

Each of three replicates fits one order on 8192 newly generated A words and, separately, a transfer control on 8192 B words. Each fit reads the integers and checks all 12 divisors. Generation labels are unavailable to the learner. Each replicate tests 65,536 independently generated words from **each** of A, B and the uniform null. The two timing sessions used identical training and held-out words. [All empirical mask counts](results/histograms.csv) · [Raw input fingerprints and verified counts](results/holdout.csv)

| Replicate | Train A | Train B | Test A | Test B | Test uniform odd |
|---|---:|---:|---:|---:|---:|
| 0 | 173141 | 247247 | 1009001 | 2009047 | 3009041 |
| 1 | 584309 | 592591 | 1009039 | 2009081 | 3009077 |
| 2 | 916781 | 939391 | 1009079 | 2009099 | 3009149 |

## Learner and measurement

The marginal rule stably sorts each prime by descending observed hit frequency, breaking ties by increasing prime. For the joint rule let \(H(R)\) count training words whose entire hit mask is contained in \(R\). With \(R\) the remaining set of unscreened primes, the exact empirical dynamic program computes \(V(\varnothing)=0\) and \(V(R)=H(R)+\min_{i\in R}V(R\setminus\{i\})\). A subset-sum transform supplies every \(H(R)\). Fitting takes \(O(k2^k)\) operations after counting the raw masks. This menu has 12 entries. The empty mask and six two-hit counts characterize the entire planted training law. In arbitrary data the implementation uses the complete mask. A survivor reaches the same exact backend under every order, so its fallback cost is independent of that order in the unit-probe objective. [Training and deployment header](learned_order.hpp)

Residual greedy picks the prime that rejects the most training words among those that remain after the previous checks. With disjoint pair masks, this means choosing the smaller endpoint of the heaviest uncovered pair, then repeating. The dynamic program makes exactly these choices under its increasing-index tie break. Both rules fill the zero-gain suffix in increasing order. The C++ audit compared every table entry for every training replicate. A separate Python implementation repeated the comparison on the archived histograms. The identical trained tables imply identical held-out word-by-word decisions and times through the common call path. [Residual-greedy audit](greedy_cost.cpp) · [Feige, Lovász and Tetali on greedy min-sum set cover](https://tetali.math.gatech.edu/PUBLIS/mssc_final.pdf)

For law A, each well-trained joint order tests one fresh endpoint of each pair in its first six positions. Conditional on a planted pair this takes 3.5 probes on average. Empty-set words use 12. The resulting population cost is exactly \(5.2\). Increasing order finds pairs at positions 1, 3, 5, 7, 9 and 11, giving \(7.2\) overall. In the observed A training samples the distinct pair counts make marginal sorting place each pair consecutively, also giving \(7.2\). A hand order that already knows the six pairs can reach \(5.2\) without training. The difference here concerns which schedule can be recovered from observations.

The sequential treatments all use the same compiled function on identically laid-out tables. Each leading check multiplies by the divisor's inverse modulo \(2^{64}\) and compares with \(\lfloor(2^{64}-1)/p\rfloor\). The unmodified packet screen receives survivors. Inputs at most \(2^{32}-1\) go directly to public FLINT to preserve correctness for small primes. The public FLINT comparator and the frozen packet comparator receive every input directly. Preloading a schedule occurs outside the timed loop. An ordinary deployment can call \(\texttt{learned\_order::is\_prime}\) with a prepared table and the two FLINT function pointers. [Benchmark](experiment.cpp) · [Frozen packet](../packet_screen/packet.hpp)

Every treatment received one warm-up pass per held-out batch. Two cycles of a six-treatment Williams order balanced timing positions and immediate predecessors. The time for each block is the elapsed time for an indirect-call loop divided by 65,536. A table cell takes the median of 12 block times per replicate and then the median of the three replicate medians. These are warm sustained per-word costs. Each of the six results on each of 589,824 held-out input slots was verified against the archived 12-base deterministic Miller–Rabin implementation. There were 12,573 prime slots. Direct remainders independently checked every feature mask, and every timed pass checked its prime count. [Independent arithmetic reference](../benchmark.cpp)

## Complete-call results

Each cell gives **first session / repeat session** in ns per input. The repeat measures timing variability on the same seeds.

| Input law | Public FLINT | Frozen packet | Increasing | Marginal from A | Joint from A | Joint from B |
|---|---:|---:|---:|---:|---:|---:|
| A | 113.51 / 112.66 | 91.14 / 89.57 | 33.63 / 33.68 | 33.87 / 33.64 | 33.41 / 33.42 | 34.07 / 33.37 |
| B, shifted from A | 113.04 / 113.00 | 89.18 / 89.16 | 33.40 / 33.36 | 32.94 / 32.82 | 33.19 / 33.40 | 32.87 / 32.83 |
| Uniform odd | 125.91 / 127.11 | 102.99 / 103.62 | 105.32 / 106.33 | 105.57 / 106.11 | 106.22 / 106.24 | 105.24 / 105.46 |

| Input law | Increasing probes | Marginal from A | Joint from A | Joint from B |
|---|---:|---:|---:|---:|
| A | 7.2043 | 7.2029 | 5.2074 | 7.0210 |
| B, shifted from A | 6.7980 | 5.7382 | 6.9410 | 5.2045 |
| Uniform odd | 11.9632 | 11.9638 | 11.9632 | 11.9643 |

The learned A order beat the A marginal order in elapsed time on two of three individual seed medians in the first session and all three in the repeat. On B its probe cost exceeded the transferred marginal rule's by 1.203 per input. Refitting on B restored the lower probe count. On uniform odd inputs all leading schedules checked close to the full menu, and the frozen packet was faster. CPU time also depends on the implementation. The B-trained schedule, which used 7.021 probes on A, narrowly beat the A-trained schedule in the repeat.

## One-time training and break-even

Training times start with 8192 existing words in memory. They include building the full divisor-mask histogram and producing the inference table. Nine warm measurements per training set alternate which fit runs first. The median A acquisition time was 48.1 / 47.5 microseconds in the two sessions. Joint fitting took 62.9 / 58.4 microseconds and marginal fitting took 2.38 / 2.25 microseconds. The median of the measured within-run sums for acquisition plus joint fitting was 125.0 / 105.8 microseconds. Taking medians before adding can give a different number. Workload generation, input transport and selecting the 12-prime menu are outside these times. [First training measurements](results/training.csv) · [Repeat training measurements](repeat/training.csv)

Break-even counts below divide the per-replicate one-time cost by that replicate's median time saved per future A word and round up. Relative to an untrained method, the numerator includes acquisition and the joint fit. Relative to the marginal learner it uses the joint fit's additional cost over the marginal fit, since both consume the same measured census. “No gain” means the measured per-word difference was nonpositive. Small time differences make these ratios sensitive to timing variation.

| Comparator | First session, three replicates | Repeat, three replicates |
|---|---:|---:|
| Public FLINT | 1,735 / 1,552 / 1,315 | 1,325 / 1,471 / 1,291 |
| Frozen packet | 2,362 / 2,185 / 1,843 | 1,867 / 2,076 / 1,816 |
| Increasing, same menu | No gain / 184,088 / 140,259 | 184,921 / 453,163 / 120,191 |
| Marginal from A, same census | No gain / 65,604 / 74,333 | 105,490 / 301,553 / 65,031 |

## Supplemental batching and a fixed budget of six

After the two sequential-order sessions, two additional comparisons used the same training and held-out seeds, method call protocol, independent reference and timing design. Each was repeated without changing its settings. First, a straight-line bitwise OR of all 12 inverse-test predicates charges one final hit branch. With a runtime-loaded divisor table, its A times were **29.17 / 28.83 ns** versus **33.19 / 32.75 ns** for joint-A sequential checks in those same sessions. It was faster on each of the three seeds in both sessions. Under B the all-12 batch took 29.07 / 28.86 ns and the transferred joint order took 33.65 / 33.38 ns. On uniform odd inputs the batch took 107.47 / 107.02 ns and the frozen packet took 103.29 / 103.61 ns. A separate compile-time constant version of the 12-predicate OR took 33.94 / 34.07 ns on A. For the runtime table, Apple clang emitted twelve scalar multiplies, one compare, eleven conditional compares and one conditional branch before fallback. The constant-table timings also depend on the compiler and CPU. [Batch implementation](batch_control.cpp) · [First batch session](batch_control.csv) · [Repeat batch session](batch_repeat.csv)

The second comparison fixes a budget of six leading tests. It evaluates the first six primes of a given order as one runtime-loaded batch and calls the complete packet backend after a miss. All four six-prime selections use the identical native function. The cost of reordering within their batch is immaterial. The budget of six was deliberately chosen for the planted six-pair structure after seeing the sequential experiment. The training algorithm still recovers its six indices solely from its integer samples. Increasing order and the trained marginal order each place both endpoints of three A-pairs in their first six. The joint order selects one endpoint of every pair. On B this previously learned selection touches only three of the new pairs.

| Actual input law | Frozen packet | Full batch of 12 | First six increasing | First six marginal-A | First six joint-A | First six joint-B |
|---|---:|---:|---:|---:|---:|---:|
| A | 89.10 / 90.92 | 28.82 / 29.58 | 62.10 / 62.83 | 62.54 / 63.44 | **26.59 / 27.12** | 61.79 / 62.99 |
| B | 89.13 / 89.39 | 28.63 / 28.71 | 51.56 / 51.45 | 50.26 / 51.66 | 62.06 / 63.15 | **26.21 / 26.42** |
| Uniform odd | 102.98 / 104.56 | 106.75 / 107.15 | 103.22 / 104.17 | 103.54 / 104.34 | 103.28 / 104.07 | 103.18 / 104.54 |

On A, the six marginal-A primes rejected 39.91% of held-out integers and the six joint-A primes rejected 79.89%. On B the six joint-A primes rejected 39.86% and the six joint-B primes rejected 80.01%. On the null only 0.34% hit a joint-A prime. The smaller batch always preserves exact primality via fallback. It changes which divisors are tested before fallback, which accounts for the more substantial timing differences compared with the full 12-prime order experiment. Relative to the untrained full batch of 12, the A-trained six saved 2.10–2.49 ns on each of six seed/session comparisons. Pairing the corresponding primary session's separate acquisition-plus-fit time with these rates yields 42,257–64,690 subsequent A calls to recover training. Against the six marginal-A primes, the incremental same-census fit cost amortizes in 1,369–1,851 A calls. A batch chosen with advance knowledge of the matching can achieve identical coverage. [First cutoff session](six_control.csv) · [Repeat cutoff session](six_repeat.csv)

The separate residual-greedy session measured 90.92 microseconds for histogram acquisition and 92.96 microseconds for acquisition plus fitting on A, using medians of three replicate medians. Acquisition time varied between binaries and sessions. Pairing its per-replicate total cost with the two cutoff sessions gives **37,747–44,280 subsequent A calls** to recover the greedy learner's cost relative to the untrained batch of 12. The exact dynamic program provides a finite optimality check for these planted data. [Raw greedy measurements](greedy_cost.csv) · [Amortization recalculation](summarize.py)

The following deployment uses the same six-predicate function as the cutoff benchmark. An existing exact primality callable can supply the fallback.

~~~cpp
#include "learned_order.hpp"
#include <vector>

learned_order::Schedule train(const std::vector<prime_screen::Word>& previous_inputs) {
    learned_order::Census counts{};
    for (auto n : previous_inputs) ++counts[learned_order::hit_mask(n)];
    return learned_order::prepare(learned_order::fit_residual_greedy(counts));
}

int is_prime(prime_screen::Word n, const learned_order::Schedule& schedule,
             prime_screen::Test ordinary, prime_screen::Test odd_after_screen) {
    auto exact = [=](prime_screen::Word x) {
        return prime_screen::packet::is_prime(x, ordinary, odd_after_screen);
    };
    return learned_order::is_prime_batch<6>(n, schedule, exact);
}
~~~

## Reproduction

The measurements used an ARM64 Apple M4, macOS 26.2 (25C56), Apple clang 17.0.0 (clang-1700.6.3.2), and FLINT 3.6.0. The library SHA-256 was \(\texttt{9c257de62afab11ce51b94658faf6d9fd08a062809e86e117ccb8c8b8eea7d03}\). Run from this folder with a 64-bit FLINT installation exporting \(\texttt{n\_is\_prime}\) and \(\texttt{n\_is\_prime\_odd\_no\_trial}\). The command creates fresh output directories and refuses to overwrite existing results. On machines without ARM64 NEON the frozen header selects its portable fallback, which changes the timing comparison. [FLINT library setup](../README.md)

~~~sh
clang++ -std=c++17 -O3 -mcpu=native experiment.cpp -o /tmp/prime-learned-order
out=$(mktemp -d)
/tmp/prime-learned-order /path/to/libflint.dylib "$out/first"
/tmp/prime-learned-order /path/to/libflint.dylib "$out/repeat"
python3 summarize.py "$out/first" "$out/repeat"
clang++ -std=c++17 -O3 -mcpu=native batch_control.cpp -o /tmp/prime-batch-control
/tmp/prime-batch-control /path/to/libflint.dylib > "$out/batch.csv"
clang++ -std=c++17 -O3 -mcpu=native -DLEARNED_ORDER_CUTOFF_SIX batch_control.cpp -o /tmp/prime-six-control
/tmp/prime-six-control /path/to/libflint.dylib > "$out/six.csv"
clang++ -std=c++17 -O3 -mcpu=native greedy_cost.cpp -o /tmp/prime-greedy-cost
/tmp/prime-greedy-cost > "$out/greedy.csv"
~~~

Running \(\texttt{python3 summarize.py}\) with no arguments recalculates both archived sessions. It verifies that the two sessions used the same observed masks and orders, independently checks the empirical optimum on all six fitted schedules using the matching structure, and reconstructs held-out probe counts from the published histogram. Timing file SHA-256 values are \(\texttt{2fd6fed17247c940181a7398fd4bcc58a004b71234d5e6f988c0b7de06e74114}\) and \(\texttt{1d0cf282a4dc759fd9772438ca7c6fece1152512c8d1e3992ccf668b72bedb2f}\). These finite experiments quantify the cost of this menu and two specified distributions on one machine. They establish neither an asymptotic learning rate nor a change to the arithmetic complexity of primality testing.

A second experiment with distinct sources, fresh seeds and randomized first-hit logging is described in [stopped_trials.md](stopped_trials.md).
