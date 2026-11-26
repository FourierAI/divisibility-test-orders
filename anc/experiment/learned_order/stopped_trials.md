# Choosing six divisors from first-hit logs

A single training record contains the public priority mask and the first successful divisor, or an empty symbol. The learner never sees the word, its full divisor set, its hit count, the pair distribution, or its hidden sign. Its fitted model uses the stated cap of two hits among the twelve candidate primes. The same 64-bit exact packet/FLINT backend completes classification after a screening miss.

## Two indistinguishable fixed priorities

The twelve primes from 1637 through 1733 are split into three consecutive quartets. An empty menu hit set has probability 1/5. Otherwise choose a quartet uniformly and draw one of six equally weighted pair tickets. Within a quartet numbered 0,1,2,3, source A has tickets 01, 23, 02, 02, 13, 13. Source B has tickets 01, 23, 03, 03, 12, 12. For each selected product draw a cofactor uniformly from the odd multipliers putting the word in the upper half of the 64-bit range, rejecting multipliers divisible by any of the 12 menu primes. Rejection is conditional on the ticket, preserving its probability. All measured synthetic inputs are actual integers.

Every menu prime has marginal hit probability 2/15 in both sources. Given a nonempty selected quartet, the first hit under increasing priority has probabilities 1/2, 1/3, 1/6, 0, respectively, under both sources. Even unlimited increasing first-hit logs leave the two sources indistinguishable. For a six-prime selection, write s for the number of unselected labels in each quartet. Over an equal mixture of A and B all six distinct pairs per quartet are equiprobable. The number of uncovered pairs is minimized when the three s values are 2,2,2. Hence on that mixture the probability of missing a nonempty word is at least 2/15 per ordinary input, in addition to empty words. Within either individual source a suitable six-prime selection covers every nonempty word.

The tables report complete, warmed single-word calls on one Apple M4 with FLINT 3.6.0. Every candidate prefilter uses the same multiplication-based batch kernel and fallback. «Full A» has all 12 training divisibility outcomes. «Fixed A» sees only the first hit in increasing order and chooses the six most frequent. «First A/B» use the randomized one-hit log below. All-12 uses the twelve predicates in one batch and has no training cost. Input generation, feature extraction during training, and fitting are outside the inference timer.

| Input | Session | FLINT | Packet | All-12 | Fixed A | Full A | First A | First B |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| A | first | 112.71 | 89.11 | 28.83 | 39.20 | 25.78 | 25.84 | 50.98 |
| A | repeat | 113.72 | 89.24 | 29.02 | 39.95 | 25.82 | 26.72 | 51.36 |
| B | first | 112.05 | 88.60 | 27.99 | 37.97 | 51.00 | 51.19 | 24.94 |
| B | repeat | 113.58 | 89.56 | 28.31 | 38.50 | 51.80 | 52.06 | 25.39 |
| Uniform odd | first | 127.75 | 104.58 | 108.21 | 103.62 | 102.90 | 102.90 | 102.07 |
| Uniform odd | repeat | 127.65 | 104.19 | 108.43 | 103.47 | 104.75 | 104.69 | 104.38 |

Each cell is the median of five seed medians in ns per input. Each seed covered 32,768 held-out inputs per law and eight balanced timing blocks. A fresh compilation and timing session reused the frozen seeds. The independent twelve-base Miller–Rabin reference checked all 491,520 input slots. The timings do not measure isolated cold calls. Uniform-odd inputs use the learned schedules from the two synthetic sources.

## One recorded hit per training input

Independently mark each divisor with probability 1/2. Scan marked divisors in increasing order, then unmarked divisors in increasing order, stopping at the first hit. If the returned index j is unmarked, it is the smallest true hit. For each i>j, add −4 to the ij pair count estimate if i is marked and +4 otherwise. Add two to the uncorrected singleton estimate for j. After all words, subtract half the sum of the estimated ij pair counts from that singleton. Empty logs and marked first hits have zero update. These estimates divided by the number of words are unbiased for the pair and singleton probabilities under the two-hit cap. Finally select the six indices with highest estimated coverage over all 924 possibilities. Ties go to the smallest numerical mask. The full-information arm uses the same selection criterion on its census.

Across five independent training replicates of each source, 0, 2, 5 and 10 of the ten fitted sets covered all 18 positive tickets after 64, 256, 1024 and 8192 first-hit records. These nested sample sizes reuse the prefix of each training stream. Finite-sample selections sometimes differ by exchanging equivalent vertices. The 8192-record fits were frozen for timing. On A they rejected 79.92% of held-out words, the same held-out fraction as all-12. Applying the same A fits after changing the law to B rejected 53.31%. Training and fitting took a median of 0.479 ms across the ten fits in the first session and 0.481 ms on repeat. For A, the median per-seed ratio of this training cost to the per-call saving over all-12 was 160,163 and 176,594 future calls. Each ratio uses its own fitted schedule, timings, and training cost. This calculation assumes future words continue to follow the training law.

## Reproduction

From this directory, use the library path described in the [parent setup](../README.md). Give each run a fresh directory under the temporary root.

~~~sh
clang++ -std=c++17 -O3 -mcpu=native stopped_benchmark.cpp -o /tmp/stopped-benchmark
out=$(mktemp -d)
/tmp/stopped-benchmark /path/to/libflint.dylib "$out/session"
python3 summarize_stopped.py
~~~

The standard-library Python checker independently regenerates training and held-out integers using division, recomputes the learned, fixed-log and census selections, verifies held-out rejection counts and word hashes, and reproduces both published timing summaries. The native benchmark checks primality and measures time. [First session](stopped_results/timings.csv) · [Repeat session](stopped_repeat/timings.csv) · [Training sizes and selections](stopped_results/training.csv) · [Holdout counts](stopped_results/heldout.csv)
