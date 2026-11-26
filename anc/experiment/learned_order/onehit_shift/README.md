# Distribution shift in the 74-page manuscript's one-hit experiment

On a stable source A, learning six divisors saved **1.40–1.87 ns per complete primality call** against a fixed nine-divisor filter on all five seed medians in both timing sessions. The nine-divisor filter covers every planted pair in both A and B with zero training. After a change from A to B, running the frozen six took 50.65 / 50.16 ns per word and the fixed nine took 26.25 / 26.20 ns. Both methods returned the same exact primality decisions.

## Workloads and comparators

The code uses the original Section 7 generator, logger and empirical coverage estimator. The candidate primes are 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723 and 1733, divided into three consecutive quartets. With probability 1/5 a word has no candidate divisor. Otherwise choose a quartet uniformly, then one equally weighted ticket from `01,23,02,02,13,13` for A or `01,23,03,03,12,12` for B. An odd cofactor coprime to all twelve candidates places the word in the upper half of the unsigned 64-bit range. The null consists of uniform odd 64-bit words. The ABAB stream has successive segment lengths 8,705, 8,676, 8,732 and 6,655. Its three switches occur inside the online learner's 2,048-word epochs. [Original generator and estimator](../stopped_benchmark.cpp)

Each general one-hit fit receives 8,192 records, uses independent fair priority marks, and maximizes the estimated coverage over the 924 sets of six. It receives the twelve-prime menu and the two-hit cap. The source structures and the quartet partition are supplied to the three specialized controls below.

- **Minimax six** chooses labels 0 and 1 in each quartet. It misses just ticket 23 in each source, for a population rejection rate of 2/3 of all words. Over the equally weighted pair of sources all six edges of a quartet are equiprobable. Leaving two unselected vertices in each quartet minimizes the number of uncovered edges over the three quartets by convexity of the binomial coefficient. This fixed set is optimal for worst-source coverage under the six-divisor budget.
- **Common nine** chooses labels 0, 1 and 2 in each quartet. Together A and B contain every edge of the complete graph on the quartet. Covering all edges in all three quartets requires at least nine vertices. This filter ties the source-aware oracle's population rejection rate of 4/5 in both sources. The source-aware oracle chooses 0 and 3 for A and 0 and 2 for B in each quartet. For ABAB the oracle receives the switch positions and installs its table once per segment.
- **Targeted router** starts an epoch with alternating public masks consisting of the oracle A six and the oracle B six. An unmarked first hit when using the A six certifies B given the two-source promise, and conversely. Conditional on using the other source's six, the probability of such a witness is 4/15. The router selects a six after two consistent witnesses, uses packet fallback for the rest of the epoch after conflicting witnesses or the 64-record cap, and starts over after 2,048 words. During diagnosis the logged first hit also rejects eligible composites. The inference timer includes obtaining the actual one-hit records, the routing logic and all fallback calls. Uniform words can generate spurious source identifications.

The cascade tests the trained A six first and the remaining six only after a miss. Its second stage is an out-of-line helper preserving this branch. All fixed batches use runtime divisor tables. The public FLINT and frozen packet baselines receive every word directly. On the uniform workload the source-aware oracle entry uses the packet backend.

## Complete-call timings

Entries are ns per word, first session / repeat. Each cell is the median across five seed medians. A seed median uses ten warmed timed passes over 32,768 identical inputs for every treatment. A balanced ten-treatment ordering rotates timing positions. The same indirect-call loop handles every method. All methods traverse the same four contiguous spans on ABAB. Only the oracle uses span identity to select its table. Online state lasts across spans and starts anew for each independent timed pass. These measurements are sustained single-word throughput on one machine.

| Filter | A | B | ABAB | Uniform odd |
|---|---:|---:|---:|---:|
| Public FLINT | 112.48 / 111.42 | 111.30 / 111.20 | 112.48 / 112.54 | 126.99 / 126.41 |
| Frozen packet | 88.02 / 87.78 | 87.65 / 87.73 | 88.38 / 88.24 | 104.38 / 103.70 |
| All twelve | 28.61 / 28.52 | 27.81 / 27.53 | 27.77 / 27.83 | 108.51 / 108.33 |
| Minimax six | 38.55 / 38.46 | 37.51 / 37.23 | 37.76 / 37.60 | 104.92 / 104.60 |
| First hit A | 25.66 / 25.86 | 50.65 / 50.16 | 36.78 / 36.46 | 105.33 / 104.96 |
| First hit B | 50.81 / 50.45 | 24.59 / 24.79 | 38.63 / 38.41 | 105.56 / 105.32 |
| Trained A six, then remaining six | 27.17 / 26.91 | 32.20 / 32.35 | 29.16 / 29.25 | 108.17 / 108.06 |
| Common nine | 27.34 / 27.27 | 26.25 / 26.20 | 26.37 / 26.47 | 106.87 / 107.25 |
| Source-aware oracle | 25.68 / 25.51 | 24.63 / 24.70 | 24.79 / 24.82 | 104.37 / 104.13 |
| Targeted router | 29.91 / 29.65 | 28.70 / 28.74 | 31.38 / 31.24 | 106.28 / 105.50 |

All ten independently trained sets covered all 18 own-source tickets and 12 opposite-source tickets. The A-trained six rejected 80.046% of actual A words, 53.366% of B and 67.496% of ABAB. The common nine rejected 80.046%, 80.035% and 79.938%. The targeted router rejected 77.396% on ABAB. On pure A and B it made 80 correct selections in 80 epochs each, using 1,132 and 1,074 diagnostic records, respectively. On the uniform null it acquired 5,064 diagnostic records and called three of the 80 epochs A or B. The router's work offset its coverage gain over the transferred A-trained six when compared with the common nine. The oracle and the fitted six have identical maximum coverage on a stable source.

## Training cost and reproduction

The one-time A training cost for 8,192 in-memory inputs was 287.1 / 328.0 microseconds, including first-hit acquisition, inference over all candidate sets, and construction of the runtime table. The two median per-seed break-even counts against the common nine were **169,526 / 217,405 future A calls**. Against all twelve they were 96,617 / 114,238. Each quotient uses one seed's fit time and per-word speed difference. The input generator and library loading are outside these measurements. The archived paper experiment used different seeds and a different binary. The two new timing sessions repeated exactly the same new holdouts.

Five training seed bases were 8870301, 8870333, 8870397, 8870451 and 8870525, with 100903 added for B and another 15000107 for the mark generator. Five held-out bases were 58399171, 58516723, 58643333, 58784317 and 58918369. Add 1000003 times the law index (A=0, B=1, uniform=2, ABAB=3). In ABAB segment j, starting at 1, add another 10000019 times j. Each timing session checks all ten classifiers on 655,360 input slots using an independent twelve-base deterministic Miller–Rabin reference. A standard-library Python replay reconstructs the ten fits, every held-out input hash and rejection counts using direct division. Sources are synthetic and enriched with the selected divisors. These comparisons estimate no cryptographic or general-input speedup.

The measured platform was an Apple M4, macOS 26.2 (25C56), Apple clang 17.0.0 (clang-1700.6.3.2) and FLINT 3.6.0. The library SHA-256 was `9c257de62afab11ce51b94658faf6d9fd08a062809e86e117ccb8c8b8eea7d03`. Run from this directory. The build script extracts the archived benchmark's unchanged definitions before its main function, and includes them at compile time.

~~~sh
sh build.sh /tmp/onehit-shift
out=$(mktemp -d)
/tmp/onehit-shift /path/to/libflint.dylib "$out/session1"
sh build.sh /tmp/onehit-shift
/tmp/onehit-shift /path/to/libflint.dylib "$out/session2"
python3 -B summarize.py "$out/session1" "$out/session2"
python3 -B replay.py "$out/session1"
~~~

[First timings](session1/timings.csv) · [First counts](session1/counts.csv) · [First fits](session1/training.csv) · [Repeat timings](session2/timings.csv) · [Repeat counts](session2/counts.csv) · [Repeat fits](session2/training.csv)
