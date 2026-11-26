# Supplement for the disjoint-pair experiment

This measurement concerns the separate disjoint-pair experiment reported under “Probe counts and parallel checks.” The primary Section 7 one-hit experiment and its different source support are evaluated in [onehit_shift](../onehit_shift/README.md).

Within each of three quartets, source A has pairs 01 and 23, B has 02 and 13, and the additional source C has 03 and 12. Each quartet and each of its two pairs are selected uniformly conditional on a nonempty word; empty words have probability 1/5. Source A training uses 8,192 previous integers, full divisor masks and residual greedy. Its per-seed median combined histogram and order fitting time was 50.96 microseconds across five seeds. Constructing the 12-entry runtime table is outside that timer. Increasing-index tie breaking chooses one endpoint of each source A pair. This set also happens to cover C completely. The runtime batch of six, the trained cascade, and the fixed controls all use the frozen exact packet fallback.

The width-six set 0,3 in each quartet hits every A or B edge, and the width-nine set 0,1,2 hits every A, B or C edge. The CPU experiment enumerates all 4,096 sets and checks minimality. A family's support supplies both fixed filters. The online matching comparator fully reads the twelve divisor indicators at the start of each 2,048-word epoch. Once it has observed six disjoint pairs covering all twelve vertices it uses one endpoint per pair until the next epoch. A contradiction or 64-word timeout sends the remainder of the epoch directly to packet fallback. The timing includes those diagnostic words. The independent primality reference checks every actual integer from every method.

| Source | Packet | All 12 | A-trained six | A-trained cascade | Common AB six | Common ABC nine | Matching learner |
|---|---:|---:|---:|---:|---:|---:|---:|
| A | 89.24 | 28.45 | 25.26 | 26.70 | 25.34 | 26.99 | 26.67 |
| B | 88.05 | 28.14 | 62.06 | 32.09 | 25.88 | 26.71 | 26.43 |
| C | 88.10 | 28.29 | 26.15 | 26.71 | 61.44 | 26.80 | 26.64 |
| Uniform odd | 103.40 | 107.98 | 104.78 | 107.06 | 104.11 | 105.55 | 104.30 |
| ABCA | 88.14 | 28.06 | 34.92 | 28.04 | 34.97 | 26.69 | 28.90 |

Cells are warmed ns per input on the Apple M4/FLINT 3.6.0 setup of the companion experiment. This supplement ran one timing session on five fresh seeds and 32,768 words per law per seed, with eight balanced rounds. ABCA switches after 8,705, 17,381, and 26,113 words. The training seeds, independent test seeds, input fingerprints, prime counts, fit costs and timed positions are in the CSV files. The conjectured benefit of a common six depends on which matchings are admitted.

~~~sh
clang++ -std=c++17 -O3 -mcpu=native shift_stress.cpp -o /tmp/disjoint-shift
out=$(mktemp -d)
/tmp/disjoint-shift /path/to/libflint.dylib "$out/session1"
~~~

[Raw timings](session1/timings.csv) · [Counts](session1/counts.csv) · [Training](session1/offline_fit.csv)
