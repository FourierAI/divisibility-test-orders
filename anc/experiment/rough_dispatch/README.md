# Skipping known small factors before exact 64-bit primality testing

On an Apple M4, random odd words already sieved through 149 took 455.05 ns to test when the filter resumed at 151. Repeating the wheel and divisibility tests from the start took 463.44 ns. The saving was 7.03–9.38 ns per word across the three seed medians, and the resumed filter beat each of the three comparison functions in 31 of 36 paired blocks. For words already sieved to 733, sending them directly to the exact fallback took 545.24 ns, while searching the remaining primes through 1627 took 562.12 ns.

| Actual prior sieve | Hint supplied | FLINT 3.6.0 | Existing full prescreen through 1627 | Direct odd fallback | Resume after hint through 1627 |
|---:|---:|---:|---:|---:|---:|
| 13 | 13 | 319.06 | 272.94 | 477.15 | 272.62 |
| 149 | 149 | 530.67 | 463.44 | 514.80 | 455.05 |
| 733 | 733 | 562.13 | 597.62 | 545.24 | 562.12 |
| 1627 | 1627 | 582.21 | 672.12 | 569.31 | 569.34 |
| Unfiltered odd | 149 | 128.64 | 109.40 | 441.28 | 386.24 |

Entries are median ns per word, first across 12 rounds within a seed and then across three seed medians. The intended comparison is throughput of the downstream decision on a stream produced by an existing sieve. Creating that stream is outside the timer. A caller who must construct a sieve specifically for this purpose would pay additional costs. The 1627 hint reaches the direct backend through the same logical control path, providing a timing control. A wrong hint still yields the correct answer, since only a proper divisor can cause early rejection and FLINT handles every surviving odd integer. The last row measures the cost of assuming a prior sieve when the input is actually unfiltered.

Each workload per seed contains 65,536 random odd words above `UINT32_MAX`. The generator draws uniform odd words and rejects each violating the specified presieve, checking the actual prime remainders. Four sets use the stated prior cutoffs and exclude the cost of obtaining that metadata. Implementations receive the same values. Each input is checked against the original 12-base deterministic Miller–Rabin reference before timing. A four-treatment Williams design balances position and preceding function over each four rounds, and checksums consume every result. The three seeds are 4811291, 197930093 and 845116723. Each arm calls one native function per input. The public FLINT function and the existing screen are from the earlier experiment. The direct arm uses the same full odd-word backend as the resumed arm. The current program specializes the hint outside the per-input timing loop.

The signed results apply to the stated workloads and one machine. Continuing through 1627 was fixed using the earlier raw-word study. The experiment compares four existing policy choices and does not establish a universally optimal cutoff. No Riemann hypothesis occurs in the decision or in the timing comparison. [Original FLINT implementation](https://github.com/flintlib/flint/blob/v3.6.0/src/ulong_extras/is_prime.c) · [All 180 timing blocks](results.csv)

To reproduce on macOS ARM64 with the FLINT 3.6.0 dynamic library from the parent experiment, run the following from this directory.

~~~sh
clang++ -std=c++17 -O3 -mcpu=native rough.cpp -o /tmp/prime-rough-benchmark
/tmp/prime-rough-benchmark /path/to/libflint.dylib > /tmp/prime-rough-results.csv
~~~
