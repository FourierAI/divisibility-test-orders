# Testing one 64-bit integer with four-lane prime packets

On an Apple M4, a deterministic primality call on uniform random odd 64-bit integers took 107.71 ns on average per word. The original FLINT 3.6.0 call took 130.39 ns, the earlier four-at-a-time prescreen with FLINT took 109.75 ns, and a scalar prescreen with identical exit points took 112.68 ns. All three seed medians favored the packet method over both scalar screens. On inputs already known to be prime or formed from two large primes, the public FLINT call was faster.

| Workload | Public FLINT | Earlier prescreen | Scalar with identical groups | New packet screen | Packet beats earlier screen, paired rounds |
|---|---:|---:|---:|---:|---:|
| Uniform unsigned 64-bit | 66.41 | 59.82 | 60.90 | **57.79** | 29/36 |
| Uniform odd unsigned 64-bit | 130.39 | 109.75 | 112.68 | **107.71** | 26/36 |
| Odd integers in the upper half of the 48-bit interval | 101.26 | 91.23 | 92.40 | **86.02** | 35/36 |
| 64-bit primes with high bit set | **846.93** | 915.88 | 927.10 | 885.87 | 34/36 |
| Products of two 32-bit primes with high bits set | **440.62** | 536.00 | 548.12 | 499.53 | 36/36 |

Times are ns per input. For each method and workload, the table takes the median of the 12 block times for each seed, then the median of the three seed medians. The old and new screens both test every odd prime through 1627. On odd 64-bit words the old-minus-new difference across the individual seed medians ranged from 1.86 to 4.14 ns per word. Repeated warm calls measure sustained single-word throughput on this CPU. The blocks reuse the same per-seed inputs, and their win counts are descriptive. [Raw measurements](results.csv)

## Arithmetic and API

The wheel first rejects multiples of 2, 3, 5, 7, 11 and 13. The next 64 primes, 17 through 349, use the previous scalar checks. Pack the remaining primes, 353 through 1627, two or three per odd product \(M\le 2^{31}-1\). Set \(v=\lfloor 2^{64}/M\rfloor\). For \(0\le n<2^{64}\) form

\[
 \widehat q=\left\lfloor nv/2^{64}\right\rfloor,
 \qquad r=n-\widehat q M.
\]

Since \(0\le n/M-nv/2^{64}<1\), the estimated quotient is either the exact floor or one smaller. Hence \(0\le r<2M<2^{32}\), and every prime in the packet divides \(r\) exactly when it divides \(n\). It follows that the low 32 bits of \(n-\widehat q M\) give all of \(r\). The implementation computes four 64-bit high products, then forms four packet remainders with 32-bit NEON lanes. For each packet prime \(p\), a vector multiply and comparison tests \((rp^{-1}\bmod 2^{32})\le\lfloor(2^{32}-1)/p\rfloor\). Four lanes work on the same input integer. After the small factors, FLINT's exact odd-word routine handles the survivor. Inputs up to `UINT32_MAX` use the public FLINT function.

The method combines established arithmetic techniques. FLINT 3.6.0 implements this approximate remainder as `n_mod_barrett_lazy` and documents the modular-inverse divisibility test. Kruppa describes reducing to a single-word congruent value before applying the inverse test in trial division. Here the 31-bit product bound allows four approximate remainders to feed one 32-bit vector on a 64-bit input. These measurements quantify this particular implementation. [FLINT lazy Barrett implementation](https://github.com/flintlib/flint/blob/v3.6.0/src/ulong_extras.h#L356-L369) · [FLINT divisibility algorithm](https://flintlib.org/doc/algorithms/arithmetic/divisibility-test.html) · [Kruppa, Chapter 4](https://docnum.univ-lorraine.fr/public/SCD_T_2010_0054_KRUPPA.pdf)

With 64-bit FLINT limbs and C++17, include the header and pass the two FLINT entry points. The implementation requires just one input and has no training or initialization phase. The tables are compile-time constants. On non-NEON targets with the parent's LP64 calling convention, the same function delegates to the earlier portable prescreen. The portable branch was compiled and checked with ARM NEON disabled on the M4. [Callable header](packet.hpp)

~~~cpp
#include <flint/ulong_extras.h>
#include "packet.hpp"

bool prime(std::uint64_t n) {
    return prime_screen::packet::is_prime(n, n_is_prime, n_is_prime_odd_no_trial);
}
~~~

## Measurements and reproduction

The machine ran macOS 26.2 (25C56) on Apple M4, using Apple clang 17.0.0 (clang-1700.6.3.2), `-std=c++17 -O3 -mcpu=native`, and the ARM64 FLINT 3.6.0 dynamic library from the parent experiment. Its SHA-256 was `9c257de62afab11ce51b94658faf6d9fd08a062809e86e117ccb8c8b8eea7d03`. The earlier screen, new packet screen and matched scalar use this same downstream library. The exact scalar control has the same wheel, prefix and prime order. Its remaining exits come after eleven batches of 12, one of 10, five of 8 and one of 6, with fixed loop bounds and no runtime branching on the batch size.

The prefix length and maximum packet length were chosen on a separate 75,000-word pilot. In the displayed run the untouched seeds were 651153979, 89921013 and 278735509. Per seed, the five workloads used 65,536 uniform words, 65,536 odd words, 32,768 odd 48-bit words, 4,096 primes and 4,096 semiprimes. The benchmark verified all 516,096 inputs against an independently implemented 12-base deterministic Miller–Rabin checker. The sum of prime counts over the fifteen unique seed/workload sets was 31,942. Additional arithmetic checks compared every packet remainder and detected divisor to direct arithmetic on 20,000 random words, 512 inputs at the top of the word range and neighborhoods of large multiples. The ordinary entry point and forced portable branch also matched FLINT on 12,000 additional mixed-width inputs each.

Each method receives a warm-up pass. Four-treatment Williams orders balance positions and predecessor treatments every four rounds. The timed region is an indirect-call loop over the same values for each method and checks the prime count after each pass. It excludes generating words and building or validating the functions. [Benchmark and reference checks](packet_benchmark.cpp)

Run from this directory on ARM64. The parent instructions identify the matching FLINT library. The new CSV is written under the temporary directory to preserve the published measurements. [FLINT setup](../README.md)

~~~sh
clang++ -std=c++17 -O3 -mcpu=native packet_benchmark.cpp -o /tmp/prime-packet
/tmp/prime-packet /path/to/libflint.dylib > /tmp/prime-packet-results.csv
shasum -a 256 results.csv
~~~

The saved 180-row measurement file has SHA-256 `c762c1f2fa84ff785859361e5e78775082ba2d826d85c9d9e34dcb69dc4d435c`. Fresh timings will vary.

## Repeat timing session

A fresh compilation ran the same three input seeds again on the same M4 and library. All 180 rows matched the original seed, input count, round and verified prime count. For uniform odd words the public FLINT, earlier prescreen, matched scalar and packet methods took 127.13, 108.47, 110.10 and 103.74 ns respectively. For products of large primes, the public and packet methods took 442.82 and 501.27 ns. The new session measures timing variation on the same inputs. [Repeat measurements](replication.csv)
