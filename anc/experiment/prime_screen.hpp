#pragma once

#include <array>
#include <cstddef>
#include <cstdint>
#include <limits>

// Exact single-word filter for use with FLINT 3.6.0 (64-bit limbs).
// Both backends return a proved yes/no result on the domain where called.
namespace prime_screen {
using Word = std::uint64_t;
using Test = int (*)(unsigned long);
static_assert(sizeof(unsigned long) == sizeof(Word), "64-bit FLINT limbs required");
inline constexpr unsigned wheel_modulus = 3 * 5 * 7 * 11 * 13;
inline constexpr std::size_t extra_primes = 252;

constexpr auto make_wheel() {
    std::array<unsigned char, wheel_modulus> allowed{};
    for (unsigned r = 0; r < allowed.size(); ++r)
        allowed[r] = r % 3 && r % 5 && r % 7 && r % 11 && r % 13;
    return allowed;
}

struct Screen {
    std::array<unsigned, extra_primes> prime{};
    std::array<Word, extra_primes> inverse{}, limit{};
};
constexpr auto make_screen() {
    Screen filter{};
    std::size_t count = 0;
    for (unsigned p = 17; count < extra_primes; p += 2) {
        bool prime = true;
        for (unsigned d = 3; d * d <= p; d += 2) {
            if (p % d == 0) { prime = false; break; }
        }
        if (!prime) continue;
        Word v = 1;
        // Newton iteration doubles the number of correct low bits each time.
        for (int k = 0; k < 6; ++k) v *= Word{2} - p * v;
        filter.prime[count] = p;
        filter.inverse[count] = v;
        filter.limit[count] = std::numeric_limits<Word>::max() / p;
        ++count;
    }
    return filter;
}
inline constexpr auto wheel = make_wheel();
inline constexpr auto screen = make_screen();
static_assert(extra_primes % 4 == 0);

inline bool small_factor(Word n) {
    if ((n & 1u) == 0 || !wheel[n % wheel_modulus]) return true;
    for (std::size_t i = 0; i < extra_primes; i += 4) {
        // Bitwise OR lets the four independent multiplications proceed in parallel.
        if ((n * screen.inverse[i] <= screen.limit[i]) |
            (n * screen.inverse[i+1] <= screen.limit[i+1]) |
            (n * screen.inverse[i+2] <= screen.limit[i+2]) |
            (n * screen.inverse[i+3] <= screen.limit[i+3])) return true;
    }
    return false;
}

inline int is_prime(Word n, Test ordinary, Test odd_after_screen) {
    if (n <= UINT32_MAX) return ordinary(n);
    if (small_factor(n)) return 0;
    return odd_after_screen(n);
}
}  // namespace prime_screen
