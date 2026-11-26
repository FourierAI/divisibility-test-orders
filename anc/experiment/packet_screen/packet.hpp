#pragma once

#include "../prime_screen.hpp"
#include <utility>

#if defined(__aarch64__) && defined(__ARM_NEON)
#include <arm_neon.h>

namespace prime_screen::packet {

inline constexpr unsigned scalar_prefix = 64;
constexpr unsigned last = prime_screen::extra_primes;

struct Row {
    alignas(16) uint32_t modulus[4]{}, inverse[3][4]{}, cutoff[3][4]{};
    Word reciprocal[4]{};
    unsigned first = 0, length = 0;
};

struct Table {
    std::array<Row, 32> rows{};
    unsigned used = 0;
};

constexpr Table make_table() {
    Table table{};
    unsigned next = scalar_prefix;
    while (next < last) {
        auto& row = table.rows[table.used++];
        row.first = next;
        for (unsigned lane = 0; lane < 4; ++lane) {
            const unsigned begin = next;
            uint32_t modulus = 1;
            while (next < last && next - begin < 3 &&
                   modulus <= (UINT32_MAX / 2) / screen.prime[next]) {
                modulus *= screen.prime[next++];
            }

            // An incomplete packet repeats a prime in spare slots. A missing
            // lane in the final row repeats the last prime in the whole menu.
            if (next == begin) modulus = screen.prime[last - 1];
            row.modulus[lane] = modulus;
            row.reciprocal[lane] = UINT64_MAX / modulus;
            for (unsigned slot = 0; slot < 3; ++slot) {
                unsigned index = begin;
                if (next == begin) {
                    index = last - 1;
                } else if (slot < next - begin) {
                    index = begin + slot;
                }
                row.inverse[slot][lane] = static_cast<uint32_t>(screen.inverse[index]);
                row.cutoff[slot][lane] = UINT32_MAX / screen.prime[index];
            }
        }
        row.length = next - row.first;
    }
    return table;
}

inline constexpr auto table = make_table();
constexpr unsigned max_rows = table.used;

inline uint32x4_t reduced(Word n, const Row& row) {
    // The approximate remainder is in [0, 2M), fits 32 bits, and is
    // congruent to n modulo M. Its formation only needs the low quotient.
    uint32_t quotient[4];
    for (unsigned lane = 0; lane < 4; ++lane) {
        quotient[lane] = static_cast<uint32_t>(
            (__uint128_t(n) * row.reciprocal[lane]) >> 64);
    }
    return vmlsq_u32(vdupq_n_u32(static_cast<uint32_t>(n)),
                     vld1q_u32(quotient), vld1q_u32(row.modulus));
}

inline bool packed_suffix(Word n) {
    for (unsigned index = 0; index < max_rows; ++index) {
        const auto& row = table.rows[index];
        const uint32x4_t residues = reduced(n, row);
        uint32x4_t hits = vdupq_n_u32(0);
        for (unsigned slot = 0; slot < 3; ++slot) {
            const auto products = vmulq_u32(residues, vld1q_u32(row.inverse[slot]));
            hits = vorrq_u32(hits, vcleq_u32(products, vld1q_u32(row.cutoff[slot])));
        }
        if (vmaxvq_u32(hits)) return true;
    }
    return false;
}

template<std::size_t... Offset>
inline bool raw_batch(Word n, unsigned first, std::index_sequence<Offset...>) {
    return ((n * screen.inverse[first + Offset] <= screen.limit[first + Offset]) | ...);
}

inline bool prefix_rejects(Word n) {
    if (!(n & 1) || !wheel[n % wheel_modulus]) return true;
    for (unsigned i = 0; i < scalar_prefix; i += 4) {
        if (raw_batch(n, i, std::make_index_sequence<4>{})) return true;
    }
    return false;
}

inline int is_prime(Word n, Test ordinary, Test odd_after_screen) {
    if (n <= UINT32_MAX) return ordinary(n);
    if (prefix_rejects(n) || packed_suffix(n)) return 0;
    return odd_after_screen(n);
}

} // namespace prime_screen::packet

#else

namespace prime_screen::packet {

inline int is_prime(Word n, Test ordinary, Test odd_after_screen) {
    return prime_screen::is_prime(n, ordinary, odd_after_screen);
}

} // namespace prime_screen::packet

#endif
