#pragma once

#include "../packet_screen/packet.hpp"
#include <algorithm>
#include <array>
#include <cstdint>
#include <limits>
#include <numeric>
#include <utility>

namespace learned_order {
using prime_screen::Test;
using prime_screen::Word;
inline constexpr unsigned size = 12;
inline constexpr unsigned states = 1u << size;
inline constexpr unsigned all = states - 1;
inline constexpr std::array<unsigned, size> primes{
    1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733};
using Order = std::array<unsigned, size>;
using Census = std::array<std::uint64_t, states>;
struct Divisor { Word inverse, limit; };
using Schedule = std::array<Divisor, size>;

constexpr Schedule divisors() {
    Schedule result{};
    for (unsigned i = 0; i < size; ++i) {
        Word inverse = 1;
        for (unsigned round = 0; round < 6; ++round)
            inverse *= 2 - Word(primes[i]) * inverse;
        result[i] = {inverse, UINT64_MAX / primes[i]};
    }
    return result;
}
inline constexpr Schedule menu = divisors();
inline unsigned hit_mask(Word n) {
    unsigned mask = 0;
    for (unsigned i = 0; i < size; ++i)
        mask |= unsigned(n * menu[i].inverse <= menu[i].limit) << i;
    return mask;
}
inline Order increasing() {
    Order order{};
    std::iota(order.begin(), order.end(), 0u);
    return order;
}
inline Schedule prepare(const Order& order) {
    Schedule result{};
    for (unsigned i = 0; i < size; ++i) result[i] = menu[order[i]];
    return result;
}
inline int is_prime(Word n, const Schedule& schedule, Test ordinary, Test odd_after_screen) {
    if (n <= UINT32_MAX) return ordinary(n);
    for (const auto& divisor : schedule)
        if (n * divisor.inverse <= divisor.limit) return 0;
    return prime_screen::packet::is_prime(n, ordinary, odd_after_screen);
}
template<std::size_t... I>
inline bool hits_batch(Word n, const Schedule& schedule, std::index_sequence<I...>) {
    return (unsigned(n * schedule[I].inverse <= schedule[I].limit) | ...);
}
template<std::size_t width, class Fallback>
inline __attribute__((always_inline)) int is_prime_batch(
        Word n, const Schedule& schedule, Fallback fallback) {
    static_assert(width > 0 && width <= size);
    if (n > UINT32_MAX && hits_batch(n, schedule, std::make_index_sequence<width>{})) return 0;
    return fallback(n);
}
inline Order fit_marginals(const Census& frequency) {
    std::array<std::uint64_t, size> hits{};
    for (unsigned mask = 1; mask < states; ++mask) {
        if (!frequency[mask]) continue;
        for (unsigned bits = mask; bits; bits &= bits - 1)
            hits[__builtin_ctz(bits)] += frequency[mask];
    }
    auto order = increasing();
    std::stable_sort(order.begin(), order.end(), [&](unsigned i, unsigned j) {
        return hits[i] > hits[j];
    });
    return order;
}
inline Order fit_residual_greedy(const Census& frequency) {
    std::array<unsigned short, states> active;
    unsigned count = 0, remaining = all;
    for (unsigned mask = 1; mask < states; ++mask)
        if (frequency[mask]) active[count++] = static_cast<unsigned short>(mask);
    Order order{};
    for (auto& choice : order) {
        std::array<std::uint64_t, size> hits{};
        for (unsigned j = 0; j < count; ++j) {
            const auto mask = active[j];
            for (unsigned bits = mask; bits; bits &= bits - 1)
                hits[__builtin_ctz(bits)] += frequency[mask];
        }
        choice = __builtin_ctz(remaining);
        for (unsigned bits = remaining; bits; bits &= bits - 1) {
            const unsigned i = __builtin_ctz(bits);
            if (hits[i] > hits[choice]) choice = i;
        }
        const unsigned selected = 1u << choice;
        remaining ^= selected;
        unsigned kept = 0;
        for (unsigned j = 0; j < count; ++j)
            if (!(active[j] & selected)) active[kept++] = active[j];
        count = kept;
    }
    return order;
}
// Under the two-hit training laws the histogram is exactly the empty-cell
// count and the pair counts. Under general laws this DP uses the full mask.
inline Order fit_joint(const Census& frequency) {
    Census subsets = frequency, cost{};
    std::array<unsigned char, states> next{};
    for (unsigned i = 0; i < size; ++i)
        for (unsigned mask = 0; mask < states; ++mask)
            if (mask & (1u << i)) subsets[mask] += subsets[mask ^ (1u << i)];
    for (unsigned remaining = 1; remaining < states; ++remaining) {
        auto best = std::numeric_limits<std::uint64_t>::max();
        for (unsigned bits = remaining; bits; bits &= bits - 1) {
            const unsigned i = __builtin_ctz(bits);
            const auto candidate = cost[remaining ^ (1u << i)];
            if (candidate < best) { best = candidate; next[remaining] = i; }
        }
        // Charge one probe for every row whose entire mask remains untested.
        cost[remaining] = subsets[remaining] + best;
    }
    Order result{};
    unsigned remaining = all;
    for (auto& i : result) { i = next[remaining]; remaining ^= 1u << i; }
    return result;
}
} // namespace learned_order
