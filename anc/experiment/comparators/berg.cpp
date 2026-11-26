// Fixed-width port of the deterministic witness schedule published in
// zmwangx/miller-rabin 1.0.1. The generated header retains the upstream
// divisibility tests and Bradley Berg's tables. See build_berg.py.
#include <cstdint>
#include "berg_tables.h"

using Word = std::uint64_t;
using Wide = __uint128_t;

// Montgomery reduction with the positive inverse of the odd modulus.
// a*b and (low(a*b)*inverse mod 2^64)*n have the same low word.
// Their high-word difference therefore equals the signed exact quotient by
// 2^64 and lies in (-n,n). An unsigned borrow selects the correction.
struct Montgomery {
    Word n;
    Word inverse;
    Word one;
    unsigned squarings;
    Word odd_exponent;

    explicit Montgomery(Word modulus)
        : n(modulus), inverse((3*modulus) ^ 2), one((-modulus) % modulus),
          squarings(__builtin_ctzll(modulus-1)), odd_exponent((modulus-1) >> squarings) {
        for (unsigned i=0; i<4; ++i) inverse *= 2-n*inverse;
    }

    Word multiply(Word a, Word b) const {
        Wide product = static_cast<Wide>(a) * b;
        Word high = static_cast<Word>(product >> 64);
        Word mask = static_cast<Word>(product) * inverse;
        Word correction = static_cast<Word>((static_cast<Wide>(mask)*n) >> 64);
        return high - correction + (high < correction ? n : 0);
    }

    Word twice(Word x) const { return x >= n-x ? x-(n-x) : x+x; }

    template<bool base_two> bool passes(Word base) const {
        const Word factor = base_two ? twice(one) : static_cast<Wide>(one)*base % n;
        Word x = factor;
        const int highest_bit = 63-__builtin_clzll(odd_exponent);
        for (int bit=highest_bit-1; bit>=0; --bit) {
            x = multiply(x,x);
            if ((odd_exponent >> bit) & 1)
                x = base_two ? twice(x) : multiply(x,factor);
        }
        if (x == one || x == n-one) return true;
        for (unsigned j=1; j<squarings; ++j) {
            x = multiply(x,x);
            if (x == n-one) return true;
        }
        return false;
    }
};

extern "C" int berg_word_prime(unsigned long input) {
    const Word n = input;
    if (!(n&1)) return n==2;
    if (n < 65536) {
        const unsigned bit = static_cast<unsigned>(n-1)/2;
        return (smallprime16[bit/32] >> (bit%32)) & 1;
    }
    if (!preliminary_test_ui(n)) return false;
    const Montgomery ring(n);
    const std::uint32_t hash = UINT32_C(0xad625b89)*static_cast<std::uint32_t>(n);
    if (n <= UINT32_MAX) return ring.passes<false>(hashtable32[hash >> 24]);
    if (!ring.passes<true>(2)) return false;
    const unsigned base = hashtable64[hash >> 18];
    return ring.passes<false>(base) &&
           (n < (UINT64_C(1)<<49) || ring.passes<false>(hashtable64_2[base >> 13]));
}
