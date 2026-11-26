"""Check two density radii on the same finite prime menu and word interval."""

from fractions import Fraction
from math import isqrt, log


def make_menu(size, lower):
    limit = 2 * lower
    sieve = bytearray([1]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytes((limit - p * p) // p + 1)
    primes = []
    last = lower
    for index in range(size):
        spacing = (lower - 18 * size) * (size + 8 * index) // (5 * size**2)
        candidate = last + spacing
        while candidate <= limit and not sieve[candidate]:
            candidate += 1
        if candidate > limit:
            raise ValueError("Interval has too few primes at these spacings")
        primes.append(candidate)
        last = candidate
    return primes


def odd_count(length, modulus):
    def through(bound):
        return (bound // modulus + 1) // 2

    return through(4 * length - 1) - through(2 * length - 1)


def physical_gain(primes, index, length, radius):
    left, right = primes[index : index + 2]
    total_left = sum(odd_count(length, p * left) for p in primes[:index])
    total_right = sum(odd_count(length, p * right) for p in primes[:index])
    lower = Fraction(1, left) - Fraction(1, right) - Fraction(2, length)
    return lower - ((1 + radius) * total_left - (1 - radius) * total_right) / length


def check_radius(primes, lower, radius):
    a, b = radius.as_integer_ratio()
    threshold = (4000 * lower**2 * b + a - 1) // a
    length = 1 << (threshold - 1).bit_length()
    assert 4 * length < lower**3
    scale = 1 << 100
    prefix_lower = 0
    safe = failed = exact_counts = ties = 0
    witness = None
    for i, (p, q) in enumerate(zip(primes, primes[1:])):
        # The sum of previous reciprocal primes is in this scaled interval.
        prefix_upper = prefix_lower + i
        product = p * q
        numerator = length * b * (q - p) * scale - 2 * b * product * scale
        slope = length * (b * (q - p) + a * (q + p))
        error = 2 * (a + b) * i * product * scale
        if numerator - slope * prefix_upper > error:
            safe += 1
        elif numerator - slope * prefix_lower < -error:
            failed += 1
            if witness is None:
                witness = i
        else:
            exact_counts += 1
            gain = physical_gain(primes, i, length, radius)
            if gain > 0:
                safe += 1
            elif gain < 0:
                failed += 1
                if witness is None:
                    witness = i
            else:
                ties += 1
        prefix_lower += scale // p
    if witness is not None:
        gain = physical_gain(primes, witness, length, radius)
        assert gain < 0
        print(f"First certified reversal at rank {witness + 1}, "
              f"primes {primes[witness:witness + 2]}, saving {-gain} tests per word")
    print(f"eps={radius}, L=2^{length.bit_length()-1}, positive={safe}, "
          f"negative={failed}, ties={ties}, exact row sums needed={exact_counts}")
    return length, safe, failed


if __name__ == "__main__":
    size, lower = 32_768, 6_800_000
    assert 10 * size * log(size) < lower < 20 * size * log(size)
    menu = make_menu(size, lower)
    small = check_radius(menu, lower, Fraction(3, 1000))
    large = check_radius(menu, lower, Fraction(4, 1000))
    assert small[0] == large[0] and small[1] == size - 1 and large[2] > 0
