// Reuse the original data generator, seed progression, and 12-base reference.
// Renaming its entry point keeps the published benchmark source unchanged.
#define main original_two_method_benchmark_main
#include "../benchmark.cpp"
#undef main
#include <array>

using MpuTest = bool (*)(unsigned long);
static MpuTest mpu_test;
static Test berg_test;

static int from_mpu(unsigned long n) { return mpu_test(n); }
static int from_flint(unsigned long n) { return baseline(n); }
static int from_berg(unsigned long n) { return berg_test(n); }

template <typename F>
static F symbol(void* library, const char* name) {
    auto address = dlsym(library, name);
    if (!address) throw std::runtime_error(std::string("missing symbol ") + name);
    return reinterpret_cast<F>(address);
}

static void* open_library(const char* path) {
    auto handle = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (!handle) throw std::runtime_error(dlerror());
    return handle;
}

static void check_comparators(Word n, bool expected) {
    if (mpu_test(n) != expected)
        throw std::runtime_error("MPU disagreement at " + std::to_string(n));
    if ((berg_test(n) != 0) != expected)
        throw std::runtime_error("Berg disagreement at " + std::to_string(n));
}

static void check_comparator_edges() {
    std::vector<bool> sieve(1000001,true);
    sieve[0] = sieve[1] = false;
    for (std::size_t p = 2; p*p < sieve.size(); ++p)
        if (sieve[p]) for (std::size_t j = p*p; j < sieve.size(); j += p) sieve[j] = false;
    for (std::size_t i = 0; i < sieve.size(); ++i) check_comparators(i,sieve[i]);
    for (unsigned d = 0; d < 257; ++d) {
        Word middle = (Word{1} << 32) - 128 + d;
        check_comparators(middle, reference(middle));
        check_comparators(UINT64_MAX-d, reference(UINT64_MAX-d));
    }
    for (Word n : {UINT64_C(2047), UINT64_C(3215031751), UINT64_C(341550071728321),
                   UINT64_C(3825123056546413051), UINT64_C(18446744073709551557)})
        check_comparators(n, reference(n));
}

// One measured native indirect-call loop for all implementations.
__attribute__((noinline)) static double timed(const std::vector<Word>& values, Test test) {
    return time_call(values, test);
}

static void compare(Word seed, const char* name, Sample kind, std::size_t size) {
    const auto values = sample(kind, size);
    std::size_t prime_count = 0;
    for (Word n : values) {
        bool answer = reference(n);
        check(n, answer);
        check_comparators(n, answer);
        prime_count += answer;
    }
    const std::array<Test,4> tests = {from_flint, candidate, from_mpu, from_berg};
    for (auto f : tests) timed(values, f);
    // Williams design: each algorithm takes each position once and each
    // ordered pair of different algorithms is adjacent once in four blocks.
    constexpr std::array<std::array<unsigned,4>,4> orders =
        {{{0,1,3,2}, {1,2,0,3}, {2,3,1,0}, {3,0,2,1}}};
    for (unsigned round = 0; round < 12; ++round) {
        std::array<double,4> times{};
        for (auto i : orders[(round + seed%4)%4]) {
            times[i] = timed(values, tests[i]);
            if (consumed != prime_count) throw std::runtime_error("timing checksum mismatch");
        }
        std::printf("%llu,%s,%zu,%zu,%u,%.4f,%.4f,%.4f,%.4f\n",
                    static_cast<unsigned long long>(seed),name,size,prime_count,round,
                    times[0],times[1],times[2],times[3]);
    }
}

int main(int argc, char** argv) {
    if (argc != 4) {
        std::fprintf(stderr, "usage: native LIBFLINT LIB_MATH_PRIME_UTIL LIB_BERG_WORD\n");
        return 2;
    }
    try {
        auto flint = open_library(argv[1]);
        auto mpu = open_library(argv[2]);
        auto berg = open_library(argv[3]);
        baseline = symbol<Test>(flint,"n_is_prime");
        odd_after_screen = symbol<Test>(flint,"n_is_prime_odd_no_trial");
        mpu_test = symbol<MpuTest>(mpu,"is_prime");
        berg_test = symbol<Test>(berg,"berg_word_prime");
        symbol<void (*)(unsigned long)>(mpu,"prime_precalc")(0);
        std::fprintf(stderr,"FLINT %s, Math::Prime::Util C backend, Berg word port\n",
                     symbol<const char*>(flint,"flint_version"));
        validate_boundaries();
        check_comparator_edges();
        std::puts("seed,workload,inputs,primes,round,flint_ns,screen_ns,mpu_ns,berg_ns");
        for (Word seed : {89258713, 67430219, 39568211}) {
            state = seed;
            compare(seed,"uniform-u64",Sample::uniform,100000);
            compare(seed,"uniform-odd-u64",Sample::odd,100000);
            compare(seed,"random-odd48",Sample::odd48,50000);
            compare(seed,"primes-64bit",Sample::prime,5000);
            compare(seed,"semiprimes",Sample::semiprime,5000);
            compare(seed,"uniform-u32",Sample::small,50000);
        }
    } catch (const std::exception& e) {
        std::fprintf(stderr,"%s\n",e.what());
        return 1;
    }
    return 0;
}
