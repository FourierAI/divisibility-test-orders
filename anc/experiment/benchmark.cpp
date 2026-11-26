// Build: clang++ -std=c++17 -O3 -mcpu=native benchmark.cpp -o benchmark
// Run: ./benchmark /path/to/libflint.dylib [seed] (on Linux link with -ldl).
#include "prime_screen.hpp"
#include "packet_screen/packet.hpp"
#include <algorithm>
#include <chrono>
#include <charconv>
#include <cstring>
#include <cstdio>
#include <cstdlib>
#include <dlfcn.h>
#include <stdexcept>
#include <string>
#include <vector>

using prime_screen::Word;
using prime_screen::Test;
static Test baseline, odd_after_screen;
static volatile std::uint64_t consumed;
static Word state;
static Word random_word() {
    Word z = (state += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}
static int candidate(unsigned long n) { return prime_screen::is_prime(n,baseline,odd_after_screen); }

// Independent exact reference below 2^64: first 12 prime Miller-Rabin bases.
// Sorenson & Webster, Math. Comp. 86 (2017), doi:10.1090/mcom/3134.
static Word mul_mod(Word a, Word b, Word n) { return static_cast<__uint128_t>(a)*b % n; }
static bool reference(Word n) {
    constexpr unsigned primes[] = {2,3,5,7,11,13,17,19,23,29,31,37};
    if (n < 2) return false;
    for (unsigned p : primes) if (n % p == 0) return n == p;
    const unsigned s = __builtin_ctzll(n-1);
    const Word d = (n-1) >> s;
    for (unsigned p : primes) {
        Word x = 1, a = p;
        for (Word e=d; e; e>>=1) {
            if (e&1) x = mul_mod(x,a,n);
            a = mul_mod(a,a,n);
        }
        if (x==1 || x==n-1) continue;
        bool passed=false;
        for (unsigned j=1; j<s; ++j) {
            x=mul_mod(x,x,n);
            if (x==n-1) { passed=true; break; }
        }
        if (!passed) return false;
    }
    return true;
}
static void check(Word n, bool expected) {
    if ((baseline(n)!=0)!=expected || (candidate(n)!=0)!=expected)
        throw std::runtime_error("disagreement at " + std::to_string(n));
}
static void validate_boundaries() {
    std::vector<bool> sieve(1000001,true);
    sieve[0]=sieve[1]=false;
    for (unsigned p=2; p*p<sieve.size(); ++p) if (sieve[p])
        for (unsigned j=p*p; j<sieve.size(); j+=p) sieve[j]=false;
    for (unsigned n=0;n<sieve.size();++n) check(n,sieve[n]);
    for (int offset=-128;offset<=128;++offset) {
        Word n=(Word{1}<<32)+offset; check(n,reference(n));
    }
    for (unsigned d=0;d<256;++d) { Word n=UINT64_MAX-d; check(n,reference(n)); }
    for (auto p:prime_screen::screen.prime) {
        Word top=(UINT64_MAX/p)*p;
        for (Word n:{top-1,top,top+1}) check(n,reference(n));
        if (!prime_screen::small_factor(top)) throw std::runtime_error("missed divisor");
    }
    for (Word n:{UINT64_C(2047),UINT64_C(3215031751),UINT64_C(341550071728321),
                 UINT64_C(3825123056546413051),UINT64_C(18446744073709551557)}) check(n,reference(n));
}
static Word next_prime32() {
    Word p=(random_word() & UINT64_C(0x7fffffff)) | UINT64_C(0x80000001);
    while (p <= UINT32_MAX && !baseline(p)) p+=2;
    return p<=UINT32_MAX ? p : UINT64_C(4294967291);
}

enum class Sample { uniform, odd, odd48, prime, semiprime, small };
static std::vector<Word> sample(Sample type,std::size_t size) {
    std::vector<Word> a;
    a.reserve(size);
    while (a.size()<size) {
        Word n=random_word();
        switch(type) {
            case Sample::uniform: break;
            case Sample::odd: n |= 1; break;
            case Sample::odd48: n=(n & ((Word{1}<<48)-1)) | (Word{1}<<47) | 1; break;
            case Sample::prime: n |= (Word{1}<<63)|1; if (!baseline(n)) continue; break;
            case Sample::semiprime: {const Word p=next_prime32(); const Word q=next_prime32(); n=p*q; break;}
            case Sample::small: n=static_cast<std::uint32_t>(n); break;
        }
        a.push_back(n);
    }
    return a;
}
static double time_call(const std::vector<Word>& a,Test f) {
    using Clock=std::chrono::steady_clock;
    std::uint64_t total=0;
    auto start=Clock::now();
    for (Word n:a) total+=f(n);
    auto end=Clock::now();
    consumed=total;
    return std::chrono::duration<double,std::nano>(end-start).count()/a.size();
}
static double median(std::vector<double> v) {
    std::sort(v.begin(),v.end()); return v[v.size()/2];
}
static void measure(const char* name,Sample kind,std::size_t size) {
    auto a=sample(kind,size);
    std::size_t primes=0;
    for (Word n:a) {bool expected=reference(n);check(n,expected);primes+=expected;}
    time_call(a,baseline); time_call(a,candidate);  // Warm both paths before paired trials.
    std::vector<double> old_times,new_times,ratios;
    for (unsigned i=0;i<11;i++) {
        double before,after;
        if (i%2) {before=time_call(a,baseline); after=time_call(a,candidate);}
        else {after=time_call(a,candidate); before=time_call(a,baseline);}
        old_times.push_back(before); new_times.push_back(after); ratios.push_back(before/after);
    }
    std::printf("%-15s %7zu %7zu %10.2f %10.2f %8.3f\n",name,size,primes,median(old_times),median(new_times),median(ratios));
    std::fflush(stdout);
}
// FLINT 3.6 uses a signed word as the fmpz handle on this 64-bit ABI.
// Use only its public lifetime, parsing and exact-primality operations.
static int classify_decimal(void* library,const char* text) {
    const char* end=text+std::strlen(text);
    const char* digits=text;
    if (*digits=='-' || *digits=='+') ++digits;
    if (digits==end || !std::all_of(digits,end,[](char c){return c>='0' && c<='9';}))
        throw std::invalid_argument("expected a decimal integer");
    if (*text=='-') return 0;
    Word value=0;
    auto parsed=std::from_chars(digits,end,value);
    if (parsed.ec == std::errc{}) {
        return prime_screen::packet::is_prime(value, baseline, odd_after_screen);
    }
    using Handle=long;
    auto init=reinterpret_cast<void (*)(Handle*)>(dlsym(library,"fmpz_init"));
    auto clear=reinterpret_cast<void (*)(Handle*)>(dlsym(library,"fmpz_clear"));
    auto set=reinterpret_cast<int (*)(Handle*,const char*,int)>(dlsym(library,"fmpz_set_str"));
    auto test=reinterpret_cast<int (*)(const Handle*)>(dlsym(library,"fmpz_is_prime"));
    if (!init || !clear || !set || !test) throw std::runtime_error("missing FLINT integer API");
    Handle big;
    init(&big);
    if (set(&big,digits,10)!=0) {clear(&big);throw std::invalid_argument("invalid integer");}
    int result=test(&big);
    clear(&big);
    return result;
}
int main(int argc,char** argv) {
    if (argc<2) {std::fprintf(stderr,"usage: benchmark LIBFLINT [seed | --check INTEGER]\n");return 2;}
    void* h=dlopen(argv[1],RTLD_NOW);
    if (!h) {std::fprintf(stderr,"%s\n",dlerror()); return 2;}
    baseline=reinterpret_cast<Test>(dlsym(h,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(h,"n_is_prime_odd_no_trial"));
    const char* version=static_cast<const char*>(dlsym(h,"flint_version"));
    if (!baseline || !odd_after_screen || !version) {std::fprintf(stderr,"Required FLINT API unavailable\n");return 2;}
    if (argc>=3 && std::string(argv[2])=="--check") {
        if (argc!=4) {std::fprintf(stderr,"expected one decimal integer\n"); return 2;}
        try {std::puts(classify_decimal(h,argv[3]) ? "prime" : "not prime");}
        catch (const std::exception& err) {std::fprintf(stderr,"%s\n",err.what());return 2;}
        return 0;
    }
    state=argc>2 ? std::stoull(argv[2]) : UINT64_C(89258713);
    std::printf("FLINT %s, seed %llu, screen through %u, 11 paired timing runs per set\n",version,(unsigned long long)state,prime_screen::screen.prime.back());
    validate_boundaries();
    std::puts("sample                n   prime   FLINT_ns  method_ns   paired_x");
    measure("uniform-u64", Sample::uniform, 100000);
    measure("uniform-odd-u64",Sample::odd,100000);
    measure("random-odd48", Sample::odd48,50000);
    measure("primes-64bit",Sample::prime,5000);
    measure("semiprimes",Sample::semiprime,5000);
    measure("uniform-u32", Sample::small,50000);
    std::puts("All independent reference and boundary checks passed.");
    return 0;
}
