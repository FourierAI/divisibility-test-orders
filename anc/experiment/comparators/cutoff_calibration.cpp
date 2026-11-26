// clang++ -std=c++17 -O3 -mcpu=native cutoff_calibration.cpp -o calibrate
// Run with the 64-bit FLINT library, an integer seed, and "u64" or "odd48".
#include "../prime_screen.hpp"
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <dlfcn.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

using Word = std::uint64_t;
using Test = prime_screen::Test;
constexpr std::array<unsigned,9> cutoffs = {0,28,64,124,188,252,380,508,764};
constexpr unsigned capacity = cutoffs.back();
static std::array<unsigned,capacity> primes;
static std::array<Word,capacity> inverse, limit;
static Test backend, ordinary;
static volatile Word sink;
static Word state;
struct Interval {Word min_even, max_odd;};

static Word random_word() {
    Word z = (state += UINT64_C(0x9e3779b97f4a7c15));
    z = (z ^ (z >> 30))*UINT64_C(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27))*UINT64_C(0x94d049bb133111eb);
    return z ^ (z >> 31);
}
static Word uniform_below(Word n) {
    const Word threshold = -n % n;
    Word x;
    do x = random_word(); while (x < threshold);
    return x % n;
}
static void setup() {
    unsigned used = 0;
    for (unsigned p=17; used<capacity; p+=2) {
        bool prime = true;
        for (unsigned d=3; d*d<=p; d+=2)
            if (p%d == 0) {prime=false; break;}
        if (!prime) continue;
        Word v=1;
        for (unsigned j=0; j<6; ++j) v *= 2-Word(p)*v;
        primes[used]=p; inverse[used]=v; limit[used]=UINT64_MAX/p;
        ++used;
    }
}
static bool divides(Word n,unsigned i) { return n*inverse[i] <= limit[i]; }
static bool rejected(Word n,unsigned k) {
    if (!prime_screen::wheel[n%prime_screen::wheel_modulus]) return true;
    for (unsigned i=0;i<k;i+=4)
        if (divides(n,i)|divides(n,i+1)|divides(n,i+2)|divides(n,i+3)) return true;
    return false;
}
template <unsigned k> static int filter(unsigned long n) { return rejected(n,k); }
template <unsigned k> static int full(unsigned long n) {
    return rejected(n,k) ? 0 : backend(n);
}
template <bool include_backend,std::size_t... i>
static constexpr auto functions(std::index_sequence<i...>) {
    return std::array<Test,sizeof...(i)>{
        (include_backend ? full<cutoffs[i]> : filter<cutoffs[i]>)...};
}
static constexpr auto filters=functions<false>(std::make_index_sequence<cutoffs.size()>{});
static constexpr auto full_tests=functions<true>(std::make_index_sequence<cutoffs.size()>{});
static std::vector<Word> odd_uniform(std::size_t size,const Interval& interval) {
    std::vector<Word> words;
    words.reserve(size);
    while (words.size()<size) {
        Word n=random_word() | 1;
        if (interval.max_odd<UINT64_MAX) n=(n&interval.max_odd)|interval.min_even;
        if (n>interval.min_even) words.push_back(n);
    }
    return words;
}
static double median(std::vector<double> a) {
    std::sort(a.begin(),a.end());
    return a[a.size()/2];
}
__attribute__((noinline))
static double timed(const std::vector<Word>& words,Test f) {
    const auto start=std::chrono::steady_clock::now();
    Word count=0;
    for (const Word n:words) count += f(n);
    const auto elapsed=std::chrono::steady_clock::now()-start;
    sink=count;
    return std::chrono::duration<double,std::nano>(elapsed).count()/words.size();
}
struct Band {
    double proposal_mass=0, newly_rejected=0, fallback_ns=0;
    std::vector<Word> misses_saved;
};
static Band sample_band(unsigned begin,unsigned end,unsigned proposals,const Interval& interval) {
    std::vector<Word> starts, cumulative;
    Word total=0;
    for (unsigned i=begin;i<end;++i) {
        const Word p=primes[i];
        Word first=(interval.min_even+p-1)/p;
        first |= 1;
        const Word upper=interval.max_odd/p;
        const Word count=(upper-first)/2+1;
        if (UINT64_MAX-total<count) throw std::runtime_error("proposal mass overflow");
        starts.push_back(first);
        cumulative.push_back(total+=count);
    }
    Band band;
    const Word sample_size=(interval.max_odd-interval.min_even)/2+1;
    band.proposal_mass=static_cast<double>(total)/sample_size;
    for (unsigned draw=0;draw<proposals;++draw) {
        const Word ticket=uniform_below(total);
        const auto idx=std::upper_bound(cumulative.begin(),cumulative.end(),ticket)-cumulative.begin();
        const Word within=ticket-(idx?cumulative[idx-1]:0);
        const unsigned i=begin+static_cast<unsigned>(idx);
        const Word n=Word(primes[i])*(starts[idx]+2*within);
        if (n<interval.min_even || n>interval.max_odd || (n&1)==0 || n%primes[i])
            throw std::runtime_error("invalid sampled multiple");
        if (!prime_screen::wheel[n%prime_screen::wheel_modulus]) continue;
        bool first_hit=true;
        for (unsigned j=0;j<i;++j)
            if (divides(n,j)) {first_hit=false;break;}
        if (first_hit) band.misses_saved.push_back(n);
    }
    if (band.misses_saved.empty()) throw std::runtime_error("empty stratum");
    band.newly_rejected=band.proposal_mass*band.misses_saved.size()/proposals;
    return band;
}
static std::vector<double> measure_group(const std::vector<Word>& words,
                                        const std::array<Test,cutoffs.size()>& fun,
                                        bool verify) {
    std::array<std::vector<double>,cutoffs.size()> timers;
    for (auto f:fun) timed(words,f);
    const unsigned offset=uniform_below(fun.size());
    // Rotation balances position, with independently chosen direction per run.
    const unsigned step=(random_word()&1) ? 1 : fun.size()-1;
    for (unsigned r=0;r<fun.size();++r) {
        for (unsigned t=0;t<fun.size();++t) {
            const unsigned i=(offset+(r+t)*step)%fun.size();
            timers[i].push_back(timed(words,fun[i]));
        }
    }
    if (verify) {
        for (Word n:words) {
            const bool prime = ordinary(n);
            for (auto f:fun) if (bool(f(n))!=prime) throw std::runtime_error("result mismatch");
        }
    }
    std::vector<double> values;
    for (auto& v:timers) values.push_back(median(v));
    return values;
}
int main(int argc,char** argv) {
    if (argc!=4) {std::fprintf(stderr,"usage: calibrate LIBFLINT SEED u64|odd48\n");return 2;}
    void* handle=dlopen(argv[1],RTLD_LOCAL|RTLD_NOW);
    if (!handle) {std::fprintf(stderr,"%s\n",dlerror());return 2;}
    backend=reinterpret_cast<Test>(dlsym(handle,"n_is_prime_odd_no_trial"));
    ordinary=reinterpret_cast<Test>(dlsym(handle,"n_is_prime"));
    if (!backend||!ordinary) return 2;
    const Word seed=std::stoull(argv[2]);
    const std::string workload=argv[3];
    if (workload!="u64" && workload!="odd48") return 2;
    const Interval interval = workload=="u64"
        ? Interval{UINT64_C(1)<<32,UINT64_MAX}
        : Interval{UINT64_C(1)<<47,(UINT64_C(1)<<48)-1};
    state=seed;
    setup();
    constexpr unsigned proposals=65536;
    const auto training=odd_uniform(131072,interval);
    // Generate the independent validation set before training changes RNG use.
    const auto validation=odd_uniform(196608,interval);
    const auto screen_ns=measure_group(training,filters,false);
    std::array<Band,cutoffs.size()> bands;
    for (unsigned i=1;i<cutoffs.size();++i) {
        bands[i]=sample_band(cutoffs[i-1],cutoffs[i],proposals,interval);
        std::vector<double> times;
        timed(bands[i].misses_saved,backend);
        for (unsigned r=0;r<7;++r) times.push_back(timed(bands[i].misses_saved,backend));
        if (sink!=0) throw std::runtime_error("exact composite accepted");
        bands[i].fallback_ns=median(times);
    }
    const auto full_ns=measure_group(validation,full_tests,true);
    std::puts("seed,workload,cutoff,largest,proposal_mass,new_hit,accepted,backend_on_hit_ns,screen_ns,predicted_delta_ns,heldout_ns");
    double saving=0;
    for (unsigned i=0;i<cutoffs.size();++i) {
        saving+=bands[i].newly_rejected*bands[i].fallback_ns;
        std::printf("%llu,%s,%u,%u,%.9f,%.9f,%zu,%.4f,%.4f,%.4f,%.4f\n",
                    static_cast<unsigned long long>(seed),workload.c_str(),cutoffs[i],cutoffs[i]?primes[cutoffs[i]-1]:13,
                    bands[i].proposal_mass,bands[i].newly_rejected,bands[i].misses_saved.size(),
                    bands[i].fallback_ns,screen_ns[i],screen_ns[i]-screen_ns[0]-saving,full_ns[i]);
    }
}
