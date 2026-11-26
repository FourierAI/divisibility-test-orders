#define main original_benchmark_main
#include "benchmark.cpp"
#undef main
// Controls use the same bit-accurate modular-inverse check. The first five
// odd divisors in the non-table control are compile-time constant moduli.
template <unsigned cutoff, bool use_wheel, bool grouped>
static int alternative(unsigned long n) {
    if (n <= UINT32_MAX) return baseline(n);
    if (!(n & 1)) return 0;
    if constexpr (use_wheel) {
        if (!prime_screen::wheel[n % 15015]) return 0;
    } else if (!(n % 3) || !(n % 5) || !(n % 7) || !(n % 11) || !(n % 13)) return 0;
    constexpr std::size_t limit=[]() constexpr {
        std::size_t k=0;
        while (k < prime_screen::extra_primes && prime_screen::screen.prime[k]<=cutoff) ++k;
        return k;
    }();
    auto divides=[n](std::size_t i){ return n * prime_screen::screen.inverse[i] <= prime_screen::screen.limit[i]; };
    std::size_t i=0;
    if constexpr(grouped) for(;i+4<=limit;i+=4) if (divides(i)|divides(i+1)|divides(i+2)|divides(i+3)) return 0;
    for(;i<limit;++i) if(divides(i)) return 0;
    return odd_after_screen(n);
}
int main(int argc,char** argv){
    if(argc!=2)return 2;
    auto h=dlopen(argv[1],RTLD_NOW); if(!h)return 2;
    baseline=reinterpret_cast<Test>(dlsym(h,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(h,"n_is_prime_odd_no_trial"));
    if (!baseline || !odd_after_screen)return 2;
    Test fs[]={baseline,alternative<149,false,false>,alternative<1627,false,false>,alternative<1627,true,false>,alternative<1627,false,true>,candidate};
    const char* names[]={"FLINT","scalar149","scalar1627","table_scalar1627","grouped1627","full"};
    for (Word seed:{91233273UL,41797637UL,69420123UL}){
        state=seed; auto a=sample(Sample::odd,100000);
        for(auto n:a){ bool expected=reference(n);for (auto f:fs)if(bool(f(n))!=expected)return 1;}
        std::array<std::vector<double>,6> times;
        for(auto f:fs)time_call(a,f);
        for(unsigned round=0;round<12;++round)for(unsigned j=0;j<6;++j){
            unsigned k=round<6?(j+round)%6:(round+6-j)%6;
            times[k].push_back(time_call(a,fs[k]));
        }
        std::printf("seed %lu", (unsigned long)seed);
        for(unsigned k=0;k<6;++k)std::printf("  %s=%.2f",names[k],median(times[k]));
        std::puts(" ns/input");std::fflush(stdout);
    }
}
