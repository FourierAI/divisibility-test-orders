// clang++ -std=c++17 -O3 -mcpu=native rough.cpp -o rough
#define main original_benchmark_main
#include "../benchmark.cpp"
#undef main

// Each wrapper remains exact for every uint64_t; a hint only skips work.
static int public_test(unsigned long n){return baseline(n);}
static int direct(unsigned long n){
    if(n<=UINT32_MAX) return baseline(n);
    return (n&1) ? odd_after_screen(n) : 0;
}
template<unsigned seen>
static int unseen(unsigned long n){
    if(n<=UINT32_MAX) return baseline(n);
    if(!(n&1)) return 0;
    constexpr auto& s=prime_screen::screen;
    constexpr unsigned start=[](){
        unsigned i=0;
        while(i<prime_screen::extra_primes && prime_screen::screen.prime[i]<=seen) ++i;
        return i;
    }();
    if constexpr(seen<13) if(!prime_screen::wheel[n%15015]) return 0;
    unsigned i=start;
    for(;i+4<=prime_screen::extra_primes;i+=4){
        if((n*s.inverse[i]<=s.limit[i]) | (n*s.inverse[i+1]<=s.limit[i+1]) |
           (n*s.inverse[i+2]<=s.limit[i+2]) | (n*s.inverse[i+3]<=s.limit[i+3]))return 0;
    }
    for(;i<prime_screen::extra_primes;++i) if(n*s.inverse[i]<=s.limit[i]) return 0;
    return odd_after_screen(n);
}
static bool survives(Word n, unsigned floor){
    if(floor<13)return true;
    if(!prime_screen::wheel[n%15015])return false;
    for(unsigned p:prime_screen::screen.prime){
        if(p>floor) break;
        if(n%p==0)return false;
    }
    return true;
}
__attribute__((noinline)) static double round_time(const std::vector<Word>& values, Test fn){
    return time_call(values,fn);
}
static void run(Word seed,unsigned floor,unsigned hint, Test proposal){
    const unsigned N=65536;
    std::vector<Word> values;
    values.reserve(N);
    state=seed+1234521991UL*floor;
    while(values.size()<N){
        Word n=random_word()|1;
        if(n>UINT32_MAX && survives(n,floor))values.push_back(n);
    }
    std::array<Test,4> methods={public_test,candidate,direct,proposal};
    Word prime_count=0;
    for(auto n:values){
        const bool truth=reference(n);
        for(auto f:methods)if((f(n)!=0)!=truth)throw std::runtime_error("word failed reference");
        prime_count+=truth;
    }
    for(auto f:methods)round_time(values,f);
    constexpr unsigned order[4][4]={{0,1,3,2},{1,2,0,3},{2,3,1,0},{3,0,2,1}};
    for(unsigned r=0;r<12;++r){
        double t[4];
        for(auto i:order[(seed+r)%4]){
            t[i]=round_time(values,methods[i]);
            if(consumed!=prime_count)throw std::runtime_error("checksum mismatch");
        }
        std::printf("%llu,%u,%u,%u,%llu,%u,%.3f,%.3f,%.3f,%.3f\n",
                    static_cast<unsigned long long>(seed),floor,hint,N,
                    static_cast<unsigned long long>(prime_count),r,t[0],t[1],t[2],t[3]);
    }
    std::fflush(stdout);
}
int main(int argc,char**argv){
    if(argc!=2)return 2;
    auto h=dlopen(argv[1],RTLD_NOW | RTLD_LOCAL);
    if(!h)return 2;
    baseline=reinterpret_cast<Test>(dlsym(h,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(h,"n_is_prime_odd_no_trial"));
    if(!baseline||!odd_after_screen)return 2;
    std::printf("seed,prior_cutoff,hint,inputs,primes,round,flint_ns,full_screen_ns,direct_ns,unseen_ns\n");
    for(Word seed:{4811291UL,197930093UL,845116723UL}){
        run(seed,13,13,unseen<13>);
        run(seed,149,149,unseen<149>);
        run(seed,733,733,unseen<733>);
        run(seed,1627,1627,unseen<1627>);
        run(seed,0,149,unseen<149>);  // Unfiltered odd words with an inappropriate hint.
    }
}
