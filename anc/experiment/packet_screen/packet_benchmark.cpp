// Build on ARM64: clang++ -std=c++17 -O3 -mcpu=native packet_benchmark.cpp -o benchmark
#define main original_benchmark_main
#include "../benchmark.cpp"
#undef main
#include "packet.hpp"
#if !defined(__aarch64__) || !defined(__ARM_NEON)
#error "The matched benchmark compares the ARM64 NEON kernel."
#endif

namespace check_packet {
using namespace prime_screen::packet;

// At these generated packet boundaries the groups are 11 x 12, 10, 5 x 8, 6.
// Specialize each run so the compiler incurs no length branch inside a row.
constexpr bool same_boundaries(){
    if(table.used!=18)return false;
    unsigned edge=scalar_prefix;
    for(unsigned r=0;r<table.used;++r){
        const unsigned size = r<11 ? 12 : (r==11 ? 10 : (r<17 ? 8 : 6));
        if(table.rows[r].first!=edge || table.rows[r].length!=size)return false;
        edge+=size;
    }
    return edge==last;
}
static_assert(same_boundaries());
inline bool matched_suffix(Word n){
    for(unsigned i=64;i<196;i+=12)
        if(raw_batch(n,i,std::make_index_sequence<12>{}))return true;
    if(raw_batch(n,196,std::make_index_sequence<10>{}))return true;
    for(unsigned i=206;i<246;i+=8)
        if(raw_batch(n,i,std::make_index_sequence<8>{}))return true;
    return raw_batch(n,246,std::make_index_sequence<6>{});
}
int matched(unsigned long n){
    if(n<=UINT32_MAX)return baseline(n);
    if(prefix_rejects(n)||matched_suffix(n))return 0;
    return odd_after_screen(n);
}
int packet(unsigned long n){
    return prime_screen::packet::is_prime(n,baseline,odd_after_screen);
}
bool verify_arithmetic(Word n){
    bool any=false;
    for(unsigned b=0;b<max_rows;++b){
        const auto& row=table.rows[b];
        uint32_t r[4]; vst1q_u32(r,reduced(n,row));
        for(unsigned l=0;l<4;++l){
            const auto M=row.modulus[l];
            if(Word(r[l])>=Word(2)*M || n%M!=r[l]%M)return false;
            for(unsigned j=0;j<3;++j){
                const auto p=UINT32_MAX/row.cutoff[j][l];
                if(M%p || (n%p==0)!=(r[l]*row.inverse[j][l]<=row.cutoff[j][l]))return false;
                any |= n%p==0;
            }
        }
    }
    return any==packed_suffix(n) && any==matched_suffix(n);
}
}
static int native_flint(unsigned long n){return baseline(n);}
__attribute__((noinline)) static double clock_method(const std::vector<Word>& values,Test fn){
    return time_call(values,fn);
}
static void measure_packet(Word seed,const char* name,Sample kind,unsigned N){
    auto words=sample(kind,N);
    const std::array<Test,4> methods={native_flint,candidate,check_packet::matched,check_packet::packet};
    Word prime_count=0;
    for(auto n:words){
        const bool truth=reference(n);
        for(auto f:methods)if((f(n)!=0)!=truth)throw std::runtime_error("reference mismatch");
        prime_count+=truth;
    }
    for(auto f:methods)clock_method(words,f);
    constexpr unsigned orders[4][4]={{0,1,3,2},{1,2,0,3},{2,3,1,0},{3,0,2,1}};
    for(unsigned r=0;r<12;++r){
        double t[4];
        for(auto k:orders[(seed+r)%4]){
            t[k]=clock_method(words,methods[k]);
            if(consumed!=prime_count)throw std::runtime_error("timing checksum mismatch");
        }
        std::printf("%llu,%s,%u,%llu,%u,%.4f,%.4f,%.4f,%.4f\n",
                    static_cast<unsigned long long>(seed),name,N,
                    static_cast<unsigned long long>(prime_count),r,t[0],t[1],t[2],t[3]);
    }
    std::fflush(stdout);
}
int main(int argc,char**argv){
    if(argc!=2)return 2;
    auto h=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL); if(!h)return 2;
    baseline=reinterpret_cast<Test>(dlsym(h,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(h,"n_is_prime_odd_no_trial"));
    if(!baseline||!odd_after_screen)return 2;
    std::fprintf(stderr,"FLINT %s; independent suffix and word checks enabled.\n",
                 reinterpret_cast<const char*>(dlsym(h,"flint_version")));
    validate_boundaries();
    for(Word n=0;n<=1000000;++n)
        if((check_packet::packet(n)!=0)!=(baseline(n)!=0))return 7;
    for(Word n:{UINT64_C(2047),UINT64_C(3215031751),UINT64_C(341550071728321),
                UINT64_C(3825123056546413051),UINT64_C(18446744073709551557)})
        if((check_packet::packet(n)!=0)!=reference(n))return 8;
    using check_packet::verify_arithmetic;
    for(unsigned d=0;d<512;++d)if(!verify_arithmetic(UINT64_MAX-d))return 3;
    for(unsigned i=0;i<prime_screen::packet::last;++i){
        const Word p=prime_screen::screen.prime[i];
        const Word q=UINT64_MAX/p;
        for(Word n:{(q-1)*p-1,(q-1)*p,(q-1)*p+1,q*p-1,q*p})if(!verify_arithmetic(n))return 4;
    }
    state=148912137;
    for(unsigned i=0;i<20000;++i)if(!verify_arithmetic(random_word()))return 5;
    std::printf("seed,workload,inputs,primes,round,flint_ns,full_screen_ns,matched_scalar_ns,packet_ns\n");
    for(Word seed:{651153979UL,89921013UL,278735509UL}){
        state=seed;
        measure_packet(seed,"uniform-u64",Sample::uniform,65536);
        measure_packet(seed,"uniform-odd-u64",Sample::odd,65536);
        measure_packet(seed,"high-odd48",Sample::odd48,32768);
        measure_packet(seed,"prime64",Sample::prime,4096);
        measure_packet(seed,"semiprime",Sample::semiprime,4096);
    }
}
