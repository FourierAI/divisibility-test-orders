// Single-word dispatch, new holdouts; reuse archived arithmetic and input laws.
#define LEARNED_ORDER_NO_MAIN
#include "../experiment.cpp"

namespace shift {
constexpr unsigned rows=32768, epochs=2048, cap=64, arms=8, runs=8;
constexpr unsigned robust6=0x999, robust9=0x777;
constexpr Word fresh_train[]{8870301,8870333,8870397,8870451,8870525};
constexpr Word seed0[]{58399171,58516723,58643333,58784317,58918369};
constexpr const char* sources[]{"A","B","C","uniform","ABCA"};
constexpr const char* names[]{"flint","packet","all12","trained_A6","cascade_A6",
                             "common_AB6","common_ABC9","online_matching"};

static std::vector<Word> draw_c(Word seed,unsigned count) {
    state=seed;
    std::vector<Word> result; result.reserve(count);
    while (result.size()<count) {
        Word product=1;
        if (bounded(5)) {
            const unsigned ticket=bounded(6), base=4*(ticket/2), side=ticket%2;
            product=Word(lo::primes[base+side])*lo::primes[base+3-side];
        }
        const Word low=Word(1)<<63, first=(low/product+(low%product!=0))|1;
        const Word choices=(UINT64_MAX/product-first)/2+1;
        Word cofactor;
        do {cofactor=first+2*bounded(choices);} while(lo::hit_mask(cofactor));
        result.push_back(product*cofactor);
    }
    return result;
}
static std::vector<Word> sample_law(unsigned law,Word seed,unsigned count) {
    if (law<2) return draw(static_cast<Law>(law),seed,count);
    if (law==2) return draw_c(seed,count);
    if (law==3) return draw(Law::uniform_odd,seed,count);
    constexpr unsigned lengths[]{8705,8676,8732,6655}, order[]{0,1,2,0};
    static_assert(8705+8676+8732+6655==rows);
    if (count!=rows) throw std::runtime_error("mixed stream lengths");
    std::vector<Word> result;
    result.reserve(count);
    for (unsigned segment=0;segment<4;++segment) {
        auto part=sample_law(order[segment],seed+10000019*(segment+1),lengths[segment]);
        result.insert(result.end(),part.begin(),part.end());
    }
    return result;
}
static lo::Schedule mask_schedule(unsigned mask) {
    lo::Order order=lo::increasing();
    std::stable_partition(order.begin(),order.end(),
                          [mask](unsigned i){return mask&(1u<<i);});
    return lo::prepare(order);
}
static unsigned six_mask(const lo::Order& order) {
    unsigned mask=0;
    for(unsigned i=0;i<6;++i) mask|=1u<<order[i];
    return mask;
}
static int batch12(unsigned long n) {return lo::is_prime_batch<12>(n,*current_schedule,packet_entry);}
static int batch9(unsigned long n) {return lo::is_prime_batch<9>(n,*current_schedule,packet_entry);}
static int batch6(unsigned long n) {return lo::is_prime_batch<6>(n,*current_schedule,packet_entry);}
template<std::size_t... I>
inline bool complementary_hit(Word n,const lo::Schedule& schedule,std::index_sequence<I...>) {
    return (unsigned(n*schedule[I+6].inverse<=schedule[I+6].limit)|...);
}
// The second stage stays out of line to preserve the conditional branch.
__attribute__((noinline)) static int second(Word n) {
    if(complementary_hit(n,*current_schedule,std::make_index_sequence<6>{})) return 0;
    return packet_entry(n);
}
static int cascade(unsigned long n) {
    if(n<=UINT32_MAX) return packet_entry(n);
    if(lo::hits_batch(n,*current_schedule,std::make_index_sequence<6>{})) return 0;
    return second(n);
}
struct Audit {unsigned early=0, first=0, acquired=0, recovered=0;};
struct Online {
    enum Mode {acquire, fitted, ordinary};
    unsigned pos=0, touched=0, edges=0;
    unsigned masks[6]{};
    lo::Schedule table{};
    Mode mode=acquire;
    template<bool log>
    int call(Word n, Audit* audit) {
        if(pos==0) {mode=acquire; touched=0; edges=0;}
        const unsigned phase=pos;
        pos=(pos+1)&(epochs-1);
        static_assert((epochs&(epochs-1))==0);
        if(mode==ordinary) return packet_entry(n);
        if(mode==fitted) {
            if(n>UINT32_MAX && lo::hits_batch(n,table,std::make_index_sequence<6>{})) {
                if constexpr(log) {++audit->early;++audit->first;}
                return 0;
            }
            return packet_entry(n);
        }
        if constexpr(log) ++audit->acquired;
        const unsigned mask=lo::hit_mask(n);
        if(mask) {
            if(__builtin_popcount(mask)!=2) mode=ordinary;
            else if (!(mask&touched)) {
                touched|=mask;
                masks[edges]=mask;
                table[edges++]=lo::menu[__builtin_ctz(mask)];
                if(edges==6) {
                    mode=fitted;
                    if constexpr(log) ++audit->recovered;
                }
            } else if(std::find(masks,masks+edges,mask)==masks+edges) mode=ordinary;
        }
        if(phase+1==cap && mode==acquire) mode=ordinary;
        if(n>UINT32_MAX && mask) {
            if constexpr(log) {++audit->early;++audit->first;}
            return 0;
        }
        return packet_entry(n);
    }
};
static Online online;
static int online_entry(unsigned long n) {return online.call<false>(n,nullptr);}
static unsigned pop(unsigned x){return __builtin_popcount(x);}
static unsigned tickets(unsigned mask,unsigned law) {
    unsigned n=0;
    for(unsigned k=0;k<6;++k) {
        unsigned i,j;
        if(law<2) {i=matching[law][k][0];j=matching[law][k][1];}
        else {i=4*(k/2)+(k%2);j=4*(k/2)+3-(k%2);}
        n+=bool(mask&((1u<<i)|(1u<<j)));
    }
    return n;
}
static void verify_minima() {
    unsigned min2=13,min3=13;
    for(unsigned mask=0;mask<lo::states;++mask) {
        if(tickets(mask,0)!=6 || tickets(mask,1)!=6) continue;
        min2=std::min(min2,pop(mask));
        if(tickets(mask,2)==6) min3=std::min(min3,pop(mask));
    }
    if(min2!=6 || min3!=9 || pop(robust6)!=min2 || tickets(robust6,0)!=6 ||
       tickets(robust6,1)!=6 || tickets(robust6,2)!=3 || pop(robust9)!=min3 ||
       tickets(robust9,0)+tickets(robust9,1)+tickets(robust9,2)!=18)
        throw std::runtime_error("population hitter enumeration failed");
}
} // namespace shift

int main(int argc,char** argv) {
    using namespace shift;
    if(argc!=3) {std::cerr<<"usage: shift_stress FLINT_LIBRARY NEW_OUTPUT_DIR\n";return 2;}
    const fs::path dest=argv[2];
    if(!fs::create_directory(dest)) throw std::runtime_error("output directory must be new");
    auto lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);
    if(!lib) throw std::runtime_error(dlerror());
    baseline=reinterpret_cast<Test>(dlsym(lib,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(lib,"n_is_prime_odd_no_trial"));
    if(!baseline||!odd_after_screen) throw std::runtime_error("missing FLINT symbols");
    std::cerr<<"FLINT "<<reinterpret_cast<const char*>(dlsym(lib,"flint_version"))<<'\n';
    verify_minima();
    std::ofstream times(dest/"timings.csv"),counts(dest/"counts.csv"),fit(dest/"offline_fit.csv");
    for(auto* out:{&times,&counts,&fit}) out->exceptions(std::ios::badbit|std::ios::failbit);
    times<<"rep,law,seed,round,position,method,ns_per_word\n"<<std::fixed<<std::setprecision(5);
    counts<<"rep,law,seed,words,hash,primes,method,early_rejects,first_stage_rejects,online_feature_words,online_completed_fits\n";
    fit<<"rep,seed,words,hash,round,mask,acquire_ns,greedy_ns,total_ns\n";
    const lo::Schedule inc=lo::prepare(lo::increasing()), ab=mask_schedule(robust6), abc=mask_schedule(robust9);
    const std::array<Test,arms> calls{baseline,packet_entry,batch12,batch6,cascade,batch6,batch9,online_entry};
    std::vector<Word> boundaries{0,1,2,3,UINT32_MAX,Word(UINT32_MAX)+1,UINT64_MAX};
    for(unsigned p:lo::primes) {
        boundaries.push_back(p);
        Word top=(UINT64_MAX/p)*p;
        for(Word n:{top-1,top,top+1}) boundaries.push_back(n);
    }
    current_schedule=&ab;
    for(auto call:calls) {
        online={};
        for(Word n:boundaries)
            if((call(n)!=0)!=reference(n)) throw std::runtime_error("boundary mismatch");
    }
    for(unsigned rep=0;rep<5;++rep) {
        const auto training=draw(Law::matching_a,fresh_train[rep],train_size);
        const auto train_hash=fingerprint(training);
        lo::Census truth{}; for(Word n:training) ++truth[direct_mask(n)];
        verify_law(Law::matching_a,truth);
        lo::Order learned{};
        for(int round=-1;round<9;++round) {
            lo::Census hits;
            const auto acquire=nanoseconds([&]{hits.fill(0);for(Word n:training) ++hits[lo::hit_mask(n)];});
            const auto fitting=nanoseconds([&]{learned=lo::fit_residual_greedy(hits);});
            if(hits!=truth || learned!=lo::fit_joint(truth) || tickets(six_mask(learned),0)!=6)
                throw std::runtime_error("training verification failed");
            if(round>=0) fit<<rep<<','<<fresh_train[rep]<<','<<train_size<<','<<train_hash<<','<<round
               <<','<<six_mask(learned)<<','<<acquire<<','<<fitting<<','<<acquire+fitting<<'\n';
        }
        const auto table=lo::prepare(learned);
        const std::array<const lo::Schedule*,arms> tables{&inc,&inc,&inc,&table,&table,&ab,&abc,&inc};
        for(unsigned law=0;law<5;++law) {
            const Word seed=seed0[rep]+1000003*law;
            const auto words=sample_law(law,seed,rows);
            const auto hash=fingerprint(words);
            std::vector<unsigned char> prime(rows); std::vector<unsigned> masks(rows);
            unsigned total=0;
            for(unsigned i=0;i<rows;++i) {
                prime[i]=reference(words[i]);total+=prime[i];
                masks[i]=direct_mask(words[i]);
                if(masks[i]!=lo::hit_mask(words[i])) throw std::runtime_error("invalid divisor mask");
            }
            for(unsigned arm=0;arm<arms;++arm) {
                current_schedule=tables[arm]; online={};
                Audit audit{}; Online mirror;
                const unsigned first_mask[]={0,0,lo::all,six_mask(learned),six_mask(learned),robust6,robust9,0};
                for(unsigned i=0;i<rows;++i) {
                    const Word n=words[i];
                    if(bool(calls[arm](n))!=bool(prime[i])) throw std::runtime_error("primality mismatch");
                    if(arm==7) {
                        if(bool(mirror.call<true>(n,&audit))!=bool(prime[i])) throw std::runtime_error("audit mismatch");
                    } else if(n>UINT32_MAX) {
                        audit.first+=bool(masks[i]&first_mask[arm]);
                        audit.early+=bool(masks[i]&(arm==4?lo::all:first_mask[arm]));
                    }
                }
                counts<<rep<<','<<sources[law]<<','<<seed<<','<<rows<<','<<hash<<','<<total<<','
                      <<names[arm]<<','<<audit.early<<','<<audit.first<<','<<audit.acquired<<','<<audit.recovered<<'\n';
                online={}; timed(words,calls[arm]);
                if(consumed!=total) throw std::runtime_error("warm checksum");
            }
            constexpr unsigned order[]{0,1,7,2,6,3,5,4};
            for(unsigned round=0;round<runs;++round) {
                for(unsigned pos=0;pos<arms;++pos) {
                    const unsigned arm=(order[pos]+round+rep+law)%arms;
                    current_schedule=tables[arm];online={};
                    const double ns=timed(words,calls[arm]);
                    if(consumed!=total) throw std::runtime_error("timed checksum");
                    times<<rep<<','<<sources[law]<<','<<seed<<','<<round<<','<<pos<<','<<names[arm]<<','<<ns<<'\n';
                }
            }
        }
        std::cerr<<"rep "<<rep<<" verified\n";
    }
}
