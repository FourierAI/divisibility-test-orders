// build.sh supplies the archived first-hit experiment with its main omitted.
#include "trace_core.inc"
namespace shift7 {
namespace tb=trace_bench;
constexpr unsigned rows=32768, arms=10, epoch=2048, cap=64;
constexpr unsigned a6=0x999,b6=0x555,secure9=0x777,minimax6=0x333;
constexpr unsigned boundaries[]{8705,17381,26113};
constexpr Word training_base[]{8870301,8870333,8870397,8870451,8870525};
constexpr Word test_base[]{58399171,58516723,58643333,58784317,58918369};
constexpr const char* names[]{"flint","packet","all12","minimax6","first_A","first_B",
    "cascade_A","common9","oracle","targeted"};
constexpr const char* laws[]{"A","B","uniform","ABAB"};
const lo::Schedule table_a=tb::arrange(a6),table_b=tb::arrange(b6);
static unsigned oracle_counter;
__attribute__((noinline)) static std::uint64_t count_span(const Word* words,unsigned count,Test call) {
    // Preserve the shared indirect call for static tables, FLINT and the router.
    asm volatile("" : "+r"(call));
    std::uint64_t total=0;
    for(unsigned i=0;i<count;++i) total+=call(words[i]);
    return total;
}
static double timed_arm(const std::vector<Word>& words,Test call,unsigned law,unsigned arm) {
    const auto begin=std::chrono::steady_clock::now();
    std::uint64_t total=0;
    unsigned start=0;
    for(unsigned seg=0;seg<(law==3?4u:1u);++seg) {
        const unsigned end=law==3 && seg<3 ? boundaries[seg] : rows;
        if(law==3 && arm==8) {
            current_schedule=seg%2 ? &table_b : &table_a;
            call=tb::filter<6>;
        }
        total+=count_span(words.data()+start,end-start,call);
        start=end;
    }
    const auto end=std::chrono::steady_clock::now();
    consumed=total;
    return std::chrono::duration<double,std::nano>(end-begin).count()/words.size();
}
static unsigned active_source(unsigned index) {
    return (index>=boundaries[0])^(index>=boundaries[1])^(index>=boundaries[2]);
}
static int oracle_stream(unsigned long n) {
    const bool sign=active_source(oracle_counter++);
    return lo::is_prime_batch<6>(n,sign?table_b:table_a,packet_entry);
}
template<std::size_t... I>
static bool complement(Word n,const lo::Schedule& s,std::index_sequence<I...>) {
    return (unsigned(n*s[I+6].inverse<=s[I+6].limit)|...);
}
__attribute__((noinline)) static int second(Word n) {
    if(complement(n,*current_schedule,std::make_index_sequence<6>{})) return 0;
    return packet_entry(n);
}
static int cascade(unsigned long n) {
    if(n<=UINT32_MAX) return packet_entry(n);
    if(lo::hits_batch(n,*current_schedule,std::make_index_sequence<6>{})) return 0;
    return second(n);
}
struct Audit {unsigned first=0,early=0,logs=0,cert_a=0,cert_b=0;};
struct Router {
    enum Mode {testing,fitted_a,fitted_b,fallback};
    Mode mode=testing;
    unsigned offset=0,wa=0,wb=0;
    template<bool measure> int call(unsigned long n,Audit* out) {
        if(offset==0) {mode=testing;wa=0;wb=0;}
        const auto phase=offset;
        offset=(offset+1)&(epoch-1);
        static_assert((epoch&(epoch-1))==0);
        if(mode==fallback) return packet_entry(n);
        if(mode!=testing) {
            const auto& table=mode==fitted_b ? table_b : table_a;
            if(n>UINT32_MAX && lo::hits_batch(n,table,std::make_index_sequence<6>{})) {
                if constexpr(measure) {++out->early;++out->first;}
                return 0;
            }
            return packet_entry(n);
        }
        if constexpr(measure) ++out->logs;
        const unsigned marks=(phase%2)?b6:a6;
        const unsigned j=tb::first_hit(n,marks);
        if(j<lo::size && !(marks&(1u<<j))) {
            if(marks==a6) ++wb; else ++wa;
            if(wa && wb) mode=fallback;
            else if(wa==2) {
                mode=fitted_a;
                if constexpr(measure) ++out->cert_a;
            } else if(wb==2) {
                mode=fitted_b;
                if constexpr(measure) ++out->cert_b;
            }
        }
        if(phase+1==cap && mode==testing) mode=fallback;
        if(n>UINT32_MAX && j<lo::size) {
            if constexpr(measure) {++out->early;++out->first;}
            return 0;
        }
        return packet_entry(n);
    }
};
static Router router;
static int targeted(unsigned long n) {return router.call<false>(n,nullptr);}
static void reset(){router={};oracle_counter=0;}
static void population_check() {
    unsigned worst=0,common_width=13;
    for(unsigned s=0;s<lo::states;++s) {
        unsigned a=tb::covered_tickets(s,0),b=tb::covered_tickets(s,1);
        if(__builtin_popcount(s)==6) worst=std::max(worst,std::min(a,b));
        if(a==18 && b==18) common_width=std::min(common_width,unsigned(__builtin_popcount(s)));
    }
    if(worst!=15||common_width!=9||tb::covered_tickets(minimax6,0)!=15||
       tb::covered_tickets(minimax6,1)!=15||tb::covered_tickets(a6,0)!=18||
       tb::covered_tickets(a6,1)!=12||tb::covered_tickets(b6,1)!=18||
       tb::covered_tickets(b6,0)!=12||tb::covered_tickets(secure9,0)!=18||
       tb::covered_tickets(secure9,1)!=18) throw std::runtime_error("population oracle mismatch");
}
static std::vector<Word> draw_law(unsigned law,Word seed) {
    if(law<2) return tb::trade_words(law,seed,rows);
    if(law==2) return draw(Law::uniform_odd,seed,rows);
    std::vector<Word> words; words.reserve(rows);
    constexpr unsigned lengths[]{8705,8676,8732,6655};
    static_assert(8705+8676+8732+6655==rows);
    for(unsigned j=0;j<4;++j) {
        const auto part=tb::trade_words(j%2,seed+10000019*(j+1),lengths[j]);
        words.insert(words.end(),part.begin(),part.end());
    }
    return words;
}
struct Trained {unsigned mask=0;lo::Schedule table{};};
static Trained train_one(unsigned rep,unsigned sign,std::ostream& out) {
    const Word seed=training_base[rep]+100903*sign, marks_seed=seed+15000107;
    const auto words=tb::trade_words(sign,seed,tb::n_train);
    const auto hash=fingerprint(words);
    std::vector<tb::Trace> log(tb::n_train);
    Trained result;
    for(int round=-1;round<7;++round) {
        const double acquire=nanoseconds([&]{
            state=marks_seed;
            for(unsigned i=0;i<tb::n_train;++i) {
                const auto marks=unsigned(random_word())&lo::all;
                log[i]={marks,tb::first_hit(words[i],marks)};
            }
        });
        const double fitting=nanoseconds([&]{
            result.mask=tb::coverage_fit(tb::recover(log));
            result.table=tb::arrange(result.mask);
        });
        if(round>=0) out<<rep<<','<<sign<<','<<seed<<','<<marks_seed<<','<<tb::n_train<<','<<hash<<','
            <<round<<','<<result.mask<<','<<tb::covered_tickets(result.mask,sign)<<','
            <<tb::covered_tickets(result.mask,1-sign)<<','<<acquire<<','<<fitting<<','<<acquire+fitting<<'\n';
    }
    return result;
}
} // namespace shift7

int main(int argc,char** argv) {
    using namespace shift7;
    if(argc!=3) {std::cerr<<"usage: onehit_shift FLINT_LIBRARY NEW_OUTPUT_DIR\n";return 2;}
    const fs::path dest=argv[2];
    if(!fs::create_directory(dest)) throw std::runtime_error("output directory must be new");
    auto lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);
    if(!lib) throw std::runtime_error(dlerror());
    baseline=reinterpret_cast<Test>(dlsym(lib,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(lib,"n_is_prime_odd_no_trial"));
    if(!baseline||!odd_after_screen) throw std::runtime_error("missing FLINT symbols");
    std::cerr<<"FLINT "<<reinterpret_cast<const char*>(dlsym(lib,"flint_version"))<<'\n';
    population_check();
    std::ofstream times(dest/"timings.csv"),counts(dest/"counts.csv"),fit(dest/"training.csv");
    for(auto* out:{&times,&counts,&fit}) out->exceptions(std::ios::badbit|std::ios::failbit);
    times<<"rep,law,seed,round,position,method,ns_per_word\n"<<std::fixed<<std::setprecision(5);
    counts<<"rep,law,seed,words,hash,primes,method,first_rejects,all_rejects,diagnostic_logs,A_epochs,B_epochs\n";
    fit<<"rep,source,seed,mark_seed,words,hash,round,mask,own_tickets,shifted_tickets,acquire_ns,fit_ns,total_ns\n"
       <<std::fixed<<std::setprecision(0);
    const auto all=tb::arrange(lo::all),minimax=tb::arrange(minimax6),common=tb::arrange(secure9);
    for(unsigned rep=0;rep<5;++rep) {
        const auto a=train_one(rep,0,fit), b=train_one(rep,1,fit);
        for(unsigned law=0;law<4;++law) {
            const Word seed=test_base[rep]+1000003*law;
            const auto words=draw_law(law,seed);
            const auto hash=fingerprint(words);
            std::vector<unsigned> masks(rows);std::vector<unsigned char> truths(rows);
            unsigned total=0;
            for(unsigned i=0;i<rows;++i) {
                truths[i]=reference(words[i]);total+=truths[i];masks[i]=direct_mask(words[i]);
                if(masks[i]!=lo::hit_mask(words[i])) throw std::runtime_error("divisor mismatch");
            }
            const std::array<const lo::Schedule*,arms> tables{&all,&all,&all,&minimax,&a.table,
                &b.table,&a.table,&common,law==1?&table_b:&table_a,&all};
            const std::array<Test,arms> calls{baseline,packet_entry,tb::filter<12>,tb::filter<6>,
                tb::filter<6>,tb::filter<6>,cascade,tb::filter<9>,
                law==2?packet_entry:(law==3?oracle_stream:tb::filter<6>),targeted};
            const std::array<unsigned,arms> first_masks{0,0,lo::all,minimax6,a.mask,b.mask,
                a.mask,secure9,law==2?0u:(law==1?b6:a6),0};
            for(unsigned arm=0;arm<arms;++arm) {
                current_schedule=tables[arm];reset();
                Router replay;Audit audit;
                for(unsigned i=0;i<rows;++i) {
                    if(bool(calls[arm](words[i]))!=bool(truths[i])) throw std::runtime_error("primality mismatch");
                    if(arm==9) {
                        if(bool(replay.call<true>(words[i],&audit))!=bool(truths[i])) throw std::runtime_error("replay mismatch");
                    } else if(words[i]>UINT32_MAX) {
                        auto chosen=first_masks[arm];
                        if(arm==8 && law==3) chosen=active_source(i)?b6:a6;
                        audit.first+=bool(masks[i]&chosen);
                        audit.early+=bool(masks[i]&(arm==6?lo::all:chosen));
                    }
                }
                counts<<rep<<','<<laws[law]<<','<<seed<<','<<rows<<','<<hash<<','<<total<<','
                      <<names[arm]<<','<<audit.first<<','<<audit.early<<','<<audit.logs<<','
                      <<audit.cert_a<<','<<audit.cert_b<<'\n';
                reset();timed_arm(words,calls[arm],law,arm);
                if(consumed!=total) throw std::runtime_error("warm checksum");
            }
            constexpr unsigned order[]{0,1,9,2,8,3,7,4,6,5};
            for(unsigned round=0;round<arms;++round) for(unsigned pos=0;pos<arms;++pos) {
                const unsigned arm=(order[pos]+round+rep+law)%arms;
                current_schedule=tables[arm];reset();
                const double ns=timed_arm(words,calls[arm],law,arm);
                if(consumed!=total) throw std::runtime_error("timed checksum");
                times<<rep<<','<<laws[law]<<','<<seed<<','<<round<<','<<pos<<','<<names[arm]<<','<<ns<<'\n';
            }
        }
        std::cerr<<"rep "<<rep<<" verified\n";
    }
}
