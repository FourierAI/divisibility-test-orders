// One-hit training with public random priorities on two four-prime trades.
#define LEARNED_ORDER_NO_MAIN
#include "experiment.cpp"

namespace trace_bench {
constexpr unsigned n_train = 8192, n_test = 32768, replicas = 5;
constexpr unsigned pairs[2][6][2]{
    {{0,1},{2,3},{0,2},{0,2},{1,3},{1,3}},
    {{0,1},{2,3},{0,3},{0,3},{1,2},{1,2}}};
using Counts = std::array<int, lo::size>;
struct Moments { Counts single{}; std::array<Counts, lo::size> pair{}; };
struct Trace { unsigned marks, first; };
struct Fitted { unsigned fixed, one_hit, census; };

std::vector<Word> trade_words(unsigned sign, Word seed, unsigned count) {
    state=seed;
    std::vector<Word> result;
    result.reserve(count);
    while (result.size()<count) {
        Word factor=1;
        if (bounded(5)!=0) {
            const unsigned offset=4*bounded(3);
            const auto& e=pairs[sign][bounded(6)];
            factor=Word(lo::primes[offset+e[0]])*lo::primes[offset+e[1]];
        }
        const Word low=Word(1)<<63, high=UINT64_MAX/factor;
        const Word first=(low/factor+(low%factor!=0))|1;
        Word cofactor;
        do { cofactor=first+2*bounded((high-first)/2+1); }
        while (lo::hit_mask(cofactor));
        result.push_back(factor*cofactor);
    }
    return result;
}

// Only this routine sees the training word on the one-hit path. Its
// caller receives the public priority bits and the first hit or sentinel.
unsigned first_hit(Word n, unsigned marks) {
    for (auto group : {marks, lo::all ^ marks}) {
        for (;group;group&=group-1) {
            const auto j=__builtin_ctz(group);
            if (n*lo::menu[j].inverse<=lo::menu[j].limit) return j;
        }
    }
    return lo::size;
}

Moments recover(const std::vector<Trace>& log) {
    Moments estimate;
    for (auto [marks,j]: log) {
        if (j==lo::size || (marks&(1u<<j))) continue;
        estimate.single[j]+=2;
        for (unsigned i=j+1;i<lo::size;++i)
            estimate.pair[j][i]+=(marks&(1u<<i)) ? -4 : 4;
    }
    for (unsigned j=0;j<lo::size;++j)
        for (unsigned i=j+1;i<lo::size;++i)
            estimate.single[j]-=estimate.pair[j][i]/2;
    return estimate;
}

unsigned coverage_fit(const Moments& estimate) {
    unsigned best=0;
    int high=std::numeric_limits<int>::min();
    for (unsigned mask=0;mask<lo::states;++mask) {
        if (__builtin_popcount(mask)!=6) continue;
        int score=0;
        for (unsigned j=0;j<lo::size;++j) {
            if (mask&(1u<<j)) score+=estimate.single[j];
            for (unsigned i=j+1;i<lo::size;++i)
                if (mask&((1u<<j)|(1u<<i))) score+=estimate.pair[j][i];
        }
        if (score>high) {best=mask;high=score;}
    }
    return best;
}

unsigned covered_tickets(unsigned mask, unsigned sign) {
    unsigned covers=0;
    for (unsigned offset:{0u,4u,8u})
        for (const auto& e:pairs[sign])
            if (mask&((1u<<(offset+e[0]))|(1u<<(offset+e[1])))) ++covers;
    return covers;
}
Fitted train_trade(unsigned sign,unsigned rep,std::ostream& out) {
    const Word word_seed=7100003+40813*rep+1009*sign;
    const Word mark_seed=8500003+26813*rep+1601*sign;
    auto words=trade_words(sign,word_seed,n_train);
    std::vector<Trace> log(n_train);
    const double acquire=nanoseconds([&] {
        state=mark_seed;
        for (unsigned t=0;t<n_train;++t) {
            const auto marks=unsigned(random_word())&lo::all;
            log[t]={marks,first_hit(words[t],marks)};
        }
    });
    unsigned active{};
    const double fit_time=nanoseconds([&] {active=coverage_fit(recover(log));});
    Moments fixed,full;
    for (unsigned t=0;t<n_train;++t) {
        // The two comparators acquire their own information. The random
        // logger has already finished fitting and cannot see these masks.
        const auto j=first_hit(words[t],0);
        if (j!=lo::size) ++fixed.single[j];
        const auto mask=direct_mask(words[t]);
        if (!mask) continue;
        if (__builtin_popcount(mask)!=2) throw std::runtime_error("hit cap");
        ++full.pair[__builtin_ctz(mask)][31-__builtin_clz(mask)];
    }
    Fitted fitted{coverage_fit(fixed),active,coverage_fit(full)};
    for (auto n:{64u,256u,1024u,n_train}) {
        std::vector<Trace> prefix(log.begin(),log.begin()+n);
        const unsigned learned=(n==n_train ? active : coverage_fit(recover(prefix)));
        out<<rep<<','<<sign<<','<<word_seed<<','<<mark_seed<<','<<n<<','
           <<learned<<','<<covered_tickets(learned,sign)<<','<<covered_tickets(learned,1-sign)
           <<','<<fitted.fixed<<','<<fitted.census<<','<<acquire<<','<<fit_time<<'\n';
    }
    return fitted;
}

lo::Schedule arrange(unsigned mask) {
    lo::Order order{};
    unsigned index=0;
    for (auto set:{mask,lo::all ^ mask})
        for (;set;set&=set-1) order[index++]=__builtin_ctz(set);
    return lo::prepare(order);
}
template<std::size_t... I>
bool tests(Word n,const lo::Schedule& schedule,std::index_sequence<I...>) {
    return (unsigned(n*schedule[I].inverse<=schedule[I].limit) | ...);
}
template<unsigned K>
int filter(unsigned long n) {
    if (n>UINT32_MAX && tests(n,*current_schedule,std::make_index_sequence<K>{})) return 0;
    return packet_entry(n);
}

void benchmark(unsigned rep,unsigned law,const Fitted& a,const Fitted& b,
               std::ostream& timing,std::ostream& held) {
    const Word seed=9600011+80833*rep+2903*law;
    auto words= law<2 ? trade_words(law,seed,n_test) : draw(Law::uniform_odd,seed,n_test);
    const std::array<unsigned,8> masks{0,0,lo::all,a.fixed,a.census,a.one_hit,b.one_hit,b.census};
    const std::array<Test,8> calls{baseline,packet_entry,filter<12>,filter<6>,filter<6>,filter<6>,filter<6>,filter<6>};
    const char* names[]{"FLINT","packet","all12","fixed_log_A","full_A","first_A","first_B","full_B"};
    std::array<lo::Schedule,8> schedules;
    std::array<unsigned,8> rejects{};
    unsigned primes=0;
    for (unsigned i=0;i<8;++i) schedules[i]=arrange(masks[i]);
    for (Word n:words) {
        const bool truth=reference(n);
        const unsigned actual=direct_mask(n);
        primes+=truth;
        for (unsigned i=0;i<8;++i) {
            current_schedule=&schedules[i];
            if (truth!=(calls[i](n)!=0)) throw std::runtime_error("reference mismatch");
            rejects[i]+=(n>UINT32_MAX && (masks[i]&actual)!=0);
        }
    }
    for (unsigned i=0;i<8;++i) {
        held<<rep<<','<<law<<','<<seed<<','<<n_test<<','<<fingerprint(words)<<','<<primes<<','
            <<names[i]<<','<<masks[i]<<','<<rejects[i]<<'\n';
        current_schedule=&schedules[i];timed(words,calls[i]);
    }
    constexpr unsigned positions[]{0,1,7,2,6,3,5,4};
    for (unsigned round=0;round<8;++round)
        for (unsigned pos=0;pos<8;++pos) {
            const auto i=(positions[pos]+round+law+rep)%8;
            current_schedule=&schedules[i];const auto ns=timed(words,calls[i]);
            if (consumed!=primes) throw std::runtime_error("primality checksum");
            timing<<rep<<','<<law<<','<<seed<<','<<round<<','<<pos<<','<<names[i]<<','<<ns<<'\n';
        }
}
} // namespace trace_bench

int main(int argc,char** argv) {
    if (argc!=3) {std::cerr<<"usage: stopped_benchmark FLINT_LIBRARY NEW_OUTPUT_DIR\n";return 2;}
    const fs::path dir=argv[2];
    auto lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);
    if (!lib) throw std::runtime_error(dlerror());
    baseline=reinterpret_cast<Test>(dlsym(lib,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(lib,"n_is_prime_odd_no_trial"));
    if (!baseline||!odd_after_screen) throw std::runtime_error("missing FLINT API");
    if (!fs::create_directory(dir)) throw std::runtime_error("output directory must be new");
    std::ofstream training(dir/"training.csv"),held(dir/"heldout.csv"),timing(dir/"timings.csv");
    for (auto* stream:{&training,&held,&timing}) stream->exceptions(std::ios::badbit|std::ios::failbit);
    training<<"rep,law,word_seed,mark_seed,train_n,one_hit_mask,matching_tickets,shifted_tickets,fixed_mask_8192,census_mask_8192,log_ns_8192,fit_ns_8192\n";
    held<<"rep,law,test_seed,words,hash,prime_count,method,menu_mask,rejected\n";
    timing<<std::fixed<<std::setprecision(5)<<"rep,law,test_seed,round,position,method,ns\n";
    for (unsigned rep=0;rep<trace_bench::replicas;++rep) {
        auto a=trace_bench::train_trade(0,rep,training), b=trace_bench::train_trade(1,rep,training);
        for (unsigned law=0;law<3;++law) trace_bench::benchmark(rep,law,a,b,timing,held);
    }
}
