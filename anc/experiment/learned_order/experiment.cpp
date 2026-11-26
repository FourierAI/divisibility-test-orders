// Reuse the archived deterministic reference, SplitMix64, FLINT bindings,
// and per-word timing loop without duplicating the backend implementation.
#define main archived_benchmark_main
#include "../benchmark.cpp"
#undef main
#include "learned_order.hpp"
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>

namespace lo = learned_order;
namespace fs = std::filesystem;
enum class Law { matching_a, matching_b, uniform_odd };
constexpr unsigned matching[2][6][2]{
    {{0,1},{2,3},{4,5},{6,7},{8,9},{10,11}},
    {{0,2},{4,6},{8,10},{1,3},{5,7},{9,11}}};
constexpr const char* law_name[]{"A","B","uniform-odd"};
constexpr Word train_seeds[3][2]{{173141,247247},{584309,592591},{916781,939391}};
constexpr Word test_seeds[3][3]{
    {1009001,2009047,3009041},{1009039,2009081,3009077},{1009079,2009099,3009149}};
constexpr unsigned train_size=8192, test_size=65536;
constexpr const char* method_name[]{
    "flint","packet","increasing","marginal_A","joint_A","joint_B"};
constexpr unsigned methods=6;
struct Fit { lo::Order marginal, joint; };
static const lo::Schedule* current_schedule;

static Word bounded(Word n) {
    const Word threshold=(Word(0)-n)%n;
    for (;;) { const Word v=random_word(); if (v>=threshold) return v%n; }
}
static std::vector<Word> draw(Law law, Word seed, unsigned count) {
    state=seed;
    std::vector<Word> values;
    values.reserve(count);
    while (values.size()<count) {
        if (law==Law::uniform_odd) { values.push_back(random_word()|1); continue; }
        Word product=1;
        if (bounded(5)!=0) {
            const auto& edge=matching[static_cast<unsigned>(law)][bounded(6)];
            product=Word(lo::primes[edge[0]])*lo::primes[edge[1]];
        }
        const Word lower=Word(1)<<63, high=UINT64_MAX/product;
        const Word first=(lower/product+(lower%product!=0))|1;
        const Word choices=(high-first)/2+1;
        // Rejection is conditional on the chosen edge, preserving its mass.
        Word cofactor;
        do { cofactor=first+2*bounded(choices); } while (lo::hit_mask(cofactor));
        values.push_back(cofactor*product);
    }
    return values;
}
static Word fingerprint(const std::vector<Word>& values) {
    Word hash=UINT64_C(14695981039346656037);
    for (Word n:values) hash=(hash^n)*UINT64_C(1099511628211);
    return hash;
}
static unsigned direct_mask(Word n) {
    unsigned mask=0;
    for (unsigned i=0;i<lo::size;++i) mask|=unsigned(n%lo::primes[i]==0)<<i;
    return mask;
}
static void verify_law(Law law, const lo::Census& freq) {
    if (law==Law::uniform_odd) return;
    lo::Census allowed{};
    allowed[0]=1;
    for (const auto& edge:matching[static_cast<unsigned>(law)])
        allowed[(1u<<edge[0])|(1u<<edge[1])]=1;
    for (unsigned mask=0;mask<lo::states;++mask)
        if (freq[mask]&&!allowed[mask]) throw std::runtime_error("unexpected mask");
}
static std::string order_text(const lo::Order& order) {
    std::string out;
    for (auto i:order) { if (!out.empty()) out+='-'; out+=std::to_string(i); }
    return out;
}
static void write_hist(std::ostream& out, const char* partition, unsigned rep,
                       Law law, Word seed, const lo::Census& freq) {
    for (unsigned i=0;i<lo::states;++i) if (freq[i])
        out<<partition<<','<<rep<<','<<law_name[static_cast<unsigned>(law)]
           <<','<<seed<<','<<i<<','<<freq[i]<<'\n';
}
template<class Function> static double nanoseconds(Function function) {
    using Clock=std::chrono::steady_clock;
    asm volatile("" ::: "memory");
    const auto start=Clock::now();
    function();
    asm volatile("" ::: "memory");
    return std::chrono::duration<double,std::nano>(Clock::now()-start).count();
}
static std::uint64_t total_probes(const lo::Census& freq, const lo::Order& order) {
    std::uint64_t total=0;
    for (unsigned mask=0;mask<lo::states;++mask) if (freq[mask]) {
        unsigned count=0;
        for (auto i:order) { ++count; if (mask&(1u<<i)) break; }
        total+=freq[mask]*count;
    }
    return total;
}
static Fit train(unsigned rep, Law law, Word seed, std::ostream& times, std::ostream& hist) {
    const auto values=draw(law,seed,train_size);
    const auto hash=fingerprint(values);
    lo::Census truth{};
    for (Word n:values) ++truth[direct_mask(n)];
    verify_law(law,truth);
    write_hist(hist,"train",rep,law,seed,truth);
    Fit fit{};
    for (int round=-1;round<9;++round) {
        lo::Census freq;
        const double acq=nanoseconds([&] {
            freq.fill(0);
            for (Word n:values) ++freq[lo::hit_mask(n)];
        });
        lo::Schedule marginal_schedule{}, joint_schedule{};
        const auto marginal_fit=[&] {
            fit.marginal=lo::fit_marginals(freq); marginal_schedule=lo::prepare(fit.marginal);
        };
        const auto joint_fit=[&] {
            fit.joint=lo::fit_joint(freq); joint_schedule=lo::prepare(fit.joint);
        };
        double margin,joint;
        if (round%2==0) { margin=nanoseconds(marginal_fit); joint=nanoseconds(joint_fit); }
        else { joint=nanoseconds(joint_fit); margin=nanoseconds(marginal_fit); }
        if (freq!=truth || marginal_schedule.front().inverse!=lo::menu[fit.marginal[0]].inverse
            || joint_schedule.front().limit!=lo::menu[fit.joint[0]].limit)
            throw std::runtime_error("training feature mismatch");
        if (total_probes(freq,fit.joint)>total_probes(freq,fit.marginal))
            throw std::runtime_error("ERM objective mismatch");
        if (round>=0)
            times<<rep<<','<<law_name[static_cast<unsigned>(law)]<<','<<seed<<','<<train_size
                 <<','<<hash<<','<<round<<','<<acq<<','<<margin<<','<<joint<<','
                 <<order_text(fit.marginal)<<','<<order_text(fit.joint)<<'\n';
    }
    return fit;
}
static int packet_entry(unsigned long n) {
    return prime_screen::packet::is_prime(n,baseline,odd_after_screen);
}
static int ordered_entry(unsigned long n) {
    return lo::is_prime(n,*current_schedule,baseline,odd_after_screen);
}
__attribute__((noinline)) static double timed(const std::vector<Word>& values, Test call) {
    return time_call(values,call);
}
static void test(unsigned rep, Law law, Word seed, const Fit& a, const Fit& b,
                 std::ostream& timing, std::ostream& holdout, std::ostream& hist) {
    const auto values=draw(law,seed,test_size);
    const std::array<lo::Order,4> orders{lo::increasing(),a.marginal,a.joint,b.joint};
    std::array<lo::Schedule,4> schedules{};
    for (unsigned i=0;i<orders.size();++i) schedules[i]=lo::prepare(orders[i]);
    const std::array<Test,methods> calls{
        baseline,packet_entry,ordered_entry,ordered_entry,ordered_entry,ordered_entry};
    const auto install=[&](unsigned m) {
        if (m>=2) current_schedule=&schedules[m-2];
    };
    lo::Census freq{}, eligible_freq{};
    unsigned primes=0;
    std::vector<unsigned char> truths;
    truths.reserve(test_size);
    for (Word n:values) {
        const unsigned mask=direct_mask(n);
        if (mask!=lo::hit_mask(n)) throw std::runtime_error("test divisor mismatch");
        ++freq[mask];
        if (n>UINT32_MAX) ++eligible_freq[mask];
        truths.push_back(reference(n));
        primes+=truths.back();
    }
    verify_law(law,freq);
    write_hist(hist,"test",rep,law,seed,freq);
    const auto law_text=law_name[static_cast<unsigned>(law)];
    const auto hash=fingerprint(values);
    for (unsigned m=0;m<methods;++m) {
        install(m);
        for (unsigned i=0;i<test_size;++i)
            if ((calls[m](values[i])!=0)!=bool(truths[i]))
                throw std::runtime_error("independent primality check failed");
        holdout<<rep<<','<<law_text<<','<<seed<<','<<test_size<<','<<hash<<','<<primes<<','
               <<test_size-freq[0]<<','<<method_name[m]<<',';
        if (m>=2) holdout<<total_probes(eligible_freq,orders[m-2]);
        holdout<<'\n';
        timed(values,calls[m]);
        if (consumed!=primes) throw std::runtime_error("warm checksum mismatch");
    }
    constexpr unsigned base_order[]{0,1,5,2,4,3};
    for (unsigned round=0;round<12;++round) {
        for (unsigned pos=0;pos<methods;++pos) {
            const unsigned m=(base_order[pos]+round+rep+static_cast<unsigned>(law))%methods;
            install(m);
            const double ns=timed(values,calls[m]);
            if (consumed!=primes) throw std::runtime_error("timed checksum mismatch");
            timing<<rep<<','<<law_text<<','<<seed<<','<<test_size<<','<<round<<','<<pos<<','
                  <<method_name[m]<<','<<ns<<'\n';
        }
    }
    std::cerr<<"verified rep "<<rep<<' '<<law_text<<", prime count "<<primes<<'\n';
}
#ifndef LEARNED_ORDER_NO_MAIN
int main(int argc, char** argv) {
    if (argc!=3) { std::cerr<<"usage: experiment FLINT_LIBRARY NEW_OUTPUT_DIR\n"; return 2; }
    const fs::path dest=argv[2];
    if (!fs::create_directory(dest)) throw std::runtime_error("output directory must be new");
    auto lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);
    if (!lib) throw std::runtime_error(dlerror());
    baseline=reinterpret_cast<Test>(dlsym(lib,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(lib,"n_is_prime_odd_no_trial"));
    if (!baseline || !odd_after_screen) throw std::runtime_error("FLINT 64-bit symbols required");
    std::cerr<<"FLINT "<<reinterpret_cast<const char*>(dlsym(lib,"flint_version"))<<'\n';
    auto boundary_schedule=lo::prepare(lo::increasing());
    for (const auto p:lo::primes) {
        if (!reference(p) || lo::is_prime(p,boundary_schedule,baseline,odd_after_screen)!=1)
            throw std::runtime_error("small prime dispatch");
        const Word large=(UINT64_MAX/p)*p;
        for (const Word n:{large-1,large,large+1})
            if ((lo::is_prime(n,boundary_schedule,baseline,odd_after_screen)!=0)!=reference(n))
                throw std::runtime_error("multiple boundary");
    }
    std::ofstream timing(dest/"timings.csv"), training(dest/"training.csv"),
        holdout(dest/"holdout.csv"), hist(dest/"histograms.csv");
    for (auto* f:{&timing,&training,&holdout,&hist}) f->exceptions(std::ios::badbit|std::ios::failbit);
    timing<<std::fixed<<std::setprecision(5);
    training<<std::fixed<<std::setprecision(0);
    timing<<"rep,law,test_seed,inputs,round,position,method,ns_per_word\n";
    training<<"rep,law,train_seed,inputs,word_hash,round,acquire_ns,marginal_fit_ns,joint_fit_ns,marginal_order,joint_order\n";
    holdout<<"rep,law,test_seed,inputs,word_hash,primes,menu_hits,method,total_leading_probes\n";
    hist<<"partition,rep,law,seed,mask,count\n";
    for (unsigned rep=0;rep<3;++rep) {
        const auto a=train(rep,Law::matching_a,train_seeds[rep][0],training,hist);
        const auto b=train(rep,Law::matching_b,train_seeds[rep][1],training,hist);
        for (unsigned i=0;i<3;++i)
            test(rep,static_cast<Law>(i),test_seeds[rep][i],a,b,timing,holdout,hist);
    }
}
#endif
