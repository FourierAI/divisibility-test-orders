// Supplemental native ablation. The original six-treatment runs are archived.
#define LEARNED_ORDER_NO_MAIN
#include "experiment.cpp"

static int fixed_all(unsigned long n) {
    return lo::is_prime_batch<lo::size>(n,lo::menu,packet_entry);
}
static int runtime_all(unsigned long n) {
    return lo::is_prime_batch<lo::size>(n,*current_schedule,packet_entry);
}
static int runtime_six(unsigned long n) {
    return lo::is_prime_batch<6>(n,*current_schedule,packet_entry);
}
int main(int argc, char** argv) {
    if (argc!=2) { std::cerr<<"usage: batch_control FLINT_LIBRARY\n"; return 2; }
    auto lib=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);
    if (!lib) throw std::runtime_error(dlerror());
    baseline=reinterpret_cast<Test>(dlsym(lib,"n_is_prime"));
    odd_after_screen=reinterpret_cast<Test>(dlsym(lib,"n_is_prime_odd_no_trial"));
    if (!baseline || !odd_after_screen) throw std::runtime_error("missing FLINT symbols");
#ifdef LEARNED_ORDER_CUTOFF_SIX
    const std::array<Test,6> calls{
        packet_entry,runtime_all,runtime_six,runtime_six,runtime_six,runtime_six};
    constexpr const char* names[]{
        "packet","all_runtime","six_increasing","six_marginal_A","six_joint_A","six_joint_B"};
#else
    const std::array<Test,6> calls{
        baseline,packet_entry,ordered_entry,ordered_entry,runtime_all,fixed_all};
    constexpr const char* names[]{"flint","packet","increasing","joint_A","all_runtime","all_fixed"};
#endif
    constexpr unsigned positions[]{0,1,5,2,4,3};
    std::cout<<"rep,law,test_seed,inputs,round,position,method,ns_per_word\n"
             <<std::fixed<<std::setprecision(5);
    for (unsigned rep=0;rep<3;++rep) {
        const auto training=draw(Law::matching_a,train_seeds[rep][0],train_size);
        lo::Census freq{};
        for (Word word:training) ++freq[lo::hit_mask(word)];
        const auto trained=lo::prepare(lo::fit_joint(freq));
        const auto inc=lo::prepare(lo::increasing());
#ifdef LEARNED_ORDER_CUTOFF_SIX
        const auto marginal=lo::prepare(lo::fit_marginals(freq));
        const auto training_b=draw(Law::matching_b,train_seeds[rep][1],train_size);
        lo::Census freq_b{};
        for (Word word:training_b) ++freq_b[lo::hit_mask(word)];
        const auto trained_b=lo::prepare(lo::fit_joint(freq_b));
        const std::array<const lo::Schedule*,6> tables{&inc,&inc,&inc,&marginal,&trained,&trained_b};
        const auto install=[&](unsigned m) { current_schedule=tables[m]; };
#else
        const auto install=[&](unsigned m) { current_schedule=m==3 ? &trained : &inc; };
#endif
        for (unsigned law=0;law<3;++law) {
            const auto seed=test_seeds[rep][law];
            const auto words=draw(static_cast<Law>(law),seed,test_size);
            unsigned primes=0;
            for (Word n:words) {
                const bool expected=reference(n);
                primes+=expected;
                for (unsigned k=0;k<6;++k) {
                    install(k);
                    if ((calls[k](n)!=0)!=expected) throw std::runtime_error("reference mismatch");
                }
            }
            for (unsigned k=0;k<6;++k) { install(k); timed(words,calls[k]); }
            for (unsigned round=0;round<12;++round) {
                for (unsigned pos=0;pos<6;++pos) {
                    const auto k=(positions[pos]+round+rep+law)%6;
                    install(k);
                    const auto ns=timed(words,calls[k]);
                    if (consumed!=primes) throw std::runtime_error("checksum mismatch");
                    std::cout<<rep<<','<<law_name[law]<<','<<seed<<','<<test_size<<','<<round
                             <<','<<pos<<','<<names[k]<<','<<ns<<'\n';
                }
            }
        }
    }
}
