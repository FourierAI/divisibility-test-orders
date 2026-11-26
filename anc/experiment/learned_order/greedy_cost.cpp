#define LEARNED_ORDER_NO_MAIN
#include "experiment.cpp"

int main() {
    std::cout<<"rep,law,seed,round,acquire_ns,greedy_fit_ns,joint_fit_ns,order\n"
             <<std::fixed<<std::setprecision(0);
    for (unsigned rep=0;rep<3;++rep) for (unsigned law=0;law<2;++law) {
        const auto seed=train_seeds[rep][law];
        const auto values=draw(static_cast<Law>(law),seed,train_size);
        for (int r=-1;r<9;++r) {
            lo::Census freq;
            const auto acq=nanoseconds([&] {
                freq.fill(0);
                for (auto n:values) ++freq[lo::hit_mask(n)];
            });
            lo::Order greedy{}, joint{};
            lo::Schedule g{}, j{};
            auto run_greedy=[&] { greedy=lo::fit_residual_greedy(freq); g=lo::prepare(greedy); };
            auto run_joint=[&] { joint=lo::fit_joint(freq); j=lo::prepare(joint); };
            double gt,jt;
            if (r%2) { gt=nanoseconds(run_greedy); jt=nanoseconds(run_joint); }
            else { jt=nanoseconds(run_joint); gt=nanoseconds(run_greedy); }
            if (greedy!=joint) throw std::runtime_error("greedy and joint orders differ");
            for (unsigned i=0;i<lo::size;++i) {
                if (g[i].inverse!=j[i].inverse || g[i].limit!=j[i].limit)
                    throw std::runtime_error("compiled tables differ");
            }
            if (r>=0) std::cout<<rep<<','<<law_name[law]<<','<<seed<<','<<r<<','<<acq
                              <<','<<gt<<','<<jt<<','<<order_text(greedy)<<'\n';
        }
    }
}
