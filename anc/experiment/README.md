# 整数素性判定的 64 位预筛实验

本实验改造 FLINT 3.6.0 的小因子检查。每次调用独立判断一个整数，不要求输入连续、重复或预先排序。程序接受任意大小的十进制整数。优化针对大于 `UINT32_MAX`、不超过 `UINT64_MAX` 的输入，其余正整数调用 FLINT 的确定性判定。普通黎曼猜想与这个实现的正确性无关。

命令行的 `--check` 入口在 ARM64 NEON 上使用四路 32 位预筛。Apple M4 对均匀随机 64 位奇数的正式测量为每个数 107.71 ns，原版 FLINT 为 130.39 ns。对两个大质数的乘积，两者分别为 499.53 和 440.62 ns。下方种子测速命令复现早期标量实现，向量版的同组标量对照、测试输入和两次计时记录在单独目录。[四路筛选的推导与复现](packet_screen/README.md)

## 标量判据和实现

对固定奇质数 `p`，取 `v` 为 `p` 模 `2^64` 的乘法逆元，`b` 为 `UINT64_MAX / p` 的整数部分。对于 64 位无符号整数 `n`，无符号乘积 `n*v` 的低 64 位不超过 `b`，当且仅当 `p` 整除 `n`。因为若低 64 位是 `q` 且 `q <= b`，则 `p*q` 小于 `2^64`，同时与 `n` 模 `2^64` 同余，故 `p*q=n`。反过来若 `n=p*q`，这个 `q` 正是低 64 位的结果。

大于 `UINT32_MAX` 的奇数先查 `n mod 15015` 的余数表，覆盖 3、5、7、11、13。然后对 17 至 1627 的 252 个质数按每组四个执行上述检查。所有质数表和乘法常量在编译时生成。任一整除成立即可宣布合数。其余输入进入 FLINT 的 `n_is_prime_odd_no_trial` 严格判定。原版 `n_is_prime` 也用模逆整除，本实现改变的是筛选范围、分组及余数表。表大小和筛选上限根据独立的试运行选择，正式测量使用另外三个随机种子。

## 复现

实测环境为 Apple M4、macOS 26.2、Apple Clang 17、FLINT 3.6.0。以下命令在本目录运行，使用 Python 3.12 从 `python-flint` 的 macOS ARM64 wheel 获取原生库。已安装相同版本 FLINT 的机器也可以直接指定库路径。

```sh
python3.12 -m venv /tmp/prime-screen-venv
/tmp/prime-screen-venv/bin/python -m pip install python-flint==0.9.0
flint_lib=$(/tmp/prime-screen-venv/bin/python -c 'import flint,pathlib; print(next((pathlib.Path(flint.__file__).parent / ".dylibs").glob("libflint.*.dylib")))')
clang++ -std=c++17 -O3 -mcpu=native benchmark.cpp -o /tmp/prime-screen
/tmp/prime-screen "$flint_lib" --check 18446744073709551557
for seed in 89258713 67430219 39568211; do /tmp/prime-screen "$flint_lib" "$seed"; done
```

`prime_screen.hpp` 中的 `is_prime` 可嵌入单个无符号 64 位整数的调用点。`benchmark.cpp` 提供动态加载、命令行及计时。命令行对超出字长的正整数调用 FLINT 的 `fmpz_is_prime`。原始结果见 `results.txt`。

## 测量和校验

每个种子使用 10 万个均匀随机 64 位无符号数、10 万个均匀随机 64 位奇数、5 万个 48 位奇数、5000 个 64 位质数、5000 个两个 32 位质数的乘积，以及 5 万个 32 位无符号数。数表在计时前生成。两种函数都在同一原生进程预热，交替先后顺序执行 11 轮，逐个输入返回确定结果。两列时间分别是每轮平均纳秒数的中位数，倍数是同轮时间之比的中位数。计时不含进程启动、十进制解析和正确性对照。

对每个测速输入都用独立实现的 12 个质数底数 Miller–Rabin 检验核对。在整个 64 位范围内，该检验有确定性保证。此外用埃氏筛穷举 0 至 100 万，测试 32 位及 64 位边界、每个预筛质数最大的可表示倍数及邻居，并测试若干强伪素数。计时代码遇到任何分歧都会终止。

质数与两个大质数的乘积都能通过扩大的小因子筛。因此，这两种负载要支付更多预筛成本。读结果时应选择符合实际输入的那组，未经测试的硬件和分布需要重新测量。

整除判据、原版筛选范围和独立校验的依据分别见 [FLINT 整除算法](https://flintlib.org/doc/algorithms/arithmetic/divisibility-test.html)、[FLINT 3.6.0 源码](https://github.com/flintlib/flint/blob/v3.6.0/src/ulong_extras/is_prime.c) 和 [Sorenson 与 Webster 的论文](https://doi.org/10.1090/mcom/3134)。

## 从单次命中日志学习预筛

另一组实验只向学习器提供随机试除顺序和第一个成功的除数。从 8192 条训练记录里选择六个除数后，两组人工配对分布上的十次训练都覆盖了该分布的全部非空因子组合。输入分布改变后，同一组选中的除数会漏掉更多合数，需要调用后端完成判定。实验同时比较了固定顺序日志、完整训练记录和十二个除数全部并行检查的耗时。[逐组结果与复现](learned_order/stopped_trials.md)
