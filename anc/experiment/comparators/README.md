# 两种独立的原生 64 位素性判定对照

在 Apple M4、macOS 26.2、Apple Clang 17 上，原实验的扩展预筛在均匀 64 位整数上耗时 59.30 ns，原版 FLINT 为 66.16 ns。两个独立对照为 85.84 ns 和 307.27 ns。换成两个大质数的乘积，原版 FLINT 和独立的 Berg 实现都快于扩展预筛。

| 输入 | 原版 FLINT | 扩展预筛＋FLINT | Math::Prime::Util | Berg 字长移植 | FLINT / 扩展预筛，三种子的范围 |
|---|---:|---:|---:|---:|---:|
| 均匀 64 位整数 | 66.16 | 59.30 | 307.27 | 85.84 | 1.105–1.115 |
| 均匀 64 位奇数 | 127.91 | 109.25 | 596.22 | 162.63 | 1.168–1.173 |
| 48 位奇数 | 99.91 | 89.87 | 459.87 | 113.16 | 1.107–1.125 |
| 64 位质数 | 856.19 | 918.34 | 4571.00 | 1558.51 | 0.923–0.934 |
| 两个 32 位质数的乘积 | 441.64 | 537.29 | 1929.17 | 461.02 | 0.822–0.823 |
| 均匀 32 位整数 | 24.01 | 23.88 | 45.17 | 41.80 | 1.003–1.012 |

各时间列单位为每个输入的平均纳秒数。每个种子先取 12 个区组的中位数，表中再取三个种子的中位数。最后一列先求同区组时间之比，再汇总每个种子的中位数，给出三者的最小和最大值。它描述本次运行的波动。三个种子在同一台机器上测量，无法给出跨机器置信区间。32 位输入的扩展实现直接调用原版 FLINT，两者的微小差别可用来判断这一计时方法的分辨能力。完整的 216 个区组记录见 [results.csv](results.csv)。

**四种实现。** 原版调用 FLINT 3.6.0 的公开接口，扩展预筛调用同版 FLINT 的无试除入口。Math::Prime::Util 0.75 直接调用发行源码中的 C 函数，并在计时前按默认大小初始化素数缓存。其 64 位路径先筛到 89，再做以 2 为底的强伪素数检验和 Lucas 检验。项目中的汇编 Montgomery 运算只在 x86-64 开启，表中的 ARM64 结果受此影响。[FLINT 发行记录](https://flintlib.org/downloads.html) · [Math::Prime::Util 0.75 文档](https://metacpan.org/release/DANAJ/Math-Prime-Util-0.75/view/lib/Math/Prime/Util.pm) · [其素性判定源码](https://metacpan.org/release/DANAJ/Math-Prime-Util-0.75/source/primality.c)

Berg 对照使用发行包 miller-rabin 1.0.1 的筛表、小因子预筛、散列函数及全部确定性见证选择规则。我们把其大整数模幂改写为 64 位 Montgomery 运算，使每次模乘都使用原生高低半乘积。表中时间对应此移植。原理上，若 \(R=2^{64}\)、\(u\equiv ab n^{-1}\pmod R\)，则 \(ab\) 与 \(un\) 的低半部分相同，\((ab-un)/R\) 是高半部分之差，落在 \((-n,n)\) 内。结果为负时加 \(n\) 即得到模乘结果。64 位上界以上没有使用此实现。[原作者的实现与底数来源](https://pypi.org/project/miller-rabin/) · [本实验的模运算与见证选择](berg.cpp)

**校验与计时。** 四种实现处理完全相同的 930,000 个输入。每个输入先用前 12 个质数作底的独立 Miller–Rabin 实现核对。三个种子、六种输入分布、每类样本量与原实验一致。还用埃氏筛逐一核对 0 至 1,000,000，并检查 32 位边界、最大可表示值附近和若干已知强伪素数。每个输入表的四个函数先预热，每四轮使每个函数在每个位置各出现一次，每个不同函数对也以前后相邻顺序各出现一次。每轮都检查返回的质数总数。计时包含逐个整数的原生函数调用，启动、样本生成和正确性核对在计时之外。[计时与校验程序](native.cpp) · [确定性校验所用底数的依据](https://doi.org/10.1090/mcom/3134)

## 在 macOS ARM64 复现

在本目录执行以下命令。输入文件为上游发布的两个源码包和 FLINT 3.6.0 动态库，后者可按[原实验说明](../README.md)取得。下例将编译产物放到单独的临时目录。Math::Prime::Util 自带 standalone 模式，其中另一段未链接进测试器的代码用到了 Perl 的清零宏，编译命令补上等效的 memset 定义。

~~~sh
work=$(mktemp -d)
here=$PWD
curl -fL 'https://cpan.metacpan.org/authors/id/D/DA/DANAJ/Math-Prime-Util-0.75.tar.gz' -o "$work/mpu.tar.gz"
curl -fL 'https://files.pythonhosted.org/packages/fb/76/1381ddc726f59fdb7af9ebc4926e37d9d010fe711d8ade15c1499e0b61f3/miller_rabin-1.0.1.tar.gz' -o "$work/mr.tar.gz"
shasum -a 256 "$work/mpu.tar.gz" "$work/mr.tar.gz"
tar -xzf "$work/mpu.tar.gz" -C "$work"
cd "$work/Math-Prime-Util-0.75"
cc -std=gnu11 -O3 -mcpu=native -DSTANDALONE '-DZero(p,n,t)=memset((p),0,(n)*sizeof(t))' \
  -fPIC -dynamiclib -Wl,-dead_strip -Wl,-exported_symbol,_is_prime \
  -Wl,-exported_symbol,_prime_precalc -o "$work/mpu.dylib" \
  util.c primality.c cache.c sieve.c lucas_seq.c
cd "$here"
python3 build_berg.py "$work/mr.tar.gz" "$work/berg.dylib"
clang++ -std=c++17 -O3 -mcpu=native native.cpp -o "$work/native"
"$work/native" /path/to/libflint.dylib "$work/mpu.dylib" "$work/berg.dylib" > "$work/results.csv"
~~~

实测使用的两个源码包 SHA-256 摘要依次为：

~~~text
85c17cbeb5927d71f024a2e1f197bff61e1ca6da249053e1683b62c894bb8881
0ba0ab6cddb4ee6f9bdf829b66b7bb8e363ce5fdb80241528e461c667816a926
~~~
