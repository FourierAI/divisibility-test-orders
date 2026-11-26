# 第一篇论文的 Lean 4 形式化验证

验证对象是 Zhipeng Ye、Feng Jiang 和 Hao LI 的 74 页预印本 *Learning Divisibility Test Orders from the Largest Hits*。本项目覆盖第 1 节的完整四质数例子，以及定理 1、定理 2 和若干附录证明中的有限数学步骤。论文中的完整渐近定理、样本复杂度和计算困难性仍需单独验证。

## 运行

在解压后的项目目录运行以下命令。项目固定使用 Lean 4.19.0，依赖随该版本提供的库，无需下载 mathlib。

~~~sh
lake build
~~~

也提供包含同一组证明与公理审计的单文件 `FirstPaperProofs.lean`。用同版本 Lean 可直接运行 `lean --trust=0 -DwarningAsError=true FirstPaperProofs.lean`。

默认目标编译全部证明并执行公理审计。配置启用了内核的 `--trust=0` 和警告即错误。`Audit.lean` 通过 Lean 环境遍历项目定理，检查传递依赖，并在发现项目自定义公理或许可名单以外的公理时终止。许可名单是 Lean 基础库中的 `propext`、`Quot.sound` 和 `Classical.choice`。项目由 `Screening.lean` 汇总，单个模块也可以独立阅读。[Lean 官方安装说明](https://lean-lang.org/install/)

## 论文与代码对照

页码采用预印本印刷页码。表内标明每个结果的适用条件，便于核对形式化命题与原文的距离。

| 论文位置 | 代码和已验证结论 |
|---|---|
| 第 1 页，引言的四质数例子 | [FourPrimes.lean](Screening/FourPrimes.lean) 从实际整数的整除关系生成观测。两来源的命中数和最大命中相同，四个素数的边际命中率均为 1/2。完整顺序恰有 24 个，各自最优成本均为 19/12，共同顺序最坏成本的最优值为 5/3。代码也证明了任意有限有理随机化顺序的下界。 |
| 第 3、9–10 页，自然算术模型 | [IntervalCounts.lean](Screening/IntervalCounts.lean) 对实际的连续奇数区间计数。互异奇素数同时整除的比例与其倒数乘积之差严格小于 1/L。论文给定的区间条件保证每个整数最多命中 h 个候选素数。 |
| 第 3、9–10 页，试除顺序的成本 | [ScreeningCost.lean](Screening/ScreeningCost.lean) 从第一个命中即停的扫描定义推出全部前缀的存活概率和，加上全部未命中时的后备成本。相邻交换的成本差等于两次候选测试在共同前缀之后首次命中的概率差；非相邻交换也有逐前缀恒等式。 |
| 第 14–16 页，实际成本的矩展开 | [CostMoments.lean](Screening/CostMoments.lean) 从实际的扫描步骤出发，按一个子集最后一个被测试元素的秩，计算该子集出现在多少个前缀中。对完整顺序和有限带权分布，顺序间的成本差可写成包含矩与秩之差的有符号和；比较两个分布则得到矩偏差表达式。 |
| 第 4、16–17 页，定理 1 的总体上界 | [LargestHits.lean](Screening/LargestHits.lean) 证明在位移不超过 W、保留至少一个最大命中的条件下，最大测试秩的替代误差至多为 2W；误差非零时，最大的 ℓ+1 个命中都落在宽度 2W 的区间内。[ClusterCount.lean](Screening/ClusterCount.lean) 构造显式覆盖，证明这样的 h 元命中集合至多有 m(2W+1)^ℓ m^(h−1−ℓ) 个，并把这个界代入代理目标最小化的成本保证。`counted_surrogate_regret` 的命题列出位移及矩权重界；整数权重也覆盖统一放大分母后的有限有理权重。 |
| 第 10–11、16–17 页，定理 1 的下界构造 | [MomentCube.lean](Screening/MomentCube.lean) 在由实际子集形成的有符号扰动上证明总质量与低阶包含矩不变。[Indistinguishability.lean](Screening/Indistinguishability.lean) 证明配对扰动在“命中数与最大的 ℓ 个命中”的观测中抵消，并从给定的损失间隔推出某一来源上的概率下界。这些命题明确需要相应配对和有利顺序的成本界。 |
| 第 10–11 页，从命中集合分配到实际整数 | [CellLift.lean](Screening/CellLift.lean) 对非空单元构造统一分母，将给定的有理概率均匀分配给该单元内每个整数，并证明总质量为一、各单元的质量正确、单元质量的密度界转化为逐整数密度界。具体构造的单元质量满足这些界仍需证明。 |
| 第 17–19 页，定理 2 和观测重建 | [StoppedTrace.lean](Screening/StoppedTrace.lean) 中的 `saturated_trace_inversion` 把实际扫描所得的一条满长记录，与必要命中和禁止命中事件的包含排除式联系起来。`recover_required` 给出避开各子集的查询恢复必需命中质量的代数步骤。测度接口仅要求对一次二值划分有限可加；代码给出了实际有限权重实例。 |
| 第 20–21 页，单命中估计的置信度 | [SampleVariance.lean](Screening/SampleVariance.lean) 用真正的独立乘积分布证明样本方差恒等式与切比雪夫界。对有限有理观测，若单块失败概率至多为 1/4，则 2s+1 个独立块多数失败的概率至多为 (1/2)(3/4)^s；在同一批数据上同时控制 M 个前缀，可以再乘以 M。特定记录协议的无偏性及其得分方差上界仍需由论文的协议推导。 |
| 第 58 页，64 位打包试除 | [PacketArithmetic.lean](Screening/PacketArithmetic.lean) 从倒数乘法分析推出近似商最多偏小 1，余数小于 2M；对每个整除 M 的候选素数，测试余数与测试原数的整除性等价。32 位截断以及给定有效模逆时的乘法判定也已验证。结论是算术正确性，运行时间由实验测量。 |

### 定理 1 中已连通的证明链

可以从 [CostMoments.lean](Screening/CostMoments.lean) 的 `operational_counted_surrogate_regret` 开始阅读。其结论直接比较两个顺序的实际扫描成本。输入包括一个有限带权来源、候选顺序与比较顺序在菜单内的秩位移界、命中数上限及各阶包含矩的误差界。若候选顺序在由最大命中计算的代理目标上优于或等于比较顺序，Lean 给出实际成本差的显式上界。前缀展开、带符号权重、聚集集合计数和两倍误差传递均在该证明链中推导。选取比较顺序为真正的最优顺序，还需要证明它满足给定的位移界。

## 验证边界

论文定理 1 将误差写成随菜单规模变化的渐近阶。当前的有限上界需要给出合法最优顺序的位移界和矩误差界。完整的下界还要在论文指定的素数区间中构造足够多的困难实例，证明质量界和损失间隔达到所声称的数量级。附录中的素数分布估计、整套浓缩与信息论推导、低秩算法和 Gap-ETH 归约也仍须验证。引用本项目时，合适的表述是“对四质数例子和论文列明的证明步骤进行了 Lean 形式化验证”。

## 核对原稿

PDF 的 SHA-256 为 `a18be1dc864d779690318e3afd837be79b21aa11403c98241da060972029a94a`，配套 arXiv 源码包的 SHA-256 为 `88510f239aa2bc8cac49aefdba555418cefd23b62f5d32aa3eab1d09b72e41e4`。
