# Lattice-based zkSNARK 原语调研（Primitives Survey）

> 调研对象：lattice-based zkSNARK / folding / batch-argument 方案及其**可复用密码原语**。
> 结论落在两处：本目录的实现（见 §2"实现映射"），以及仍开放的工作清单（§2 末尾 ⏳ 行）。
> 方案名与术语保留英文；数学记号沿用 crate 惯例：`R = Z_{2^32}[X]/(X^64+1)`（折叠环）、
> `R_q = Z_q[X]/(X^256+1)`（ML-DSA 环），Ajtai 承诺 `c = A·w`（`A` 由种子展开、`w` 短）。
>
> 引用经 eprint 原文/元数据核对；未能核实的条目已明确标注。

## 0. 一句话结论

主流 lattice zkSNARK 全部建立在同一组可复用原语上：**Ajtai/SIS 承诺 + 小范数挑战采样
（hyperball / 固定汉明重量稀疏 / 非单位线性 `X−a`）+ 摊销 batched opening（线性组合/内积
批处理）+ gadget 与 b-bit 分解（近似短性、范数控制）+ 环上 sumcheck + folding（同态承诺
更新、批量分解检查、跨项吸收）+ Fiat–Shamir（2-adic 环要求非单位/强采样挑战集）**。
`zk` crate 在 Z1–Z4 已有前几类的基础版；本次补齐三个此前缺失的可复用件：
**hyperball 采样器**（`sampling::hyperball_vec`）、**数字分解式投影/近似短性论证**
（`protocols::short`）、**LatticeFold 式分解折叠**（`protocols::latticefold`）。

## 1. 方案与原语清单

### 1.1 LaBRADOR（Beullens–Seiler, CRYPTO 2023, eprint 2022/1341）

Transparent R1CS 证明（原文语句：R1CS **mod 2^64+1**，环 `Z_q[X]/(X^64+1)`、素数
`q ≡ 5 mod 8`；10^6 约束 58 KB）。注意：本文的环**不是** `Z_{2^32}`——
本仓库 `z2` 是同构的 2-adic 简化变体。

原语：
1. **Ajtai/SIS 承诺**：`C = A·s`，线性同态、无陷门无噪声；
2. **摊销 dot-product batched opening**：r 个内积约束用小范数挑战线性组合一次证明，
   系数范数按 `√(r·τ)` 增长，每轮做 **基-b 数字分解** `z = z₀ + b·z₁` 把见证压回小范数
   （递归摊销）；
3. **HyperBall 挑战采样**：挑战取 l1/l∞ 球内均匀分布（lattirust 实现中即
   `hyperball` 模块），范数预算直接进 soundness 记账；
4. **投影论证（modular Johnson–Lindenstrauss, GHL21）**：验证者抽随机投影
   `Π: Z_q^{dn} → Z_q^{256}`，prover 发 `p = Π·s`；`p` 的正确性恰好是 256 个
   额外的常数项内积方程，在 batched 证明中"免费"携带；接受 `‖p‖₂ ≤ √128·B`
   则 w.o.p. 有 `‖s‖₂ ≲ √(128/30)·B ≈ 2.07·B`；
5. **可逆性（非单位）引理（Lyubashevsky–Seiler 2017/523）**：`q ≡ 5 (mod 8)` 时
   小范数非零元可逆——挑战差 `a−b` 可逆保证提取方程无零因子。2-adic 环的
   对应物是"奇元素挑战"（见 §1.5）。

### 1.2 Greyhound（Nguyen–Seiler, CRYPTO 2024, eprint 2024/1293）

标准格假设下第一个具体高效的多项式承诺（`N = 2^30` 时评估证明 53 KB），
与 LaBRADOR 组合成 SNARK。

原语：
1. **Gadget 矩阵与 `G^{-1}`**：`G_n = I_n ⊗ [1,2,…,2^{δ−1}]`，`G^{-1}(t)`
   逐条目二进制分解——近似/精确短性的基础件；
2. **双层承诺**：inner（gadget 分解后的数字，LaBRADOR 式 Ajtai）+
   outer（商/交叉项）；
3. **商多项式承诺**：`f(X) − y` 被**线性因子 `X − a` 整除**——直接承诺有界系数的商
   `q(X)`（`X−a` 自身 ‖·‖∞ ≤ 2，不需要可逆）——即"非单位线性挑战"的 PCS 形态；
4. 度数逐轮折半的 split-and-fold，底层接摊销 Σ-协议。

### 1.3 LatticeFold / LatticeFold+（Boneh–Chen, eprint 2024/257 / 2025/247）

面向 IVC/SNARK 的格折叠（对标 Nova）。实例接口 `R_hom`：
`y = A·f`（Ajtai）∧ `‖f‖∞ < B` ∧ `mle[f](r) = v̂`——见证同时被承诺、被范数界定、
被 multilinear 求值，三断言分别由线性检查、范数检查、**环上 sumcheck** 承担。

原语（均已对照原文核实）：
1. **批量分解（split_{b,k}，商/余数检查）**：把系数按基 b 写 k 位
   `f = Σ b^i·f_i`（`‖f_i‖∞ < b = ⌈B^{1/k}⌉`）；验证器检查
   `Σ b^i·A·f_i == A·f` 与 `Σ b^i·v̂_i == v̂`——精确线性恒等式，违反即短 kernel 向量
   （MSIS 破）；
2. **组合引理**：任意环元素权重 `ρ_i` 下 `A·(Σρᵢfᵢ) = Σρᵢ·(A·fᵢ)` 线性保持——
   折叠权重的代数基础；
3. **强采样集挑战**：折叠挑战 `ρ` 取自 `{a : a−b 可逆}`（NTT 完全分裂时 `C = Z_q`；
   小模数时取 NTT-槽对角集 `|C| = q^τ ≈ 2^128`），小挑战子集 `C_small` 要求
   扩张因子 `‖C_small‖_op ≤ c`（挑战乘数字范数受控）；
4. **vanishing-polynomial 范数检查**：`g(u) = ∏_{i∈[b]}(X−i)(X+i)` 零点集恰为
   `[−b, b]`，对 ℓ 个变量跑 sumcheck 即证"每一位都在界内"——sumcheck 同时承担
   折叠合法性与范数界；
5. **多断言合并 sumcheck（Π_batch）**：linearization、multilinear eval、range、
   CCS 门检查用 `(β, γ, α, μ, ζ)` 权重合并进单个 sumcheck；
6. **Nova 式跨项吸收**：`C_o = C₁ + ρ·C₂ + …`，交叉项以独立 Ajtai 承诺 `u_j` 吸收
   （Ajtai 无噪声，难点纯在范数增长，由 1+4 解决）。

（本仓库 `protocols::latticefold` = 原语 1 + 拆分查询 + 同态折叠的可复用核；
`protocols::fold` 是 Nova 式 relaxed-R1CS 线，两条互补。）

### 1.4 LaZer Library（Lyubashevsky–Seiler–Steuer, CCS 2024, eprint 2024/1846）

把 LaBRADOR/LNP22 框架工程化的分层格证明库（AVX-512 NTT 底座）。核实到的
核心技巧：
1. **mod-p → R_q 提升**：整数语句 `A·s ≡ t (mod p)` 写成 `A·s + p·v = t` over `R_q`
   （附加短秘密 `v`，防溢出）；
2. **随机挑战矩阵近似短性**：`u = T·[s; v] + y`（`T` 小整数矩阵、`y` 短掩码）——
   `‖u‖` 小则 `s, v` 大概率短且无溢出；
3. 掩码承诺 + 摊销 Σ-协议（即 ZK 盲化的 Ajtai 版本）；ALS20 乘积证明处理布尔约束。

### 1.5 Rinocchio（Ganesh–Nitulescu–Soria-Vazquez, CCS 2022, eprint 2021/322）

**QRP（Quadratic Ring Programs）**：把 QAP 式编码框架推广到交换环
（`Z_p[X]/(X^d+1)`、`Z_{2^k}`），designated-verifier。原语：环上可提取编码承诺、
目标多项式整除检查、以及**2-adic 挑战必须取奇元素**（非零因子/单位子集）——
本仓库 `nonunit_linear_poly`（`C = X − a`，`a` 奇）的同源出处。

### 1.6 SLAP（Albrecht–Fenzi–Lapiha–Nguyen, EUROCRYPT 2024, eprint 2023/1469）

标准假设下第一个非交互可提取多项式承诺，证明/验证 polylog。原语：**树式 Ajtai
承诺**（向量哈希树）、split-and-fold 评估递减、"挑战空间大小 vs 提取 slack"的
权衡分析（与 Bulletproofs 式格折叠的 subtractive-set 限制对比）。

### 1.7 Ligetron（Wang–Hazay–Venkitasubramaniam, IEEE S&P 2024,
DOI 10.1109/SP54263.2024.00086）

**不是格方案**：Ligero 的空间高效变体（Merkle/哈希承诺，抗量子性来自哈希）+
WASM 前端。列出仅为对照——"post-quantum SNARK" ≠ "lattice SNARK"。

### 1.8 MatRiCT / MatRiCT-Au / MatRiCT+（eprint 2019/1287 CCS 2019 /
CCS 2020 / 2021/545 S&P 2022；Esgin–Zhao–Steinfeld–Liu–Liu 等）

支付隐私应用栈，底层是 ESLL19 工具箱：
1. **固定汉明重量稀疏挑战** `C^d_{w,p} = {deg < d, HW = w, 非零位幅值 = p}`——
   保证 `c·s` 短、`c−c′` 非零（本仓库 `in_ball_poly` 即 `p = 1` 特例）；
2. **位分解范围证明**（金额界）、one-out-of-many（匿名集）；
3. **FS with aborts**（rejection sampling，原文出现 19 次）。

### 1.9 Lyubashevsky 系 Σ-protocol 工具箱（`protocols::sigma` 的现代语境）

- **ESLL19**（CRYPTO 2019）：短小范数挑战/响应的新技巧；
- **LNS21**（eprint 2020/1183）/ **LNP22**（eprint 2022/284, CRYPTO 2022）：
  当前标准框架——均匀/稀疏挑战 + **bimodal rejection sampling** + gadget 分解参数
  + 近似范围/范数证明 + 乘积证明；Biscuit、LaZer 都构建其上；
- **BLOOM**（eprint 2022/1307）：±c 双模态挑战分布消除大匿名集 rejection 开销；
- **ACL'22**（CRYPTO 2022）：格 SNARK + 递归组合（PCD）的早期形态；
- **FS with aborts 分析**：eprint 2023/245、2023/246。

### 1.10 格折叠生态（2024–2026，存在性已核实）

LatticeFold 线之后：**Lova**（2024/1964，非结构化格）、**Neo / SuperNeo**
（2025/294 / 2026/242，小域 pay-per-bit）、**SALSAA**（2025/2124）、
**Symphony**（2025/1905）、**Cyclo**（2026/359）、**PikkuFold**（2026/1809）、
**LatticeBlindFold**（2026/1857，ZK 折叠）、**"Improving LatticeFold+ with
ℓ₂-norm checks"**（2026/721）。共性原语：同态承诺更新、显式交叉项承诺、
大挑战空间、逐轮范数管理（分解 / 模切换 / 缩放）。

> 注：常被混称的 "Alpine / Shadow / Grease" 未能定位（eprint 2024–2025 全量标题
> 扫描无果）；上述生态名单以可核实条目为准。

### 1.11 公共底座

- **MSIS / SelfTargetMSIS / LWE** 假设（与 ML-DSA 同源，参数可由 lattice-estimator
  校准——本仓库 `algebra::security` 已有 Core-SVP 估计器）；
- **2-adic 环语义**：单位判据 = 系数和奇偶；`X` 恒为单位；理想 `(X−a)`（`a` 奇）
  指数 2——所有 `Z_{2^k}` 方案的挑战设计绕不开；
- **Fiat–Shamir**：域分离 transcript + 逐形状重展开（FIPS 203/204 模式）；
  FS 化的正确性依赖轮轮挑战空间的"强采样性"。

## 2. 原语 → 实现映射（本 crate）

| # | 原语 | 谁在用 | crate 内位置 | 状态 |
| --- | --- | --- | --- | --- |
| 1 | Ajtai/SIS 承诺（种子展开 key，线性同态） | 全部 | `protocols::commitment`（Z1 环）、`z2::Z2CommitKey`、`ipa::IpaKey`、`fold::FoldKey`、`short::ShortKey`、`latticefold::LfKey` | ✅ |
| 2 | uniform / CBD / centered-bounded 采样 | LNP22 系、PQC | `sampling::{uniform_poly, cbd_poly, centered_bounded_poly}` | ✅ |
| 3 | 固定重量稀疏 in-ball 挑战 | MatRiCT（`C^d_{w,p}`）、Dilithium | `sampling::in_ball_poly` | ✅ |
| 4 | 非单位线性挑战 `X − a`（`a` 奇） | Rinocchio（奇元素）、Greyhound（商多项式）、2-adic batched opening | `sampling::nonunit_linear_poly` | ✅ |
| 5 | **HyperBall 挑战向量**（`‖β‖∞ ≤ b ∧ ‖β‖₁ ≤ B`） | LaBRADOR（lattirust `hyperball`）、LNP22 掩码分布 | `sampling::hyperball_vec` | ✅ 本次新增 |
| 6 | 摊销 batched opening（掩码二次项 `m_k/q_k` 线性化） | LaBRADOR、LNP22、LaZer | `protocols::z2` | ✅ |
| 7 | Multilinear ring-sumcheck（任意交换环、无逆元） | LatticeFold/+、Greyhound | `protocols::sumcheck` | ✅ |
| 8 | Gadget-IPA（近似 opening） | Greyhound | `protocols::ipa` | ✅ |
| 9 | Gadget split + provable slack | LaBRADOR 递归、LNP22 分解 | `protocols::z2::{gadget_split, approx_linear_check, slack_bound}` | ✅ |
| 10 | **数字分解式投影/近似短性**（balanced `2^γ` split + 精确链接 + 范数门） | LaBRADOR 范数控制（`z = z₀+b·z₁`）、LNP22 分解论证、MatRiCT 范围证明 | `protocols::short` | ✅ 本次新增 |
| 11 | **b-bit balanced 批量分解**（`Z_{2^32}` 上商消失，环内精确） | LatticeFold（`split_{b,k}` + `Π*_dec` 检查）、Neo/Cyclo | `protocols::latticefold::{decompose_balanced, recompose}` | ✅ 本次新增 |
| 12 | **分解式 folding + splitting query + 同态折叠** | LatticeFold/+、ACL'22 | `protocols::latticefold::{prove_fold_decompose, verify_fold_decompose}` | ✅ 本次新增 |
| 13 | Nova 式 folding / IVC（跨项吸收、relaxed 实例） | LatticeFold Expansion、ACL'22、Nova 系 | `protocols::fold` | ✅ |
| 14 | FS transcript（域分离 + 逐形状重展开 + 非单位挑战） | 全部 | `fs` + `sampling::nonunit_linear_poly` + `algebra::crypto::transcript` | ✅ |
| 15 | 离散高斯采样（CDT） | Falcon、部分 Σ-protocols | `algebra::crypto::sampling::DiscreteGaussian` | ✅（algebra 层） |
| 16 | Rejection sampling / FS with aborts（HVZK） | LNP22、MatRiCT、Dilithium | `protocols::sigma::fs_prove`（拒绝循环） | ✅ |
| 17 | 投影论证的 JL 变体（modular JL，`Π: Z_q^{dn} → Z_q^{256}`） | LaBRADOR 完整版 | — | ⏳ 可作为 `short` 的姊妹件（l2 范数、√(128/30) gap） |
| 18 | ZK 盲化承诺（掩码 Ajtai + `u = T·w + y` 近似检查） | LaZer、LNP22、Biscuit | — | ⏳ roadmap |
| 19 | LaBRADOR 递归全链（masked 项在挑战打开前二次承诺） | LaBRADOR 完整版 | `protocols::z2` 文档标注（当前 1-bit slack） | ⏳ roadmap |
| 20 | 多断言合并 sumcheck（β/γ/α/μ/ζ 权重）、vanishing-polynomial range check | LatticeFold Π_batch | — | ⏳ `sumcheck` 的下一步 |
| 21 | 模/环切换同态（ModSwitch/缩放） | 折叠生态逐轮范数管理 | — | ⏳ algebra 层规划 |
| 22 | 强采样集/NTT-对角挑战空间 | LatticeFold、LaBRADOR（LS18） | `sampling::nonunit_linear_poly` 覆盖 2-adic 特例 | ⏳ 素数环推广 |
| 23 | Lookup/bit 参数（非算术约束） | 全部（公认弱项） | — | ⏳ 研究分支 |

## 3. 本次新增件的协议细节（与代码对应）

### 3.1 `sampling::hyperball_vec`

`{β ∈ R^k : ‖β‖∞ ≤ b, ‖β‖₁ ≤ B}` 上的拒绝采样：系数逐个 masked rejection
（`[-b, b]` 均匀），整向量 l1 超预算则重抽。确定性（XOF 驱动）、可复现（KAT 友好）。
用途：batched opening 挑战向量、folding/splitting 挑战——`‖ζ‖₁` 直接进范数门。

### 3.2 `protocols::short`（数字分解式投影论证）

语句：`c = A·w` 公开，证明 `‖w − ζ·t‖∞ ≤ certified_bound(γ, B_h)`。

```text
v = w − ζ·t
v = 2^γ·h + l        ← balanced split：精确、‖l‖∞ ≤ 2^{γ−1}
        ──h, l──▶    验证：A·(2^γ·h + l) == c − ζ·(A·t)  （精确链接）
                     ‖l‖∞ ≤ 2^{γ−1}，‖h‖∞ ≤ B_h          （范数门）
```

内容所在：链接精确 ⟹ 揭示的 `h` 就是 `v` 的真实高位（伪造者压不小它）；
binding ⟹ `(h,l)` 唯一对应 `v`（第二个可接受 digits 对给出短 kernel 向量）。
透明设计：digits 本身短，递归时可在新 Ajtai key 下再承诺。
对应文献谱系：LaBRADOR 每轮的 `z = z₀ + b·z₁` 范数控制、LNP22 的分解论证、
LatticeFold 的 quotient/residue 检查——均为"分解数字 + 范数门 + 线性恒等式"范式；
LaBRADOR 完整版的 **JL 投影变体**（l2 范数、`√(128/30) ≈ 2.07` gap、256 个
免费内积方程）是本模块的姊妹件，列为 ⏳。

### 3.3 `protocols::latticefold`（分解式折叠）

```text
r  ← H(key, c₁, c₂)                    ‖r‖∞ ≤ 1, ‖r‖₁ ≤ B_r（hyperball）
w' = w₁ + r·w₂,  c' = c₁ + r·c₂        同态折叠，‖w'‖∞ ≤ B_w(1+B_r)
d₀..d₃ ← balanced b=8 分解（L = 32/b，商 ≡ 0）
cᵢ = A·dᵢ                              ──c', {cᵢ}──▶
                                       ζ ← H(c₁,c₂,c',{cᵢ})   splitting query
d̃ = Σ ζⁱ·dᵢ                            ──d̃──▶
验证：c' == c₁ + r·c₂；c' == Σ 2^{bi}·cᵢ（精确，即 Π*_dec 的承诺版）；
     Σ ζⁱ·cᵢ == A·d̃；‖d̃‖∞ ≤ Σ B_ζⁱ·2^{b−1}（provable 门）
```

关键点：`Z_{2^32}` 上 `L·b = 32` 时分解**精确且无商**（`2^{bL} ≡ 0`）——这是
LatticeFold 选 2-adic 环的核心理由之一；digit 全部 `b`-bit 短，承诺同态性让
验证端四条检查全是线性恒等式 + 一个范数门。与原文的差距（= 后续工作）：
multilinear 求值断言 `v̂`（由 sumcheck 承担）、强采样集挑战空间、多实例 batch。

## 4. 参考实现入口

- hyperball：`crates/zk/src/sampling.rs::hyperball_vec`
- 投影论证（数字分解式）：`crates/zk/src/protocols/short.rs`
- 分解式折叠：`crates/zk/src/protocols/latticefold.rs`
- 契约测试：`crates/zk/tests/protocol_contract.rs`（projection / latticefold 两组）

## 5. 参考（eprint 已核对）

- LaBRADOR: [2022/1341](https://eprint.iacr.org/2022/1341)（CRYPTO 2023）
- Greyhound: [2024/1293](https://eprint.iacr.org/2024/1293)（Nguyen–Seiler, CRYPTO 2024）
- LatticeFold: [2024/257](https://eprint.iacr.org/2024/257)；LatticeFold+: [2025/247](https://eprint.iacr.org/2025/247)（Boneh–Chen）
- LaZer Library: [2024/1846](https://eprint.iacr.org/2024/1846)（CCS 2024）
- SLAP: [2023/1469](https://eprint.iacr.org/2023/1469)（EUROCRYPT 2024）
- Rinocchio: [2021/322](https://eprint.iacr.org/2021/322)（CCS 2022）
- Ligetron: IEEE S&P 2024, DOI 10.1109/SP54263.2024.00086（非格，对照项）
- MatRiCT: [2019/1287](https://eprint.iacr.org/2019/1287)（CCS 2019）；MatRiCT+: [2021/545](https://eprint.iacr.org/2021/545)（S&P 2022）
- LNP22: [2022/284](https://eprint.iacr.org/2022/284)；LNS21: [2020/1183](https://eprint.iacr.org/2020/1183)；BLOOM: [2022/1307](https://eprint.iacr.org/2022/1307)；LS18 可逆性引理: [2017/523](https://eprint.iacr.org/2017/523)；FS with aborts 分析: [2023/245](https://eprint.iacr.org/2023/245)、[2023/246](https://eprint.iacr.org/2023/246)
- 折叠生态：Lova [2024/1964](https://eprint.iacr.org/2024/1964)；Neo [2025/294](https://eprint.iacr.org/2025/294)；SuperNeo [2026/242](https://eprint.iacr.org/2026/242)；SALSAA [2025/2124](https://eprint.iacr.org/2025/2124)；Symphony [2025/1905](https://eprint.iacr.org/2025/1905)；Cyclo [2026/359](https://eprint.iacr.org/2026/359)；LatticeBlindFold [2026/1857](https://eprint.iacr.org/2026/1857)；LatticeFold+ ℓ₂-norm 改进 [2026/721](https://eprint.iacr.org/2026/721)
- NIST FIPS 203/204（CBD / SampleInBall / rejection 采样的参考语义）
