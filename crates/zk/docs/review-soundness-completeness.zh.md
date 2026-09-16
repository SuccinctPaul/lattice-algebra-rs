# Soundness & Completeness 评审报告（zk crate）

> 评审对象：`crates/zk` 全部协议域（commitment / sigma / opening / sumcheck+ipa /
> shortness / folding），方法为逐行对抗性分析 + 可执行测试钉死关键论断。
> 结论按域给出；发现项（Finding）编号 F1–F5，已知取舍 K1–K4。
> 本报告对应提交：sumcheck FS 绑定修复、χ-奇偶钉死测试、文档强化（同一 PR）。

## 0. 总体结论

- **completeness**：所有协议的诚实路径测试全绿；唯一的补全性 API 缺陷
  （`RelaxedInstance::satisfying` 生成 `verify_folded` 必拒的实例）已修复（F3）。
- **soundness**：发现一个真实的 API 级 soundness 缺陷并已修复——
  sumcheck 的挑战流未绑定轮次消息（F1，见下）；其余协议 soundness 论断
  经复核成立，其中 Z2/IPA 的约束检查被精化为"单比特"语义（F2），比原文档
  更尖锐但方向一致；LaBRADOR 递归仍是对应的必要里程碑（K1）。
- 全部门禁通过：fmt / clippy `-D warnings` / rustdoc `-D warnings` /
  workspace 全量测试（670+，0 失败）。

## 1. 分域评审

### 1.1 `commitment`（AjtaiKey / ajtai）

- **binding**：两次打开 → `A(s − s′) = 0` 短 kernel 向量 → MSIS。`A` 由种子
  展开、N ≥ 覆盖行数时 overdetermined。✅
- **hiding**：Ajtai 承诺**不隐藏**（确定性、无噪声）——crate 全线 transparent，
  文档如实。✅
- 测试：determinism、discrimination、witness bound。✅

### 1.2 `sigma`（Lyubashevsky FS-NIZK）

- **completeness**：拒绝循环接受率 ~40%（`B_Y − τB_S` 记账），128 次上限
  统计上不可达；失败返回类型化 `RejectionLimit`，无 panic 路径。✅
- **soundness**：forking 抽取器 → relaxed 关系 `A·s_ext = v·t`，
  `‖s_ext‖∞ ≤ 2B_Z`、`‖v‖₁ ≤ 2TAU`——测试逐条断言。✅
- FS 绑定：挑战由 transcript（key, t, w）派生，先承诺后挑战。✅
- 已知：参数定标（lattice-estimator）为开放项（K4）。

### 1.3 `opening`（LaBRADOR 式 batched opening）

- **completeness**：诚实公式 `res = C·m + C²·q` 精确成立；10⁴ gate 端到端
  绿。✅
- **soundness（复核后的精确刻画，F2）**：
  - binding link `A·z′ == c + C·d` 精确且 overdetermined，`z′` 被唯一钉住
    （MSIS 下）；
  - masked-consistency `Σγ^k R_k == C·t* + C²·q*`：系数和 mod 2 的映射
    `χ(f) = Σf_i` 是良定义同态 `R → F_2`（kill `2` 与 `X^64+1`），
    `χ(C) = 1−a ≡ 0` ⟹ `C·R = ker χ = {Σ coeffs even}`（指数 2，
    Norm `N(C) = a^64+1` 的 `v_2 = 1` 交叉验证）。由于 χ 可乘，
    该方程等价于**单比特**
    `χ(R_0) + χ(γ)·Σ_{k≥1}χ(R_k) = 0` —— 两个 F_2-线性泛函。
  - 推论：假响应每轮 mask 磨着通过率 ~½；且当假见证的 χ-像满足这些线性
    条件时确定性通过。**这不是文档早先暗示的 2^-32 关系可靠性**——
    完整关系 soundness 必须走 LaBRADOR 递归（K1）。
  - 挑战为非单位（`X − a`，a 奇）的论证成立（单位挑战会使方程对任意
    响应可解——已有回归测试钉死）。✅
  - 测试：`verifier_equation_is_single_bit_parity` 钉死 χ 语义
    （诚实 = 0；gate 0 翻转；k ≥ 1 在 χ(γ)=0 时不可见）；
    `forged_statement_rejected_despite_binding_link` 钉死一般伪造。✅

### 1.4 `sumcheck` + `ipa`

- **sumcheck（F1，本次修复的实质缺陷）**：原 API 接受任意
  `FnMut() -> R` 挑战闭包，协议安全性**要求**轮次挑战在吸收轮次消息之后
  派生。消息无关的挑战流下，提前知道全部挑战的伪造者可为任意"自己的
  表 + 任意和"构造全通过的消息序列——单独使用时是全量破坏。
  **修复**：引入 `RoundChallenger` trait（契约：先吸收 `(h0,h1)`）+
  `FsChallenger` 参考实现（域分离 transcript，Display 编码长度前缀吸收，
  `MatrixElement::random` + XOF→RngCore 桥接映射挑战）；prove/verify
  签名改为 `&mut dyn RoundChallenger<R>`；新增回归测试
  `forged_table_fails_under_fs_binding`。
- **ring-SZ 注意**：环上有零因子，单轮失败概率 ≤ `|ann(Δ₁)|/|R|` ≤ 1/2
  （最坏），G 轮乘法放大；文档已如实标注，独立部署建议用域挑战。✅
- **ipa**：同 F2 的单比特语义（文档已同步修正）；binding link 精确；
  `forged_inner_product_claim_rejected` 回归测试存在（单位挑战回归）。
  补全性：roundtrip 测试覆盖。✅

### 1.5 `shortness`（balanced 投影论证 + gadget）

- **soundness**：平衡拆分 `v = 2^γ·h + l` **精确**（环内逐系数无进位），
  链接 `A·(2^γh + l) == c − ζ·(A·t)` 精确 ⟹ 揭示的 `h` 即真实高位；
  digit 门 + binding ⟹ `‖v‖∞ ≤ 2^γB_h + 2^{γ−1}` 可证。伪造者无法缩小
  高位（精确链接强制）。✅
- **completeness**：split 精确（`γ ∈ [1,32)` 全扫描测试）+ 低位门按构造
  成立。✅
- **F4（修复）**：`verify_projection` 对 `γ = 0` 位移会 panic（不可约拒绝
  路径），已在信任边界加参数校验返回 `false`。

### 1.6 `folding`（nova + latticefold）

- **nova**：折叠代数（跨项 `T_k`、误差 `e′ = e₁ + rT + r²(e₂ + U∘z₂sel)`）
  经 `r = 0` 恒等、链式折叠、篡改拒绝测试验证；`verify_folded` 为透明
  验证（重算承诺 + 精确残差比较），soundness 即诚实验证本身。✅
  **F3（修复）**：`RelaxedInstance::satisfying` 原实现置空承诺向量——
  构造出的实例**必被** `verify_folded` 拒绝（补全性陷阱）。已改为
  `FoldKey::satisfying(r1cs, z)`：从 key 派生承诺 + debug 断言门满足。
- **latticefold**：分解 `w = Σ2^{bi}dᵢ` 在 `Z_{2^32}` 上精确（`L·b = 32`
  时商项 ≡ 0，逐系数贪心 + 环重建断言）；四条验证检查中三条为精确线性
  恒等式、一条为可证范数门 `‖d̃‖ ≤ ΣB_ζⁱ·2^{b−1}`；伪造 digit 集需同时
  满足两个线性系统 + 范数门（拆分查询在 digit 承诺之后）。✅
  已知（K3）：这是 LatticeFold 批量分解 + splitting query 的简化核——
  单个 digit 的范数未单独认证（仅认证 ζ-组合），完整 SZ 抽取论证未复现。

## 2. 发现与处置

| # | 级别 | 内容 | 处置 |
| --- | --- | --- | --- |
| F1 | 高（API 误用即破坏） | sumcheck 挑战未绑定轮次消息；消息无关挑战流下可为任意和伪造证明 | ✅ 修复：`RoundChallenger`/`FsChallenger` 强制先吸收后派生；全部调用方迁移；回归测试钉死 |
| F2 | 中（文档弱化 + 精化） | Z2/IPA 的约束检查实为**单比特** χ-奇偶认证（χ 同态 + Norm 交叉验证）；每 mask 磨着 ~½，线性条件下可确定性通过 | ✅ 文档精化 + `verifier_equation_is_single_bit_parity` 钉死；根本解为 K1 |
| F3 | 中（补全性陷阱） | `RelaxedInstance::satisfying` 产出必被拒绝的实例 | ✅ 改为 `FoldKey::satisfying`，派生真实承诺 |
| F4 | 低 | `verify_projection(γ=0)` 位移 panic | ✅ 信任边界参数校验，返回 `false` |
| F5 | 低（已文档化） | hyperball 挑战预算不可行时 `expect` panic（FS 派生双侧一致，不破坏一致性；属参数前置条件） | 📋 建议：后续提供 `Result` 变体 |

评审过程说明：F2 的分析经历了"评估点 `f(a)` 刻画"的错误假设——被新测试
直接证伪（负循环商环上 `f ↦ f(a)` 不是良定义同态，需 `a^64+1 ≡ 0`），
最终以 χ-同态 + Norm 交叉验证得到正确刻画。错误的中间版本未进入提交。

## 3. 已知取舍（文档如实标注、非回归）

- **K1**：Z2/IPA 的完整关系 soundness 需要 LaBRADOR 递归（masked 项在
  挑战打开前二次承诺）——roadmap 里程碑；当前单比特语义已精确文档化。
- **K2**：ZK 盲化（blinding commitments）deferred——Z2/Z3/Z5 为 transparent
  证明，协议不隐藏见证。
- **K3**：`latticefold` 为 LatticeFold 批量分解 + splitting query 的简化核；
  multilinear 求值断言（sumcheck 承担）与完整 SZ 抽取未复现。
- **K4**：具体安全级未宣称；estimator 校准开放（`algebra::security` 已有
  Core-SVP 底座）。

## 4. 测试与门禁证据

- 单元测试 64 个（含新增 `forged_table_fails_under_fs_binding`、
  `verifier_equation_is_single_bit_parity`）+ 契约测试 6 个 + doc 测试；
- `cargo fmt --check`、`cargo clippy --all-targets -- -D warnings`、
  `RUSTDOCFLAGS="-D warnings" cargo doc` 全绿；
- workspace 全量 `make gate` 通过。
