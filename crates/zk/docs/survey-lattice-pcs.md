# Lattice Polynomial Commitment Schemes — the landscape beyond Greyhound

> Companion to [`survey-lattice-zksnarks.md`](survey-lattice-zksnarks.md) (the
> primitive-level survey). Scope: **polynomial commitment schemes (PCS) built
> from lattice assumptions** — the question "besides Greyhound, what else is
> there" — plus the corrections and trends a fresh literature pass produced.
> Data collection date **2026-09-22**; every eprint number below was opened
> and re-checked against the eprint page on that date. Performance figures are
> **as reported by the papers themselves** (self-measured, not horizontally
> comparable); items that could not be verified from a primary source are
> marked. Notation follows the crate: `d` = ring degree, `N` = committed
> polynomial size, `λ` = security parameter.

## 0. One-paragraph answer

Greyhound (2024) is no longer alone: between mid-2025 and September 2026 the
lattice-PCS count roughly **tripled**. The verified landscape beyond Greyhound
is: **SLAP** and its Journal-of-Cryptology follow-up (tree-based, extractable),
**Rinocchio** (ring commitments, designated verifier), **CELPC** (√-size
proofs), **CMNW** (size-optimized univariate), **Orbweaver** (the one
trusted-setup entry, k-R-ISIS), **Serval** (slack-free ℓ2 soundness), and the
2026 wave — **Hachi** (extension-*field* sumcheck + a ring-switching
quotient), **Maltese**
(Ajtai-Merkle + folding, ASIACRYPT 2026), **Akita** (split-and-fold with exact Euclidean norm checks, active Rust
implementation), **Grand Danois** (vSIS +
random projections), and **Jindo** (evaluation hiding). Three trends define the
frontier: **slack-free exact-ℓ2 soundness** replacing ℓ∞-slack gates,
**sumcheck fusion** (norm checks, norm-growth control and folding all riding
sumcheck), and a **verifier-time race with Greyhound as the baseline**. What
this crate implements from that toolbox today: the Greyhound two-layer Ajtai
PCS with the √N split (`pcs::greyhound`) and the shared-point batched opening
(`pcs::batched`) — see §4.

## 1. Comparison table (all verified against eprint pages, 2026-09-22)

Sorted by lineage: the established line first, the 2026 wave second.

| Scheme | Authors / venue / eprint | Assumption | Commitment structure | Poly type | Setup | Reported figures (their numbers) | Code |
| --- | --- | --- | --- | --- | --- | --- | --- |
| **LaBRADOR** | Beullens–Seiler, CRYPTO 2023, [2022/1341](https://eprint.iacr.org/2022/1341) | MSIS | two-layer Ajtai + amortized batched opening | (R1CS arguments, not a PCS) | transparent | 58 KB @ 10⁶ constraints | [lattice-dogs/labrador](https://github.com/lattice-dogs/labrador) (C), lattirust, Lazarus (Rust) |
| **Greyhound** | Nguyen–Seiler, CRYPTO 2024, [2024/1293](https://eprint.iacr.org/2024/1293) | MSIS | two-layer Ajtai over gadget digits, √N split | univariate | transparent | 53 KB eval proofs @ N = 2³⁰ | `greyhound.c` in lattice-dogs/labrador; Lazarus `greyhound` crate (Rust port) |
| **SLAP** | Albrecht–Fenzi–Lapiha–Nguyen, [2023/1469](https://eprint.iacr.org/2023/1469) (page states **"Preprint."** — no venue; re-checked 2026-09-24) | h-PRISIS (multi-instance Power-Ring-BASIS) reduced to Module-SIS, ROM | Ajtai hash **tree** (additive root accumulation, *not* sibling-path Merkle), split-and-fold | univariate | **trusted setup** (trapdoors) | polylog verifier, extractable | none public |
| **Fenzi–Moghaddas–Nguyen (PowerBASIS)** | Fenzi–Moghaddas–Nguyen, Journal of Cryptology 2025, [2023/846](https://eprint.iacr.org/2023/846) — **this is the base SLAP builds on, not its follow-up** (2026-09-24 correction, read off Fig. 4 + SLAP §4's own "combines the BASIS construction [FMN23] with Merkle trees") | ring-BASIS + statistical NTRU | **flat, NOT tree-based**: one `SamplePre` under the (d+1)-block power-basis matrix `B := [A −G; … ; W^dA −G]`, `W ← GL(n, R_q)` a **unit matrix**. "Merkle" occurs **once** in the entire 196 KB text, in a remark about combining with trees. `Open` accepts iff `∀i∈[0,d]: A sᵢ + fᵢe₁ = W^{−i}t` **and** `‖cᵢsᵢ‖ ≤ γ`, slack `cᵢ ∈ R_q^×, ‖cᵢ‖∞ ≤ β_s` | univariate | no preprocessing | 17 MB SNARK proof @ 2²⁰ R1CS | none |
| **Rinocchio** | Ganesh–Nitulescu–Soria-Vazquez, [2021/322](https://eprint.iacr.org/2021/322) (page states **"Preprint. 2021-03-11: received"** — no venue; the widely-copied CCS 2022 attribution is **not** supported by the primary source; re-checked 2026-09-24) | **not ring-SIS — the string "SIS" never occurs in the paper**: generalized q-PDH + augmented q-PKE + *conjectured* linear-only extractability, with LWE/Regev (or TLWE, or 2^k-residuosity) only for hiding | noisy RLWE/Regev ring encodings, image check under `sk` | QRP (QAP over rings) | **trusted linear-size SRS** | 9 encodings, linear in the witness | none published; designated verifier holds `sk`, and there is **no Fiat–Shamir and no ROM anywhere** in the scheme |
| **CMNW** | Cini–Malavolta–Nguyen–Wee, [2024/281](https://eprint.iacr.org/2024/281) (citation line is "Cryptology ePrint Archive, Paper 2024/281" — no venue; re-checked 2026-09-24) | Module-SIS, ROM (knowledge soundness also in the **QROM**); concrete part needs **q ≡ 5 mod 8** | nested-gadget Ajtai hash — **neither a Merkle tree (no sibling hashes) nor a code domain: no TrapGen, no RS/expander code** | univariate | transparent | 2× smaller than FRI, 70× smaller than SLAP-line @ L = 2²⁰ | none |
| **CELPC** | Hwang–Seo–Song, CRYPTO 2024, [2024/306](https://eprint.iacr.org/2024/306) | standard lattice | homomorphic-friendly lattice commitments | univariate | transparent | √-size proofs; 4.1× smaller than SLAP | none |
| **Orbweaver** | Fisch–Liu–Vesely, CRYPTO 2023 (rev. 2024-12), [2024/2026](https://eprint.iacr.org/2024/2026) | **k-R-ISIS** (knowledge) | structured-SRS linear-functional commitments | univariate **and** multilinear | **trusted universal SRS** | 302 KiB–1.6 MiB @ 2³⁰; polylog verifier | none |
| **Serval** | Zhang–Chow–Gao–Xiao, [2025/1903](https://eprint.iacr.org/2025/1903) (rev. 2026-03) | **M-SIS only** (the abstract's "SIS/LWE-type" is loose — LWE appears nowhere else) | **slack-free ℓ2**: self-inner-product + binary validation in one divide-and-conquer | (argument system) | n/s on page | raw 5.45 MB / "Opt." 436 KB @ L = 2²⁰, vs FMN 3.4 MB and SLAP 36.5 MB — **the Opt. column is an analytic LaBRADOR estimate and the FMN/SLAP figures are re-derived from Cini et al.; none is measured** | [gitlab.com/LatticePCSReview/servalPCS](https://gitlab.com/LatticePCSReview/servalPCS): **public Python prototype** (baseline protocol, no FS/LaBRADOR) — corrects this survey's earlier "no public repo" |
| **Hachi** | Nguyen–O'Rourke–Zhang, [2026/156](https://eprint.iacr.org/2026/156) | Module-SIS (ℓ∞) + Lyubashevsky–Seiler short inverse (**needs q ≡ 5 mod 8**), ROM | two-layer Ajtai + **ring-switching quotient `r`** (`Mz = y + (X^d+1)r`), sumcheck over the extension **field** `F_{q^k}` | multilinear | transparent | verifier Õ(√(2^ℓ·λ)) *field* ops; ℓ=30: q=2³²−99, d=2¹⁰, k=4 → 55.1 KB / 227 ms @ λ=128 | [LatticeProofs/Hachi](https://github.com/LatticeProofs/Hachi) (Rust, fixed params, AVX-512); README disagrees with its own HEAD on the gate degree |
| **Maltese** | Cheng–Nguyen–Tyagi, **ASIACRYPT 2026** (confirmed on the page), [2026/2067](https://eprint.iacr.org/2026/2067) | plain **MSIS** only | nested Ajtai hash `H(m)=A·G⁻¹(m)` in a tree — "you can *view* this as a Merkle tree", but commitments are **deterministic gadget preimages**: 0 occurrences of TrapGen/SamplePre in 90 pp ("trapdoor"/"trusted setup" appear only in reference titles), and **no authentication path is ever sent**; + folding with sumcheck norm-growth control | multilinear | **transparent** | 335 KB @ N=2³⁰ (P3: log q=32, d=64, e=8, n=32, b=2, k=7, ω=6 cycles, no heuristic; P4's 224 KB needs the dense-ternary heuristic). "~300× smaller" is against CMNW's >100 MB polylog row only — vs SLAP 767 MB it is ~2300×, and **vs RoKoko's 187 KB Maltese is 1.8× larger** | none found |
| **Akita** | Dao et al., [2026/1983](https://eprint.iacr.org/2026/1983) (rev. 2026-09-18) | Module-SIS with **exact Euclidean norm checks** | split-and-fold ("root-to-tail"); 128-byte commitments; setup offloading | multilinear | transparent | 61–72 KB proofs (Greyhound-parity size); verifier 19.2–89.7× faster than Greyhound | [LayerZero-Labs/akita](https://github.com/LayerZero-Labs/akita) (Rust, active; `akita-transcript`/`-sumcheck`/`-algebra`/`-planner` crates) |
| **Grand Danois** | Kallesøe–Khoshakhlagh, [2026/1196](https://eprint.iacr.org/2026/1196) (rev. 2026-08, page says **Preprint**) | **vSIS** — and **Def. 2.2 does state it** (2026-09-24 correction; this row previously claimed "vanishing is never defined", which is wrong): vSIS_{q,d,n,β} "adapted from [CLM23]" is defined as `Pr[A←$X_{n,µ}, w←A(A): Aw = 0 mod q ∧ 0 ≠ ‖w‖ ≤ β] ≤ negl`, i.e. the assumption is **indexed by** a distribution `X_{n,µ}` over `R_q^{n×2^µ}`, glossed in Table 1 as "vSIS-friendly". What is genuinely missing is a **sampler** for `X_{n,µ}` and a reduction from Module-SIS to it — so hardness is assumed *relative to whichever distribution the construction picks*, and an implementation must name its own | depth-2 Ajtai (not a tree) + `Π = (I_r⊗J')(I_{ȷr}⊗J)` JL against **ℓ2 mod q** (ratio [30,337], extractor slack √(337/30) ≈ 3.35) + rotation matrices `M_a` making a row fold O(d) instead of O(d²); the tensor structure the verifier actually leans on is the product form `β_{M}α(e) = (β⊗α) Π_i (I_d(1−e_i) + M_{1,i}e_i) …` | multilinear | transparent CRS `(A,B,D)`, no trapdoor | **80–90 KB @ 2³² is an estimate, not a measurement** — the paper has no parameter table, no runtime, and says parameters are future work; "O(λℓ) verifier" is an informal claim with no bounding theorem | none |
| **Jindo** | Hwang–Lee–Seo–Song, [2026/044](https://eprint.iacr.org/2026/044) (rev. 2026-06) | lattice (RLWE in application) | extends CELPC + Greyhound with **evaluation hiding** (sublinear masking) | multilinear + univariate | n/s on page | ~10× better than CELPC; ~10× proving / ~100× verification vs LaZer | claimed, no public link |

**Not lattice — listed to preempt the recurring confusion**: WHIR
([2024/1606](https://eprint.iacr.org/2024/1606)), BaseFold (CRYPTO 2024),
FRI-Binius ([2024/1724](https://eprint.iacr.org/2024/1724)) and **DeepFold**
(USENIX Security 2025, [2024/1595](https://eprint.iacr.org/2024/1595)) are
**Reed-Solomon/Merkle-based** ("post-quantum via hashing", no algebraic
assumption). DeepFold in particular is routinely cited as a lattice PCS — it
is not; it is BaseFold-lineage. The lattice line buys shorter proofs and
smaller fields at the price of MSIS-type assumptions and norm management.

**Withdrawn / superseded**: HyperWolf ([2025/922](https://eprint.iacr.org/2025/922))
was withdrawn 2025-10-03 and superseded by Serval from the same group; Neo
([2025/294](https://eprint.iacr.org/2025/294)) is formally superseded by
**Neo & SuperNeo** ([2026/242](https://eprint.iacr.org/2026/242), CRYPTO 2026) —
cite the latter.

## 2. What each new scheme contributes at the primitive level

Primitives only (extractable as modules), not paper-specific engineering:

- **Hachi**: two algebra objects our survey previously conflated. (1) the
  sumcheck runs over the **extension field** `F_{q^k} = F_q[Z]/(φ)`, `φ`
  irreducible of degree `k` (the reference impl uses `φ = X⁴−2`, elements as
  `[u32;4]`) — **not** "extension rings `F_q^k[X]`" as first written here;
  (2) a **subfield of the ring** `R_q^H = Fix(H)`, `H ≤ Aut(R_q)`, needing
  `k | d/2`, with the packing `ψ : (R_q^H)^{d/k} → R_q` and
  `Tr_H(ψ(a)·σ₋₁(ψ(b))) = (d/k)⟨a,b⟩`. The √ verifier comes from the
  verifier's only heavy step being a DP evaluation over *fields*, so it
  avoids the extra factor `λ` Greyhound pays for ring ops.
  What this survey called a "residual technique" the paper calls **`r`, the
  quotient from ring switching** (attributed to HMZ25; the word "residual"
  appears nowhere in 2026/156): `Mz = y` in `R_q` iff there is `r` with
  `Mz = y + (X^d+1)·r` over `Z_q[X]`, `r` is gadget-decomposed and norm-gated,
  and `M̃_α(i,u) = −(α^d+1)` folds it into the *same* sumcheck as the
  relation — one argument for both, at soundness error `(2d−1)/|F_{q^k}|`.
  Correction on the gate: `c_bal = (w²+8w)·∏_{k=1..7}(w²−k²)` is
  **degree 16, not 18** — it is exactly `∏_{i=−8..7}(w−i)`, the centered
  16-digit set `{−8,…,7}`; 18 = 16 + deg ẽq + deg 1_{≤μ} is the *composed*
  round polynomial, which is where the earlier count went wrong. Verified
  here: `sumcheck::range`'s new `centered_vanishing_eval(·, 16)` agrees with
  that closed form at 81 field points
  (`hachi_balanced_gate_is_our_centered_vanishing_polynomial`). Note the
  gate needs a **field** (no zero divisors), so it is unavailable over our
  2-adic ring. Parameters: `q = 4294967197 = 2³²−99`, which is `≡ 5 (mod 8)`
  as the Lyubashevsky–Seiler short-inverse lemma requires — and therefore,
  per `algebra::ring::number_theory::x_pow_d_plus_1_splitting`, `X^1024+1`
  splits into **two** degree-512 factors, the opposite of our Z1 ring.
- **Akita**: (a) *exact Euclidean norm checks inside parameter selection* —
  and note this is **not** a JL argument: the paper states outright that it
  "uses no Johnson–Lindenstrauss projection", checking instead the exact
  integer identity `E_int = Σ (centered lift)² == E_resp ∧ E_resp ≤ S_max`
  (their §6.2). Landed as `shortness::exact_l2`, whose direct route is valid
  only while `S_max < q` and which refuses rather than guess past that; the
  digit-plane Gram fallback is **not** implemented. Their reference
  implementation also reports that a *dense ±1* JL projection mismatches the
  certified lower tail and switches to sparse-ternary with slack
  `√(128/29)` — we cite `√(128/30)` in `shortness::projection`, a different
  distribution's constant that still needs checking against GHL21.
  (b) *setup offloading* (verifier work on public matrices deferred and
  proved against commitments); (c) *batched openings of independent
  polynomials* — the primitive `pcs::batched` implements the core-shape
  version of, and `pcs::mle::batch_verify` the cross-table version; (d) a
  *planner* crate (automated parameter/schedule DP over whole schedules, not
  just sizes) — an engineering idea worth copying. The paper never writes
  "split-and-fold" for its mechanism: "root-to-tail" is §1.1's phrase for
  whole-recursion tuning; the actual fold is a canonical coefficient split
  with **per-role ring dimensions** `(d_A, d_car, d_B, d_D)`, which our
  single-constant `pcs` instance cannot express (see
  `open-milestones.md` G1).
- **Serval**: exact-ℓ2 enforcement reduced to a *self-inner-product argument
  + binary validation avoiding modular wraparound* — most relevant over
  2-adic rings, where wraparound is exactly the failure mode.
- **Maltese**: sumcheck-based control of norm growth across folding rounds —
  a refinement of the LatticeFold decomposition loop.
- **Grand Danois**: *rotation matrices* so the verifier folds constraint rows
  in time linear in the ring degree (not d²) — note the assumption change to
  vSIS.
- **Jindo**: *evaluation hiding* — sublinear masking that makes PCS openings
  zero-knowledge; the cheapest published ZK option for our transparent PCS.
- **SLAP/CMNW/CELPC**: the tree/Ajtai-hash line — extractability and
  Brakedown-class proof sizes; complements (does not supersede) the
  LaBRADOR amortized-opening line.

## 3. Trends since mid-2025 (what to track)

1. **Slack-free exact-ℓ2 soundness** (Serval, Akita, Osadnik's LatticeFold+
   ℓ2 note [2026/721](https://eprint.iacr.org/2026/721)) replacing
   slack-tolerant ℓ∞ gates — enables tighter MSIS parameters.
2. **Sumcheck fusion**: norm checks (SALSAA, [2025/2124](https://eprint.iacr.org/2025/2124)),
   norm-growth control (Maltese), and folding of double commitments
   (RoKoko, [2026/575](https://eprint.iacr.org/2026/575)) all ride the
   sumcheck — converging with this crate's `sumcheck` domain.
3. **Verifier-time race with Greyhound as the baseline** (Hachi, Akita,
   Grand Danois, RoKoko all quote it).
4. **The lookup gap is closing**: [2026/471](https://eprint.iacr.org/2026/471)
   (Bootle–Guskind–Patranabis–Sotiraki, 2026) is the first lookup-argument
   framework over rings (`Plookup`/`LogUp`-style IOPs over `Z_q[X]/(X^d+1)`),
   including a proof that naive field-to-ring translations break on
   zero divisors. Caveats: prime-ring statement (not 2-adic — our
   `Z_{2^32}[X]/(X^64+1)` has the exact zero-divisor surface the paper
   warns about), and not yet integrated into any folding scheme. This is the
   research entry for survey ⏳ item 23.

## 4. What this crate adopts (implementation map)

Status as of 2026-09-22, after reading the LaBRADOR / SLAP / Hachi / Akita
primary sources. The headline is that §1's schemes are **not** blocked on
per-scheme glue but on a short list of missing `src` capabilities — the
architecture puts capabilities in `src` and assembles schemes in
`examples/`, so a missing capability blocks every scheme that needs it. The
gaps are itemized as G1–G6 in
[`open-milestones.md`](open-milestones.md).

| Landscape primitive | Status here | Where |
| --- | --- | --- |
| Greyhound two-layer Ajtai commitment + √N split evaluation (five link equations + norm gates) | ✅ core-size proof (LaBRADOR compression deferred) | `pcs::greyhound` |
| σ-automorphism packing (removes the factor-`d` size overhead) | ✅ packed mode, scalar coefficients and scalar points | `pcs::packing`, `pcs::{commit_packed, open_packed, verify_packed}` |
| Batched opening at a shared point (HyperBall weights, single combined `z`) | ✅ core-size batched proof | `pcs::batched` |
| Opening against a **non-factored** weight table `y = ⟨w, F⟩` (the shape the sumcheck line lands in) | ✅ tall-key mode; Σ opening per claim, transparent not hiding | `pcs::mle` (`open_mle_proof`/`verify_mle_proof`) |
| Multi-claim reduction Σ λᵢyᵢ = ⟨Σ λᵢwᵢ, F⟩ (cross-point / cross-table batching) | ✅ one opening per batch under a transcript-derived γ | `pcs::mle::{combined_claim, open_claims, batch_verify}` |
| Shared samplers: HyperBall challenge vectors, ternary challenges | ✅ | `foundation::sampling` |
| Scheme-facing abstraction so an example is an assembly, not a reimplementation | ⚠️ **the seam exists but is single-user** (corrected 2026-09-24, measured): all four implementors are `impl Pcs/BatchPcs for GreyhoundKey`, `impl Pcs for PackedGreyhound`, `impl WeightPcs for MleKey` — every one of them written inside `api.rs` itself, and **no example implements or calls any of them**. Worse, `WeightPcs` requires `value_of(com, weight)`, which only a **tall** key can answer (`MleKey` does, via `mle`'s witness recovery), so short-key schemes (Orbweaver's `2W−1` power window, CELPC's plain Ajtai) cannot satisfy the signature at all. **DONE since (2026-09-24, same session):** `value_of` **and** the `mask_seed` on `open` moved out of `WeightPcs` into a new **`WeightPcsExt`** — both are capabilities of the tall-key mode, not of a weight-table PCS — and `examples/orbweaver.rs` now implements the slimmed base trait, i.e. a *structurally different* second scheme: trusted power-window SRS, `PreVerify` keyed by the functional itself, `(π₁, π₀)` response pair. Measured: the trait's `commit` equals §4's free-function `Com`, its `open` reports `ring_dot(f,x)`, the honest proof **verifies through the trait**, and a false `y` is refused **naming E2 through the trait**; `orbweaver` example green, `protocol_contract` **14/14**, `greyhound_pcs` green. Still open: `BatchPcs` has one implementor. Earlier evidence for this row's diagnosis: `open-milestones.md` §"`pcs::api` 这条「方案抽象」其实是空的" | `pcs::api::{Pcs, BatchPcs, WeightPcs, WeightPcsExt}` |
| Ring selection by `X^d+1` factorization pattern (complete split vs two degree-`d/2` factors) | ✅ incl. prime search for a requested pattern | `algebra::ring::number_theory::{x_pow_d_plus_1_splitting, find_prime_for_splitting}` |
| Vanishing-polynomial range/bit gate, **symmetric** digit set `[−b, b]` | ✅ exact over prime rings, batched into `sumcheck::batch` | `sumcheck::range` |
| Vanishing gate for the **centered** digit set (Hachi `c_bal`, balanced base-`b`) | ✅ `centered_vanishing_eval(·, 16)` verified equal to the published closed form at 81 points; needs a field, so unusable over `Z_{2^32}` | `sumcheck::range::{centered_digits, vanishing_eval_interval, centered_range_claim_table}` |
| Exact-ℓ2 (slack-free) gate — Akita's `E_int == E_resp ∧ ≤ S_max` | ✅ **both encodings of the Euclidean route land**, and the choice is the paper's own: `max{U_dir, S_max} < q` (p. 69: "the direct route is admissible only when…"), shared by `shortness::exact_l2::select_route` and `pcs::norm_route::select` so the two cannot drift; Eq. (120)'s single field identity for the admissible case, Eqs. (121–123)'s digit-plane Gram recombination otherwise (measured in `examples/akita.rs`: a `U_dir = 682 112 < p32` schedule decides Direct, a `U_dir = 1.93·10²⁰` one decides DigitExpanded with an 11-byte energy encoding and 264 Gram claims). `check_direct` mirrors Lemma 6.3's three legs (canonical decoding into `[0,S_max]`, the admissibility window, equality with the transmitted claim). **Still not here**: p. 64's *coefficient route* (which feeds the A-collision radius of Eq. (79) to the Module-SIS estimator) — `NormRoute` has no such variant, so "both §6.2 routes" would overstate; and Eqs. (126)–(128)'s `π` binding of the sum-check's final evaluations into the committed witness | `shortness::exact_l2` + `pcs::norm_route` |
| Self-inner-product argument (Serval's `ct(⟨s,σ(s)⟩) = b` divide-and-conquer, 4 ring elements/round) | ✅ arithmetic core + the **leveled binding**, 15 tests. `prove_bound`/`verify_bound` run Fig. 3's commitment column and quadratic column on **one** challenge sequence (§3.4, p. 14), so the terminal identity is evaluated on the tail `LeveledAjtai::check_lane` authenticated and `b` is a statement *about `cm`*; a bound proof for one digit vector refuses under another's root (`RootMismatch`) and a spliced chain-of-`s1`/quadratic-of-`s2` proof dies on the base opening `A₀·s_logN = …`. The bare `prove`/`verify` still proves chain-consistency only, and that is deliberate — `examples/serval.rs` demonstrates the difference. Soundness of the bound statement remains conditional on M-SIS hardness at the caller-supplied `β` (Eq. 4) | `shortness::self_ip`, `pcs::leveled::LeveledAjtai::check_lane` |
| Block-diagonal (tensor) keys `(I_m ⊗ A)` with tree chaining | ✅ one small `A` applied per block, bottom-up `commit_tree`, binary preimages, level labels domain-separated | `pcs::nested::TensorGadget` |
| NTT-free, heap-sized Ajtai keys generic over `(scalar ring, ring degree)` | ✅ schoolbook matvec, ExpandA-compatible derivation, cross-checked against `algebra::module::ModuleMatrix::mul_vec`; **works on `q = 2³² − 99`, whose 2-adicity is 2 so no NTT-backed key can exist at all** | `pcs::key::RingMatrixKey` |
| Mixed row/column contraction `(I_m ⊗ xᵀ)M` / `(cᵀ ⊗ I_k)M` + the either-order law | ✅ 7 tests, the law checked against an independent Σᵢⱼ expansion **and re-checked on `q = 2³² − 99` (`q ≡ 5 mod 8`, no NTT)**; CMNW steps 1/3/9, Maltese folding and Danois row folding all read as these two contractions | `pcs::mixed::BlockMat<R, D>` |
| σ-automorphism `X ↦ X⁻¹` and the `const(g·σ(h)) = Σ gₖhₖ` pairing, generic over `(R, d)` | ✅ `sigma_of`/`pairing_of`; the concrete Z1/d=256 forms are now thin wrappers, and `σ` having order two is what lets Serval's `σ⁻¹` be read directly | `pcs::packing::{sigma_of, pairing_of}` |
| Coefficient-level (**field**) random matrices and the ring ↔ coefficient bridge — CMNW's approximate range proof, and the same shape Grand Danois' `Π` and Maltese's folding need | ✅ 14 tests. No ring-level matrix can express these: a ring element acts by `d`-banded circulant multiplication, while `P ← χ^{λ×r₂nαd}` mixes coefficients across the negacyclic block. The bridge `const(Σₗ σ(nₗ)·eₗ) = ⟨ñ, ẽ⟩_{Z_q}` (the sentence under CMNW Eq. 21) is tested against an independent `BlockMat` contraction; writing it caught a real bug — `PolyRing::coefficients()` **trims trailing zeros**, so flattening must pad back to `d` or every later block shifts | `pcs::projection::{FieldMat, to_coeffs, from_coeffs, sigma_pairing_vec, gamma_stack, sigma_matrix}` |
| **CMNW scheme assembly** (`examples/cmnw.rs`) | ✅ **measured green**: honest proof verifies all seven Fig. 7 equations plus Lemma 5's three gates (`β₁ ≥ r₀κd`, `β_p ≥ β₁r₂nαd`, `β₂ ≥ β₁r₁κd`) on `q = 2³² − 99`, `d = 64`, `α = 32`, `r = (2,2,2)`, `n = 1`, `λ = 8`, `l = 1` — **34 368 bytes**. 13 tamper cases, and the finding that matters: under Fiat–Shamir every message is absorbed before the next challenge, so no tamper isolates a single equation (a false `u` trips all seven). The example therefore asserts the **whole failing set** and additionally that **each of the 10 checks appears in some set** — which is what proves none of them is dead code. Equation (6) *is* isolable, by a prover that cheats on the layer relation (`s₁` swapped, `t` recomputed): its set is exactly `{6}`. The earlier "index ambiguity" that left steps 4–7 out was **my misreading of the figure box**: App. A p. 31 makes `P`/`B` coefficient-level (`B ← Z_q^{l×λ}`, `l = ⌈λ/log q⌉`) and check 4 a **constant-term** equality | `pcs::key` + `pcs::mixed` + `pcs::gadget` + `pcs::projection` + `pcs::packing` |
| **Ring switching: the negacyclic residual** (Hachi 2026/156 §1.3, the step that replaces LaBRADOR recursion) | ✅ `a·b = c + (X^d+1)·ρ` with `c` the ring product and `ρ_j = P_{j+d}` unique (`deg ρ ≤ d − 2`); the relation form re-derives `Σ m·z` and refuses an unrelated `w` instead of emitting a `ρ` that proves nothing. Verified in python3 first (300 random trials: decomposition rebuilds the unreduced product, and the identity survives substituting `X = ζ ∈ F_{q^4}`; `ζ^d + 1 = 0` occurred **0** times, which is why dropping `ρ` must break the claim). That scratch run also caught two real out-of-bounds reads (`p[k+D]` at `k = d−1`, where the product has only `2d−1` coefficients) | `pcs::switching::{schoolbook, negacyclic_residual, relation_residual, evaluate_at_base}` |
| **Two-oracle product sum-check over an extension field** (Hachi §1.3's `Σ P(i)·Q(i) = V`; Maltese Eq. (15) is a sum of these) | ✅ `sumcheck::circuit::Product`, a `Composition<R, 3>` for `A(X)·B(X)` over **any** `MatrixElement` domain — including `ExtField`, which is what makes the claim a *field* statement (Hachi's `Õ(k)`-per-round verifier rests on exactly this). Executed over `F_{q^4}` at `q = 2³²−99`: the honest inner product proves and verifies, Def. 9's output is asserted to be the **circuit** value `Ã(ρ)·B̃(ρ)` (not a table extension), a third oracle is refused as `WrongLength{3,2}` rather than silently paired, and a false claim is refused by the prover. `multilinear_at` is the fold the protocol itself uses, pinned against an independent `Σᵢ U(i)·êq(i,r)` expansion at a general point **and** at all `2^µ` vertices, and it refuses a table that does not span the point | `sumcheck::circuit::{Product, multilinear_at}` |
| **Hachi scheme assembly** (`examples/hachi.rs`) | ✅ **measured green, and §1.3's step is now *proved*** (2026-09-25): lift `Σⱼ mⱼzⱼ = w` to `Z_q[X]`, commit the `Z_q`-coefficient vectors of `(z, ρ)` with a coefficient-level Ajtai matrix, substitute `ζ ∈ F_{q^4}` from the transcript, then run the **degree-2 sum-check over `F_{q^k}`** for `Σ_{i∈{0,1}^µ} P(i)·Q(i) = V` (p. 7) — `P` the committed table, `Q` the public weights `ζ` produces (`m̂ⱼ(ζ)·ζᵃ` on each `z_{j,a}`, `−(ζᵈ+1)·ζᵇ` on each `ρ_b`, `V = ŵ(ζ)`), `µ = 6`, 3 extension elements per round — and tie its output back to `P̃(ρ)·Q̃(ρ)`. On `q = 2³²−99 (≡5 mod 8, no NTT)`, `d = 8`, `k = 4`, `Z^4 = 2`, `T = 6`. **Six rejections, each attributed**: `ρ := 0` **re-committed so the opening still holds** fails only the substitution; a false claim is refused before any `ρ` exists; a `‖z‖∞ = 9` witness passes the opening and trips only the norm gate; a stale commitment fails first; a round message moved by one extension element trips `SumcheckRejected`; and a prover that proves the **same sum over a rotated cube** — `Σᵤpᵤqᵤ` is invariant under a bijection of the indices, so every round verifies — is caught only by the tie-back, `PointClaim`. **What remains open**: the recursion that would make the output claim succinct (p. 7's "we can recursively repeat this process"; here `P̃(ρ)` is discharged by opening the vector), and Lemma 1/Theorem 1's trace-map bridge `R_q^H ≅ F_{q^k}` | `pcs::switching` + `pcs::projection::FieldMat` + `algebra::ring::extension::ExtField` + `sumcheck::circuit::{Product, multilinear_at}` + `shortness::exact_l2` |
| **Grand Danois scheme assembly** (`examples/grand_danois.rs`) | ✅ **measured green 2026-09-24**: honest proof verifies at **149 892 bytes** (constraint matrix 17×4672 ring elements), two norm-gate tampers each attributed (`gate-wtz` on `(ŵ,t̂,ẑ)`, `gate-p` on `‖p‖² ≤ 337²ω²`), and the example asserts **all 13 named checks are tripped by at least one** tamper. `pcs::rotation` 16/16 — including an **operation-counting** ring that proves the fast fold is `O(d)` and the expansion `O(d²)` *and* that the two routes agree — `pcs::jl_compose` 14/14. **Three defects found in the paper itself**: §3.2.2 p.20 prints `J′((J′e′)⊗e″)` where p.9's `J` is the identity that typechecks; eq.(14) row 4 `(c⊤G_{L1})` is not type-correct (`r ≠ L1`; the real equation is `Ĵz = c⊤p`, giving **m** rows); Lemma 3.2's proof adds tails as `2^{-a}+2^{-b} = 2^{-(a+b)}` where it must be `≤`. Two further gaps are ours to fill, not the paper's: `L1 = mȷ²` is forced by the `256r×256r²` composed map but never stated, and Def. 2.2 p.12's `A₀⊗…` yields `n^µ×2^µ`, contradicting Table 1's `n×2^µ` — only the entrywise reading typechecks. **Not done**: no recursion (the PoK of `z′` is left as the paper's alternative protocol), and `k = 1` because `ExtField` is not a `Ring`, so §3.2.2's `k×k` treatment of `a⊤` is unexercised. Sizes are **not** comparable to the paper's 80–90 KB estimate. **Corrected 2026-09-25**: this row used to add "the sumcheck closes in transparent-table mode rather than the paper's degree-2 form" — eq. (19) now runs through `sumcheck::circuit` as `(U + γV)·W` with the three oracles kept separate, so the verifier closes on `(ũ(r)+γṽ(r))·w̃(r)`; 13 named checks, all tripped, exit 0, honest proof **149 956 bytes** (the +64 B over the previous 149 892 is the third coefficient of each of the 16 round messages). | `pcs::rotation` + `pcs::jl_compose` + `pcs::projection::FieldMat` + `sumcheck::circuit::WeightedProduct` |
| Multi-assertion batched sumcheck (Π_batch) | ✅ | `sumcheck::batch` |
| Pairwise commitment folding base step + JL shortness certificate | ✅ base step only | `shortness::fold` |
| LaBRADOR recursion compressing O(√N) → polylog proof size | ✅ **the step landed 2026-09-25**, read off §5.3 + Fig. 3's caption + Def. 3.5/Lem. 3.7 (pp.7–8, 14–15) rather than reconstructed; the withdrawn non-unit-challenge route was in fact not what the paper does — §2 p.6 requires only **`c₁ − c₂` invertible for distinct challenges** (Appendix B p.32 divides by `c̄ᵢ = cᵢ − c′ᵢ`, never by `cᵢ`), `‖c‖₂² ≤ τ`, `‖c‖_op ≤ T`. What landed: `derive_view` (the verifier's recomputation of `Π, ψ, ω, a″, φ″, α, β, cᵢ`), `TargetShape` (§5.3's `n′ = max{⌈n/ν⌉, ⌈m/μ⌉}`, `r′ = 2ν+μ`, `m = rt₁κ+(t₁+t₂)(r²+r)/2`), `target_instance` (all `κ+κ₁+κ₂+3` equations of (6), `F′ = ∅`, budget (5)) and `SizeModel`/`RecursionPlan` (§5.7's two formulas, integer ceilings only). Executed, not just built: `tests::two_levels_compose_into_a_smaller_relation` runs `prove_core` on a level-0 target relation and verifies it. **The compaction is shape-bound and does not hold at this crate's toy instance**: a level's target witness is `2n+m` ring elements while its source is `rn`, and `m` does not shrink with `n` — measured with `κ=4, t₁=t₂=4, q=2³²−99, d=64, r=8`, one level *costs* 5240 B at `n=3` (this example's rank), breaks even at `n=64` (`k=4096` constraints) and saves 9360 B at `n=128`; the paper's own level 1 is `r=112, n=37450` (Table 3, p.28). What is still not landed: driving ≥ 2 levels from an example at a compacting shape (the debug-time cost of a `256·r′·n′`-coefficient projection at `n′ ≥ 64` is minutes), §5.6's last-level variant without outer commitments, and growing `κ, κ₁, κ₂` per level as §6.1 does for 128-bit security (Remark 5.2's `√(128/30)` per level is reported by `recursion_msis_norm_sq`, not absorbed) | `pcs::dotproduct::{derive_view, CoreView, TargetShape, target_instance, TargetInstance, TargetEquation, SizeModel, LevelSize, RecursionPlan, recursion_msis_norm_sq, split_z}`, `examples/labrador.rs` |
| Ajtai hash **tree** with preimage sampling (**SLAP only** — 2026-09-24 correction: FMN/2023/846 is the *flat* PowerBASIS commitment of its Fig. 4, one `SamplePre` under a `(d+1)`-block matrix, no tree; the tree is SLAP's own addition on top of `[FMN23]`) | ✅ **G2 landed** (was "the crate has no TrapGen/SamplePre at all" — that is now false): `pcs::trapdoor` gives Micciancio–Peikert `GenTrap` (`A = [Ā | G − ĀR]`, `B = [R; I]`, `A·B = G`, MP12 §5.2 Alg. 1 / Def. 5.2, ±1-coin `R` from MP12's statistical instantiation) and `SamplePre` as MP12 Alg. 3's algebraic skeleton `x = p + B·G⁻¹(u − A·p)` with the Gaussian oracles replaced by exact substitutes, plus SLAP Appendix C's deterministic `p = 0` form quoted verbatim in the module docs. `pcs::prisis` assembles the shared-preimage basis `B = [[A,0,−G],[0,wA,−G]]` and asserts `B·R̃ = G_{n(d+1)}`; 13 + 10 tests green. Fixed here: the per-slot trapdoor blocks were `G⁻¹` of the *narrow* `W⁻ⁱG`, so `R̃` came back `t` columns wide and could not stack against the closing zero block. Corrected earlier: Maltese was listed in error — 0 TrapGen/SamplePre occurrences in its 90 pp. **The SLAP tree assembly in `examples/` has since landed and passes** (measured 2026-09-24, in the 14/14 batch: `slap` exits 0 and its tamper battery attributes `["eval(claim 0)", "root(claim 0, leaf 2)"]`; `pcs::slap_tree`'s 10 red tests were adjudicated the same day, all test-side). **Correction to what this row said two minutes ago:** it is *not* true that FMN needs an absent capability — `pcs::prisis` already builds FMN's general `(d+1)`-block basis with `W` as a [`UnitMatrix`](pcs::trapdoor) (`Rᵢ := R·G⁻¹(W⁻ⁱG)`, block row `i` = `[0 … WⁱA … 0 | −G]`, `B·R̃ = G_{n(d+1)}`), and its module doc already observes that SLAP's `w_j` **is** FMN's `W = w·I_n`, so the two schemes are one object here. The genuine residual, and it is documented in-code rather than by me: `W` is a *certified unit pair* (a diagonal of scalar units), not a uniform `GL(n, R_q)` draw, **"because the crate has no solver over `R_q`"** — so the missing capability was an `R_q`-matrix invertibility solver / `GL(n,R_q)` sampler. **Landed 2026-09-24 as `algebra::ring::matrix_unit`** (5 tests, `lattice-algebra` + `lattice-pqc` gate **663/0**): `multiplication_matrix`/`expand` give the ring embedding `R_q → Z_q^{d×d}`, so invertibility of `A ∈ R_q^{n×n}` is decided by field Gauss–Jordan on `E(A)`; `invert_matrix` reads `A⁻¹` back out of `E(A)⁻¹`'s block column 0 and **verifies by multiplying back in `R_q` and re-expanding**, so `None` means "not a unit", never "the extraction looked wrong"; `powers_pair` returns both `Wⁱ` and `W⁻ⁱ` (FMN's `Rᵢ = R·G⁻¹(W⁻ⁱG)` and `WⁱA`), and `sample_gl` reports its rejection count because the unit density of `R_q^{n×n}` is below 1. Two things this settled: a test of mine first reached for `1 + X` as a zero divisor and it is **not** one (`X^d+1` at `X = −1` is `2`, so `X+1` divides nothing for odd `q`) — replaced by a `det = 0` matrix, which refutes invertibility over any commutative ring; and `prisis` can now draw a genuine `W ← GL(n, R_q)` instead of a diagonal of scalar units | `pcs::trapdoor` + `pcs::prisis` + `algebra::ring::matrix_unit` |
| Nested-gadget tree with tensor keys `(I_{2^i} ⊗ A)` and sumcheck norm-growth control (Maltese) | ✅ the tree side is now `pcs::tree_commit` (Def. 19 `TCom`: `Setup`/`Commit`/`Open`/`Open_F`, no trapdoor, **no authentication path**), `pcs::tree_eval` (Π^PE_NC Protocol 3, Π^Dec Protocol 5, Lemma 14's field↔ring packing, `EqTables` for shared `êq` tables) and `pcs::tree_fold` (Π^Fold Protocol 4, Eq. (11)–(19), `CycleShape`), with `pcs::nested` still covering the hashing relation. Still absent: the partially-split CRT isomorphism `R_F ≅ K^{d/e}`, so `K = F` and every reduction's sum-check runs over `F`. **`e = 8` is now known to be unreachable at this instance, not merely unwritten** (measured; pinned by `algebra`'s `number_theory::the_eight_degree_regime_needs_a_prime_outside_the_house_class`): `X⁶⁴ + 1 = Φ₁₂₈` splits into `64/ord₁₂₈(q)` factors of degree `ord₁₂₈(q)`, every prime `≡ 3 or 5 (mod 8)` has `ord₁₂₈ = 32`, so the house prime `2³² − 99 ≡ 29 (mod 128)` gives **`e = 32`** while P3 states `e = 8`. A 32-bit prime with `e = 8` does exist (`find_prime_for_splitting(64, 8, 32)` → one `≡ 7 (mod 8)`, 2-adicity 1), but `ExtField`'s `Z⁸ − A` model then fails — a binomial is irreducible only when `q ≡ 1 (mod 4)`, swept for every `2 ≤ A < 400` — and the `q ≡ 1 (mod 8)` alternative has 2-adicity 4. So Protocols 1–2 need a *general* degree-8 modulus, not just an instance | `pcs::{tree_commit,tree_eval,tree_fold,nested}` + gap G9 |
| **Maltese scheme assembly** (`examples/maltese.rs`) | ✅ **cycle + §5.4 `Π^Fin` assembled, not yet succinct** (2026-09-25, measured; the tally and the `Π^Fin` detail are in §5's note below, one place): P3's shape parameters (`log q = 32`, `d = 64`, `b = 2`, `α = 32`, `k = 7`, `C_sp(32,8)`) with `n`, `ℓ` shrunk; the honest cycle *and* the finisher verify, every named check is tripped by some tamper, and no check is left untested. **Three findings that a port must not re-lose**: (1) Eq. (12) does **not** bind `v_top` here — Π^Fold's `TE` point is the PE→TE bridge `(1 ‖ u_PE)`, so the factor `êq(0^{ℓ−k}, u_{(:ℓ−k)})` reads coordinate 1 and vanishes; measured, forging `v_top` tripped *none* of Protocol 4's checks. §5.4's `Π^Fin` is what binds it in the paper's way (`fin.eval_te`, Eq. (35), through Def. 23's fresh recommitment), and `forward.top_tree_claim` survives as §2.2 p. 9's **non-succinct** direct-open cross-check, not the only binding. (2) Π^Dec never bound `t*_dec` to the planes it shows: swapping in **another well-formed tree of the same shape** satisfied every equation Protocol 5 prints (found by attack 2026-09-24); `tree_eval::decomposed_leaves` is now the single `s_dec` constructor both sides use and `EvalError::DecomposedCommitmentMismatch` names the check. (3) `b = 2` forces the shape: the cycle shrinks only while `k > log h + 1`, and `B = 2^k·T·b = 12 288` ⇒ `⌈log₂ B⌉ = 14` ⇒ `k ≥ 7` ⇒ `ℓ = 8`, so each verifier pass touches a `2^{15}`-entry `êq` table `2^k = 128` times — one cycle assembles in 10.0 s release vs 84.3 s debug, hence `--release` for this example alone. The two-name `FoldError::Tree` residual this row used to record is **fixed**: step 7 has its own `FoldError::SubtreeCommitInvalid`, audited as `fold.subs_tree_opens` separately from `fold.input_tree_opens`. Evidence: `open-milestones.md` §"Maltese：Eq. (12) 在这个 shape 下不约束 `v_top`" and §"#15 收口" | `pcs::{tree_commit,tree_eval,tree_fold,tree_fin}` + `sumcheck::circuit` |
| Extension **field** `F_{q^k}` with a real inverse, NTT-free (Hachi) | ✅ `F_q[Z]/(Z^k − A)`, `k = 4`, `A = 2`, `q = 2³² − 99` verified a field (every nonzero of a 255-element sweep invertible); a *reducible* `(q,k,A)` is detected as a zero divisor rather than silently misbehaving. **`k = 8` now exists too**, at the prime Maltese's P3 regime actually requires: `ExtField<Zq<2³² − 527>, 8, 3>` with `q ≡ 113 (mod 128)`, whose `X⁶⁴ + 1` splits into eight degree-8 factors — 6560 elements swept invertible (`an_eight_degree_extension_exists_at_a_prime_in_p3s_regime`). What that prime's 2-adicity (4) still does not buy is the CRT reading `R_F ≅ K^{d/e}`, and the `q ≡ 7 (mod 8)` 2-adicity-1 alternative has **no** binomial modulus at all (`Z⁸ − A` irreducible only when `q ≡ 1 mod 4`), so a general modulus remains the blocker | `algebra::ring::extension::ExtField` (also a `MatrixElement`, so `sumcheck` runs over it) |
| Per-scheme ring dimensions and moduli (Akita's `(d_A, d_car, d_B, d_D)`, LaBRADOR's `d=64`, SLAP's `log₂q≈276`) | ⚠️ **partly landed**: gadget **and** commitment keys are now generic over `(scalar ring, ring degree, digits/base)`, including non-NTT-friendly `q`; what still binds the crate constants is the protocol layer (`greyhound`, `batched`, `nested`, `mixed`) | `pcs::gadget::{split, join}` + `pcs::key::RingMatrixKey` |
| Nested-gadget Ajtai hash chain `h_i(x) = A_i · G⁻¹(x)` (CMNW's commitment; SLAP's node hashing minus the trapdoor) | ✅ multi-level, transparent, no trapdoor and no error-correcting code required; levels are domain-separated so equal widths do not collapse, and every preimage is binary by construction | `pcs::nested::NestedGadget` |
| Centered **base-b** gadget split (LaBRADOR `t₁/t₂`, Akita digit planes, CMNW's `δ = q^{1/α}`, Serval's second base `σ_α`) | ✅ one implementation (`gadget::digit_planes`) behind both the const-generic `split::<R,D,BASE,DIGITS>` and LaBRADOR's runtime-base `Decomposition`, so the two cannot drift. **Corrected 2026-09-24:** the exactness guard was `BASE^DIGITS > q`, which is the *unsigned* criterion — a balanced digit set spans only `±⌊B/2⌋(B^t−1)/(B−1)`, so `base 16, 8 planes, q = 2³²−99` passed the old guard (16⁸ = 2³² > q) yet left residual `1` on a value near `q`, recomposing to `value − 2³²`, wrong by 99 in `Z_q`. The guard is now the span, and a balanced base expands the **least-absolute** representative (which is what lets `t₂` be sized by `‖g⃗‖` rather than by `log q`, §5.4) while `BASE = 2` keeps the canonical one | `pcs::gadget::{digit_span, digit_planes, split}`, `pcs::dotproduct::Decomposition` |
| LaBRADOR's **principal relation + core argument** (§5.1 `R`, §5.2 Figures 2–3, §5.4 norm bounds, §5.7 size) | ✅ green 2026-09-24: 24 lib tests + the `examples/labrador.rs` assembly runs end to end on `q = 2³²−99, d = 64` (the paper's two-factor, NTT-free regime), honest proof verifies, 15 tamper cases each named. Three real defects fixed on the way: γ₁²/γ₂² divided the second term by 24 where §5.4 says `/12` for both; the projection-plane count used a capacity rather than a span; and the verifier's single rejection could not distinguish "checked and failed" from "never reached", so `verify_core_report` now returns the whole set | `pcs::dotproduct`, `pcs::binary_r1cs`, `examples/labrador.rs` |
| Operator-norm-rejected challenges (LaBRADOR `‖c‖_op ≤ 15`, Akita `Γ`) | ⚠️ **partly landed (G5)**: the space itself is exact — §2's shape (23 zeros, 31 `±1`, 10 `±2`, `τ = 71`) sampled by the unbiased fixed-weight recipe, with the filter in rigorous **integer** arithmetic as `⌈√‖g‖₁⌉` where `g = c·σ(c)`. But that bound is loose: measuring the true `σ_max` of the 64×64 negacyclic matrix over this shape gives median 16.9 and `P(≤15) = 0.15–0.17` — the paper's own "roughly one in six" — while the certified bound has median 23 and minimum 20, so **15 would reject every draw**. `ChallengeSpace::PAPER` therefore filters at 24, and 24 (not 15) is what the Module-SIS budgets must be read with. Matching 15 needs a certified eigensolver for `T²I − M_cM_cᵗ ⪰ 0`, which no row-sum/Gershgorin-family bound can do here (they converge to `ρ(|M_g|) ≈ 290 > 225`) | `pcs::dotproduct::{ChallengeSpace, operator_norm_bound}` |
| Evaluation hiding / ZK openings (Jindo) | ✅ **closed 2026-09-25** (was: Fig. 7's two response gates not implementable on the proof object). The capability landed in `pcs::mle`: `MleLevels` (Fig. 3 `Com*` steps 3–4's two compressed levels — `t̂ₖ = ⌊tₖ/B_t⌉`, `û = ⌊(D t̂)/B_u⌉`), `MleQuadProof` (Fig. 7's *sent* response `t̂`, `f̂* := F̂*c`, `r := Rc`; lines 5–6's `h`, `s` stay verifier-side, as printed), `MleLevels::quad_report` returning the **whole** failing set of `QuadCheck::{InnerNorm, OuterNorm}`, and `QuadParams` deriving `B`, `B_o` through Theorem 3 → 5 → 6 from the instance. `examples/jindo.rs` now sends those messages and asserts both lines, each **failing alone** (measured: `long inner response f̂* → {L7}`, `stack shifted by q → {L8}`), with the honest transcript at `|f*|+|r|+|h| = 18811 ≤ B = 698424` and `|s|+|t̂| = 5309 ≤ B_o = 100863`. **Two transcription corrections, both against the PDF's glyph geometry and the paper's own arithmetic**: (a) lines 7–8 gate a **sum of ℓ2 norms**, not of squares — the `2` after `‖f̂*‖`, `‖h‖`, `‖t̂‖` is the norm subscript (it sits at the subscript baseline; B.6 p. 18, B.8 p. 19 and B.9 p. 20 all *add roots* to reach `B = b√((m₁+1)d) + B_χ√((μ+ν)d) + B_t√(μd)`), so the gates of the earlier audit note and of this row are mis-written; (b) Theorem 5's `σ = 14/(ln M)·m₀√n₀·B_C·B` is a **product** (Lemma 2 p. 6: `σ ≈ 14T/ln M`), i.e. a larger `B` needs a *larger* σ — which the toy fails (required 2753520 vs sampled 336, now printed rather than hidden). Residual, documented in the example header: `B = [B′|I_μ]`'s identity block is absent here (Thm. 2's MLWE hiding still not delivered), the value-mask row is exempt from `L7` for the same `p = q` reason `NORM` exempts it, and `NORM`'s tamper now trips `{NORM, L7}` together because both read the sub-polynomial rows. Evidence: `open-milestones.md` §"Jindo 的 Fig. 7 L7/L8" and its follow-up section | `pcs::masking`, `pcs::mle` |
| Ring lookup arguments | ⏳ research branch, entry [2026/471](https://eprint.iacr.org/2026/471) | survey ⏳ item 23 |

## 5. Verification notes

- Every eprint link in §1 was fetched from eprint.iacr.org on 2026-09-22;
  titles/authors/status read from the page itself, not from citations. Three
  rows' venue status was re-fetched and settled on **2026-09-24** (SLAP, CMNW,
  Rinocchio — see the notes added to those rows).
- Performance figures are the papers' own, under their parameter choices and
  hardware; no cross-paper comparison in this document is an apples-to-apples
  measurement (same policy as `docs/research/02-peer-research.md` §9).
- **Resolved 2026-09-24** (were UNVERIFIED): the venue question for CMNW, SLAP and
  Rinocchio has a single answer — **none of the three eprint pages states a venue**.
  SLAP's citation is literally "Preprint.", Rinocchio's is "Preprint.
  2021-03-11: received", CMNW's is the bare archive line. So the CCS 2022 (Rinocchio)
  and any conference attribution for CMNW/SLAP are second-hand citations, not
  page-supported facts, and §1 now says so per row.
  **Still open**: Serval's and Jindo's implementation claims; the `babykoala` ring
  parameters behind ICICLE's LaBRADOR port. Everything else in §1 was read off a
  primary source.
- **Akita §6.2 is now on all three routes (2026-09-25, read off the cached PDF, not
  from memory).** The §4 row above said "still not here: p. 64's coefficient route …
  and Eqs. (126)–(128)"; that is no longer true, and what landed is worth the
  distinction the paper itself draws:
  * The **coefficient route** is not a third *proof of Eq. (118)* — it proves no
    energy statement at all. p. 64: "on the coefficient route, the schedule combines
    `Δ_f^cert` (Eq. 113) with the certified challenge-difference bound to derive the
    A-collision radius in (79), which it supplies to the Module-SIS estimator", so
    `pcs::norm_route` gained `NormRoute::Coefficient` plus the derivation itself
    (`delta_cert` = Eq. 113, `a_collision_radius`/`CollisionRadius::from_coefficient`
    = Eq. 79's `η_{A,g} = 2κ̄_{1,g}Δ_f^cert`, `certified_challenge_difference` =
    p. 108's `κ̄_{1,j} ≤ 2ω_j`), and the estimator interface that consumes it
    (`MsisInstance` = Theorem 10.33's `(n_I, m_I, d_I, q)`, `MsisEstimator`,
    `CoreSvpEstimator` over `algebra::security`, `SecurityContract`,
    `DeclaredRadius`). Corollary 10.26's Euclidean price `η²_{A,2} = 64Γ²S_max` is
    the sibling constructor, and `tighter` is the choice between them.
    `shortness::exact_l2::Route` deliberately did **not** gain a variant: that enum
    answers "which of the two proofs of Eq. (118) decided this claim", and the
    coefficient route sends no such claim, so a third arm there would be a lie about
    a gate that never ran.
  * **Measured consequence, and the reason §3.2's sparse signed challenge family is
    load-bearing rather than an optimization**: pricing the example's own
    `δ_f = 11` schedule under a *full-ring* family (`κ_1 = d_A(q−1)/2`, `Γ ≤ κ_1` by
    Lemma 3.1) makes `64Γ²S_max` leave the `u128` window entirely, so that schedule
    admits **only** the coefficient route while Eq. (79) still derives a finite
    radius. Any "the Euclidean route is tighter" claim is therefore conditional on
    the certified operator bound, exactly as p. 108's "the planner may select this
    Euclidean radius only when the schedule certifies the accepted challenge family
    and its operator bound" says.
  * **Eqs. (126)–(128) are a named check, not a comment.** `DigitMap` is `π` with
    Lemma 6.3's premise enforced (injective + inside a span of `N_Aδ_f` cells, which
    together *are* "image = the scheduled `ẑ` digit cells"); `pi_binding` forms both
    printed sides, with Eq. (126)'s `η_norm b^h` and Eq. (127)'s `η_norm^{h+1}` kept
    visibly distinct (the expanded route binds the planes raw, because `b^h` already
    entered through Eq. 123); `check_pi_identity` is the equation; and
    `sumcheck::fused::{Summand, fuse}` is Eq. (128)'s additive fusion, which is the
    only reason `P_base` and `P_bind` can share one sum-check "with no new
    sum-check rounds". In `examples/akita.rs` this is check **C11**, which a
    transposition of two `π` addresses trips **alone**: the permuted map is still a
    bijection onto the scheduled span, so no premise fails, and nothing else in the
    level reads `π` — which is exactly what it means for the binding to be the check
    rather than the layout being an assumption.
- Greyhound-adjacent implementation landscape (lattirust, Lazarus, condor-rs,
  lattice-dogs/labrador, ICICLE) is documented in
  `docs/research/02-peer-research.md`; note its finding that **Lazarus's
  `pcs` crate is an empty placeholder** — the real Rust reference for the
  Greyhound PCS is Lazarus's `greyhound` crate (a port of `greyhound.c`).
- **Maltese §5.4 `Π^Fin` is wired, and `GH′` now sends Eq. (38)'s message
  (2026-09-25, measured)** — the comparison table's "`Π^Fin` (not implemented)" is
  superseded, and the assembly's tally is **54 tampers tripping all 57 named checks**
  (`cargo run -q --release -p lattice-zk --example maltese`, exit 0, 594.17 s on the
  committed tree; `scripts/integration_gate.sh` for the same tree: 14/14 examples,
  `--lib` 660/0, workspace 1345/0 across 19 binaries, four feature lanes OK).
  `examples/maltese.rs` hands the cycle's set-aside
  `TE(1,k,b)^ω × PE(1,k,b)^{ω+1}` to a finisher (`zk::pcs::tree_fin`): Eq. (35) binds
  `v_top` *through Def. 23's fresh two-layer recommitment* — the paper's route — and
  forging that value trips `fin.eval_te` alone; Eq. (36) binds the `PE` side-claims at
  `(1 ‖ u_PE)`; `GH′`'s `q⊺s1 = y1` binds the layer-1 claim.
  **What landed since that first wiring**: `GH′`'s own prover message `ŵ, v, z` and
  Eq. (38)'s five rows (`pcs::tree_fin::{gh_prime_prove, gh_prime_report,
  folded_norm_bound}`), read off p. 45 as a rendered page image — row 1 `D·ŵ = v`
  needs a third seed-expanded matrix (`Def. 23`'s `GHSetup` prints only `B1, B2`
  because it restates the commitment scheme; `D` is the `ŵ`-commitment of the
  three-move protocol `GH′` modifies), rows 3–4 open `G_{b1,2^γ}·ŵ`, and row 5 is the
  `+η·ẽ₁·q⊺` entry, which is §5.4.3's *whole* modification: the lib test
  `the_eta_entry_is_what_carries_eq_37_into_eq_38` runs one forgery twice and gets
  `[QFormMismatch]` at `η = 0` versus `[QFormMismatch, GhEq38LastRowMismatch{row:0}]`
  with `η ≠ 0`. Plus `FinishAccounting`, which computes Fig. 6's finish row
  component by component at P3 (`µ′+m = 22` rounds, `20 544 B` landed, `51 KB` left
  for `Greyhound(2^{µ+k+1}nαd = 268 435 456` field elements) — and confirms the
  paper's own arithmetic `43.8·6 + 72 = 334.8 ≈ 335`).
  `forward.top_tree_claim` survives as §2.2 p. 9's direct-open branch, now explicitly a
  **cross-check** of the finisher rather than the only binding. What still is *not*
  succinct: the Greyhound three-move core (Eq. (38) is *verified*, not proved) and
  LaBRADOR, plus §4's `BatchSC`/`ShiftSC` — so `s_reshape` is opened and read.
  `Π^PE_NC,fin`'s Step 1 `Q_N` zero-check deliberately does **not** run as a round
  here: its conclusion is Def. 23's two norm bounds, which `gh_open_report` already
  gates by name on the opened witness, so a round would add messages without adding a
  check (stated in the module doc, and it is the one Fig. 6 component — `SC(2b)` —
  this compilation does not send). Evidence and the two claims this superseded:
  [`open-milestones.md`](open-milestones.md) §"#15 收口".

## 6. References

All eprint links inline in §1. Folding-line and Σ-protocol references live in
[`survey-lattice-zksnarks.md`](survey-lattice-zksnarks.md) §5.
