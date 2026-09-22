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
2026 wave — **Hachi** (extension-ring residuals), **Maltese**
(Ajtai-Merkle + folding, ASIACRYPT 2026), **Akita** (split-and-fold with exact
Euclidean norm checks, active Rust implementation), **Grand Danois** (vSIS +
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
| **SLAP** | Albrecht–Fenzi–Lapiha–Nguyen, EUROCRYPT 2024, [2023/1469](https://eprint.iacr.org/2023/1469) | ring-SIS | Ajtai hash **tree** (vector Merkle), split-and-fold | univariate | transparent | polylog verifier, extractable | none public |
| **Fenzi–Moghaddas–Nguyen** (SLAP follow-up) | Journal of Cryptology 2025, [2023/846](https://eprint.iacr.org/2023/846) | ring-BASIS + statistical NTRU | tree-based | univariate | no preprocessing | 17 MB SNARK proof @ 2²⁰ R1CS | none |
| **Rinocchio** | Ganesh–Nitulescu–Soria-Vazquez, CCS 2022, [2021/322](https://eprint.iacr.org/2021/322) | ring-SIS variants | extractable ring-encoding commitments | QRP (QAP over rings) | structured | designated verifier | none |
| **CMNW** | Cini–Malavolta–Nguyen–Wee, [2024/281](https://eprint.iacr.org/2024/281) (venue not stated on the page — UNVERIFIED) | Module-SIS, ROM | Ajtai/tree, no preprocessing | univariate | transparent | 2× smaller than FRI, 70× smaller than SLAP-line @ L = 2²⁰ | none |
| **CELPC** | Hwang–Seo–Song, CRYPTO 2024, [2024/306](https://eprint.iacr.org/2024/306) | standard lattice | homomorphic-friendly lattice commitments | univariate | transparent | √-size proofs; 4.1× smaller than SLAP | none |
| **Orbweaver** | Fisch–Liu–Vesely, CRYPTO 2023 (rev. 2024-12), [2024/2026](https://eprint.iacr.org/2024/2026) | **k-R-ISIS** (knowledge) | structured-SRS linear-functional commitments | univariate **and** multilinear | **trusted universal SRS** | 302 KiB–1.6 MiB @ 2³⁰; polylog verifier | none |
| **Serval** | Zhang–Chow–Gao–Xiao, [2025/1903](https://eprint.iacr.org/2025/1903) (rev. 2026-03) | SIS/LWE-type | **slack-free ℓ2**: self-inner-product + binary validation in one divide-and-conquer | (argument system) | n/s on page | 8× smaller than FMN, 85× smaller than SLAP @ L = 2²⁰ | claimed, no public repo verified |
| **Hachi** | Nguyen–O'Rourke–Zhang, [2026/156](https://eprint.iacr.org/2026/156) | Module-SIS | Ajtai + **residual technique over extension rings** F_q^k[X] | multilinear | transparent | verifier Õ(√(2^ℓ·λ)) | [LatticeProofs/Hachi](https://github.com/LatticeProofs/Hachi) (Rust, fixed params, AVX-512) |
| **Maltese** | Cheng–Nguyen–Tyagi, **ASIACRYPT 2026**, [2026/2067](https://eprint.iacr.org/2026/2067) | Module-SIS | Merkle tree over Ajtai hash **+ folding** with sumcheck norm-growth control | multilinear | n/s on page | 335 KB @ N = 2³⁰; ~300× smaller than prior polylog-verifier lattice PCS | none found |
| **Akita** | Dao et al., [2026/1983](https://eprint.iacr.org/2026/1983) (rev. 2026-09-18) | Module-SIS with **exact Euclidean norm checks** | split-and-fold ("root-to-tail"); 128-byte commitments; setup offloading | multilinear | transparent | 61–72 KB proofs (Greyhound-parity size); verifier 19.2–89.7× faster than Greyhound | [LayerZero-Labs/akita](https://github.com/LayerZero-Labs/akita) (Rust, active; `akita-transcript`/`-sumcheck`/`-algebra`/`-planner` crates) |
| **Grand Danois** | Kallesoe–Khoshakhlagh, [2026/1196](https://eprint.iacr.org/2026/1196) (rev. 2026-08) | **vSIS** (vanishing SIS) | vSIS parameters + JL projections + rotation matrices | multilinear | structured public params | ~80 KB @ 2³²; O(λℓ) verifier | none |
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

- **Hachi**: the *residual technique over an extension ring* — a multilinear
  opening whose verifier work scales with √(2^ℓ·λ) without new assumptions.
  Directly relevant to a ring whose base is `F_q[X]/(X^d+1)` with an
  extension `F_q^k`; the same lead author as Greyhound, so the structure maps
  cleanly onto our `pcs` domain. Its degree-18 balanced-norm gate polynomial
  `c_bal = (w²+8w)·∏_{k=1..7}(w²−k²)` composed with the sumcheck is the
  vanishing-polynomial norm check (survey ⏳ item 20) in the wild.
- **Akita**: (a) *exact Euclidean norm checks inside parameter selection* —
  the slack-free tightening of our ℓ∞ gates; (b) *setup offloading* (verifier
  work on public matrices deferred and proved against commitments); (c)
  *batched openings of independent polynomials* — the primitive
  `pcs::batched` implements the core-shape version of; (d) a *planner* crate
  (automated parameter/schedule DP) — an engineering idea worth copying.
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

| Landscape primitive | Status here | Where |
| --- | --- | --- |
| Greyhound two-layer Ajtai commitment + √N split evaluation (five link equations + norm gates) | ✅ core-size proof (LaBRADOR compression deferred) | `pcs::greyhound` |
| Batched opening at a shared point (LaBRADOR amortized opening in PCS form; HyperBall weights, single combined `z`) | ✅ core-size batched proof | `pcs::batched` |
| Shared samplers: HyperBall challenge vectors, ternary challenges | ✅ | `foundation::sampling` |
| Batched opening at *different* points (sumcheck line) | ⏳ needs the batched univariate sumcheck | `sumcheck` domain |
| LaBRADOR recursion compressing O(√N) → polylog proof size | ⏳ explicit milestone | `opening` + `pcs` |
| Exact-ℓ2 (slack-free) norm gates | ⏳ trend; today's gates are ℓ∞ with slack | `pcs`/`shortness` |
| Vanishing-polynomial range/norm gate inside sumcheck (Hachi `c_bal`, LatticeFold Π_batch) | ⏳ next step for `sumcheck` | survey ⏳ item 20 |
| Evaluation hiding / ZK openings (Jindo) | ⏳ | `pcs` |
| Ring lookup arguments | ⏳ research branch, entry [2026/471](https://eprint.iacr.org/2026/471) | survey ⏳ item 23 |

## 5. Verification notes

- Every eprint link in §1 was fetched from eprint.iacr.org on 2026-09-22;
  titles/authors/status read from the page itself, not from citations.
- Performance figures are the papers' own, under their parameter choices and
  hardware; no cross-paper comparison in this document is an apples-to-apples
  measurement (same policy as `docs/research/02-peer-research.md` §9).
- UNVERIFIED items: CMNW's conference venue; Serval's and Jindo's
  implementation claims; the `babykoala` ring parameters behind
  ICICLE's LaBRADOR port. Everything else above was checkable from a
  primary source.
- Greyhound-adjacent implementation landscape (lattirust, Lazarus, condor-rs,
  lattice-dogs/labrador, ICICLE) is documented in
  `docs/research/02-peer-research.md`; note its finding that **Lazarus's
  `pcs` crate is an empty placeholder** — the real Rust reference for the
  Greyhound PCS is Lazarus's `greyhound` crate (a port of `greyhound.c`).

## 6. References

All eprint links inline in §1. Folding-line and Σ-protocol references live in
[`survey-lattice-zksnarks.md`](survey-lattice-zksnarks.md) §5.
