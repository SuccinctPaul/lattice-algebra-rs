# Research document index: `lattice-algebra` as the algebra base service

**Research question**: we want `crates/algebra` to become the algebra base service for our organisation — what is still missing?
**Research date**: 2026-09-19 | **Branch**: `feat/pqc` | **Repository under study**: `lattice-algebra-rs` (three crates: `algebra` / `pqc` / `zk`)
**Method**: ① in-repo evidence (code, CI, docs, git statistics); ② an inventory of the parallel stacks inside the organisation
(verified by a full grep/manifest pass over `/Users/paul/zkp`); ③ peer research (public repositories / crates.io / official docs);
④ every key defect was **reproduced by actually running it**, not inferred from reading code.

| Document | What it answers | Horizontal / vertical |
| --- | --- | --- |
| [01-requirements.md](01-requirements.md) | The definition of a "base service"; real consumers and the evidence of their requirements; the REQ list plus machine-checkable acceptance criteria | requirements side |
| [02-peer-research.md](02-peer-research.md) | What peers have built and how far they took it; a per-dimension horizontal comparison matrix | **horizontal comparison** |
| [03-gap-analysis.md](03-gap-analysis.md) | A six-dimension scorecard; how serviceable each layer within our stack is; the timeline stage model; the P0/P1/P2 gap list | **vertical comparison** |

---

## Executive summary

1. **The kernel is done, the shell is not.** The L0–L4 layering, the capability traits, the const-generic parameterisation and
   the deterministic (XOF-first) design are on a par with arkworks / plonky3; matching 511 official KAT/ACVP vectors byte-exact
   is a strong practice that is rare in this class of project. But of the six parts of the "service shell" — release, version
   contract, `no_std`, API gate, multi-platform measurement, governance — four score 0. **Overall level 0–1 / 4.**

2. **A real consumer was already broken → ✅ fixed on the consumer side (2026-09-19).** `LPN-zk` (2025-01) consumes this
   repository via a path dependency; after the W1 split removed the `lattice-algebra-rs` facade, its `cargo check` failed outright
   (virtual manifest), and the `MatrixScalarType`/`VectorArithmatic` it referenced had no counterpart left.
   **It has now been migrated to the current API (check + test fully green)**, and the migration itself surfaced
   6 integration friction points (3 public capability gaps: matrices have no "construct from data" entry point,
   `hamming_weight` is missing, and `GenericMatrix` lost its `Ord` derive; plus the `rand` version being locked in place by
   `Ring::rand`, and the doubled `matrix::matrix::` path) — see [01 §2.1b](01-requirements.md). The repository is still at
   `version = "0.1.0"`, while its history contains 5 breaking `refactor(...)!` commits, and consumers have no mechanical way
   to detect breakage.

3. **L0 was incorrect within the value range its documentation promised (measured) → ✅ fixed (2026-09-19).** `Zq` declares
   `q ≤ 2⁶⁴`, but the real boundary stopped at `2⁶³`: at `q = u64::MAX-58`, `mod_add` drops the 2⁶⁴ carry, `inverse()` silently
   returns a non-inverse (`12345⁻¹` yields 21, product ≠ 1), and `centered()` has the same class of `i64` cast.
   The fix = carry-folding `mod_add` + an EGCD with `u128` modular Bézout + `u128/i128` centered; the test domain was aligned in
   step (axiom modulus 15→17, a new Goldilocks with `q > 2⁶³`; boundary primes whose `q−1` is not easy to factor are now covered
   by targeted differential tests). `make gate` exits 0, **726 tests pass**.
   *Correction: the first draft claimed that at `q ≈ 2⁶³` `inverse` returned `None` for invertible elements — that modulus is in
   fact composite (digit sum 90), so `None` was correct behaviour; the real boundary is only `q > 2⁶³`. See 01 §2.2.*

4. **The competition is internal, not external.** The same lattice algebra has at least 6 independent implementations under
   `/Users/paul/zkp/lattice_based`; and more importantly **our own upstream projects use an unmaintained parallel stack**:
   `lettuce` (8,129 LOC, carrying its own L0–L4, whose `ntt.rs` TODOs are exactly the capabilities we have already implemented)
   and the collaborator repository `hachi-pcs` (which chose `tfhe-ntt 0.6` + `ark-ff 0.5` over this repository). The rival of a
   base service is "copy another 300 lines" and "a ready-made external stack", not arkworks.

5. **Naming is a hard collision, not a style question.** This repository declares `[lib] name = "algebra"`, and the upstream
   `Lazarus/algebra` crate is also named `algebra` (crates.io `Lazarus 0.1.0`, 2025-05-14) → the two cannot coexist in a single
   dependency graph; `pqc`/`zk` are likewise too generic for the same reason.
   **Yet the three package names `lattice-algebra`/`lattice-pqc`/`lattice-zk` are all currently unclaimed on crates.io**
   → the release window is open.

6. **The external baseline and the window of opportunity (the core judgement of this peer research).** As of 2026-09-19, of
   "① published ② generic over modulus/degree ③ `no_std` ④ capability traits ⑤ serving PQC and ZK at the same time",
   **no one satisfies all five simultaneously**: `module-lattice` (0.2.3, newly created 2026-01-27) satisfies ①③④ but welds the
   ring degree to `U256` and has zero ZK surface, **yet already has 5,492,955 downloads in 4 months**; ICICLE's lattice API
   satisfies ②④⑤ but crates.io stops at 1.3.0 (2024-02-14); Lazarus stops at 0.1.0 (571 downloads), larkworks was never
   published because of `license = ""`, and LatticeFold has no release (issue #193).
   **We are currently the one with ④⑤ complete, ② complete in shape (but with the G1 boundary defect), and ①③ at zero** —
   so the nature of the gap is "two layers of engineering shell", not mathematics. The peers' latest anchors: `ark-ff` 0.6.0
   (2026-04-26, 96,358,403 downloads), Plonky3 0.7.0 (2026-09-04, release-plz automated per-crate tags + the full
   windows/SIMD/wasm matrix), `ml-kem` 0.3.2 (7.51M), `ml-dsa` 0.1.1 (2.74M), `sntrup761` newly created in 2026-02 and released
   in 03, `tfhe-ntt` 0.7.1. The round-3 candidates we implemented were each covered upstream during 2026,
   **so "we implemented it too" is no longer a differentiator**.

7. **The counter-argument that must be recorded alongside all of this** (see 03 §6.1): the thesis that "PQC and ZK share an
   algebra foundation" **has no production-deployment validation yet** — Zama owns the strongest Rust lattice ring/NTT layer
   (`tfhe-ntt`), yet its `tfhe-zk-pok` falls back to `ark-bls12-381`/`ark-ec` instead of its own ring layer. Our answer can only
   be existing facts (the `pqc`/`zk` crates both depend solely on `algebra` and line up with the KATs), not a vision. The
   industry's mainstream behaviour is **forking algebra libraries rather than following upgrades** (SP1→`slop-*`, Ceno pinning
   `=0.4.3`, `blstrs` frozen for three years, our own `lettuce` `[patch]` and `hachi-pcs` choosing `tfhe-ntt`), so
   **fork-resistance (G2/G3/G4/G6 + a pluggable backend) is the reason this project exists, not engineering decoration**.

8. **The recommended next step is not adding features but the "stop-the-bleeding package" G1–G7** (see 03 §5 P0): fix boundary
   correctness + release and version policy + a public-API gate + repair the only real consumer + align the library names +
   remove `rand` from public signatures + remove documentation drift. On the 0–4 scale, these seven items lift D1/D2/D3 from
   0–1 to 3; only then do the remaining dimensions mean anything.

---

## Reading guide

- Only want to know "how far off we are" → the 03 §1 scorecard + items 1 and 7 of the executive summary.
- Want to know "how others do it" → the per-dimension horizontal matrix in 02 §2 (with verifiable versions/dates/download counts).
- Want to start working → the P0 table in 03 §5 (each item lists the action, the size, and the criterion for closing it).
- External positioning (the existing English documentation site) is in `docs/src/pages/reference/ecosystem.mdx`; this document set
  is **internal decision material**, maintained separately from the user-facing site, and its conclusions should be rewritten in
  the site's house style if they are ever published externally.

## Scope and limitations

- Peer data comes from public repositories and the crates.io API (query date 2026-09-19); download counts are cumulative and are
  used only for order-of-magnitude comparison.
- The LOC figures for the internal parallel stacks are source lines counted by `find … | xargs wc -l` (comments and tests
  included), with no de-noising.
- Maturity scores are **ordinals** (a 0–4 level rubric, see 01 §4), used for ranking, not measurements; every score must be
  traceable to a piece of evidence.
