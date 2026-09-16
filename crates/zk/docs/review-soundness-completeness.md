# Soundness & Completeness Review (zk crate)

> Scope: every protocol domain in `crates/zk` (commitment / sigma /
> opening / sumcheck + ipa / shortness / folding), reviewed line-by-line
> with an adversarial eye and with the key claims pinned by executable
> tests. Findings are numbered F1–F5; accepted trade-offs K1–K4.
> This report matches the commits containing the sumcheck FS-binding fix,
> the χ-parity pinning test and the documentation hardening.

## 0. Overall conclusion

- **Completeness**: all honest paths are green across the protocol suite.
  The one completeness-level API defect — `RelaxedInstance::satisfying`
  building instances that `verify_folded` always rejects — is fixed (F3).
- **Soundness**: one real API-level soundness defect was found and fixed —
  the sumcheck challenge stream was not bound to the round messages (F1,
  below). The remaining protocols' soundness claims hold under review,
  with one sharpening: the Z2/IPA constraint check is precisely a
  **single-bit** certification (F2), which makes the LaBRADOR recursion a
  required milestone rather than an optional size optimization (K1).
- All gates pass: fmt / clippy `-D warnings` / rustdoc `-D warnings` /
  the full workspace test suite (670+ tests, zero failures).

## 1. Per-domain review

### 1.1 `commitment` (AjtaiKey / ajtai)

- **Binding**: two openings give `A(s − s′) = 0`, a short kernel vector —
  an MSIS break. `A` is seed-expanded and overdetermined at the required
  row counts. ✅
- **Hiding**: Ajtai commitments do **not** hide (deterministic, no noise)
  — the whole crate is transparent and says so. ✅
- Tests: determinism, discrimination, witness bounds. ✅

### 1.2 `sigma` (Lyubashevsky FS-NIZK)

- **Completeness**: the rejection loop accepts with ≈40% probability per
  attempt under the `B_Y − τB_S` accounting; the 128-attempt cap is
  statistically unreachable and returns a typed `RejectionLimit` — no
  panic path. ✅
- **Soundness**: the forking extractor yields the relaxed relation
  `A·s_ext = v·t` with `‖s_ext‖∞ ≤ 2B_Z`, `‖v‖₁ ≤ 2TAU` — asserted line
  by line in tests. ✅
- FS binding: challenges derive from the transcript (key, t, w) —
  commitments land before challenges. ✅
- Known: concrete parameter calibration (lattice-estimator) remains open
  (K4).

### 1.3 `opening` (LaBRADOR-style batched opening)

- **Completeness**: the honest identity `res = C·m + C²·q` holds exactly;
  the 10⁴-gate end-to-end test is green. ✅
- **Soundness (precise post-review characterization, F2)**:
  - the binding link `A·z′ == c + C·d` is exact and overdetermined, so
    `z′` is uniquely pinned (up to MSIS);
  - the masked consistency check `Σγ^k R_k == C·t* + C²·q*` reduces to a
    **single bit**: the coefficient-sum map `χ(f) = Σ f_i (mod 2)` is a
    well-defined homomorphism `R → F_2` (it kills `2` and `X^64 + 1`);
    `χ(C) = 1 − a ≡ 0 (mod 2)` puts `C·R` inside its kernel, and both
    have index 2 (cross-checked by the norm `N(C) = a^64 + 1`, whose
    `v_2` is exactly 1 for odd `a`). By multiplicativity the certified
    bit is `χ(R_0) + χ(γ)·Σ_{k≥1}χ(R_k)` — two `F_2`-linear functionals
    of the witness's coefficient-sum vector. A false response therefore
    passes with probability ½ per mask grind — or deterministically, if
    its witness satisfies those parity conditions structurally.
  - the non-unit challenge argument holds: a unit challenge would make
    the verifier equation solvable for any response (regression test
    pinned). ✅
  - tests: `verifier_equation_is_single_bit_parity` pins the χ semantics
    (honest = 0; gate 0 flips; gates k ≥ 1 invisible when χ(γ) = 0);
    `forged_statement_rejected_despite_binding_link` pins the generic
    forgery rejection. ✅

### 1.4 `sumcheck` + `ipa`

- **sumcheck (F1, the substantive defect fixed in this review)**: the
  original API accepted an arbitrary `FnMut() -> R` challenge closure,
  but the protocol is only sound when round challenges are derived *after
  absorbing the round messages*. With a message-independent challenge
  stream, a forger that knows all challenges in advance can craft a
  message sequence consistent with any claimed sum over its own table —
  a total break when used standalone.
  **Fix**: a `RoundChallenger` trait whose contract is to absorb `(h0,
  h1)` before deriving the challenge, with `FsChallenger` as the
  reference implementation (domain-separated transcript, length-prefixed
  `Display` encoding, challenges mapped through `MatrixElement::random`
  over a transcript-seeded RNG); `prove`/`verify` now take
  `&mut dyn RoundChallenger<R>`; every caller migrated; regression test
  `forged_table_fails_under_fs_binding` pins the property.
- **ring-SZ caveat**: over a ring, Schwartz–Zippel weakens with zero
  divisors — a dishonest round message passes round `i` with probability
  ≤ `|ann(Δ₁)|/|R|` ≤ 1/2 in the worst case (`Δ₁` the leading
  coefficient of the message difference), amplifying multiplicatively
  over the `G` rounds. Documented; field challenges are the conservative
  recommendation for standalone deployments. ✅
- **ipa**: same single-bit semantics as F2 (module doc corrected in the
  same pass); the binding link is exact; the
  `forged_inner_product_claim_rejected` regression test (unit-challenge
  break) exists. Completeness: roundtrip tests. ✅

### 1.5 `shortness` (balanced projection argument + gadget)

- **Soundness**: the balanced split `v = 2^γ·h + l` is **exact**
  (coefficient-wise, no carries in the ring), so the link
  `A·(2^γ·h + l) == c − ζ·(A·t)` is exact and the revealed `h` is the
  true high part of `v` — a forger cannot shrink it. Digit gates +
  binding certify `‖v‖∞ ≤ 2^γ·B_h + 2^{γ−1}`. ✅
- **Completeness**: the split is exact (scanned over `γ ∈ [1, 32)`) and
  the low-digit gate holds by construction. ✅
- **F4 (fixed)**: `verify_projection` with `γ = 0` would panic on a
  shift; parameter validation now rejects at the trust boundary.

### 1.6 `folding` (nova + latticefold)

- **nova**: the fold algebra (cross terms `T_k`, error
  `e′ = e₁ + rT + r²(e₂ + U∘z₂sel)`) is validated by the `r = 0`
  identity, chained folds and tamper-rejection tests; `verify_folded` is
  a transparent verifier (recomputes commitments + exact residual
  comparison), so soundness is the honest verification itself. ✅
  **F3 (fixed)**: `RelaxedInstance::satisfying` left the commitment
  vectors empty — every instance it built was rejected by
  `verify_folded`. Now `FoldKey::satisfying(r1cs, z)`: derives real
  commitments and debug-asserts gate satisfaction.
- **latticefold**: the decomposition `w = Σ2^{bi}·dᵢ` is exact in
  `Z_{2^32}` (`L·b = 32` makes the quotient vanish; asserted), three of
  the four verifier checks are exact linear identities and the fourth is
  a provable norm gate `‖d̃‖ ≤ ΣB_ζⁱ·2^{b−1}`; a forged digit set must
  satisfy two linear systems plus that gate (the splitting query lands
  after the digit commitments). ✅
  Known (K3): this is the simplified core — individual digit norms are
  not separately certified (only the ζ-combination), and the full
  LatticeFold SZ extraction is not reproduced.

## 2. Findings and disposition

| # | Severity | Content | Disposition |
| --- | --- | --- | --- |
| F1 | high (API misuse = break) | sumcheck challenges not bound to round messages; a message-independent stream lets a forger prove any sum | ✅ fixed: `RoundChallenger`/`FsChallenger` enforce absorb-then-derive; all callers migrated; regression test added |
| F2 | medium (doc weakened + sharpened) | the Z2/IPA constraint check is a **single parity bit** (χ homomorphism + norm cross-check) — ½ per grind, or deterministic pass under structurally-satisfiable parity conditions | ✅ docs sharpened + `verifier_equation_is_single_bit_parity` pins it; the root fix is K1 |
| F3 | medium (completeness trap) | `RelaxedInstance::satisfying` produced instances that are always rejected | ✅ moved to `FoldKey::satisfying`, derives real commitments |
| F4 | low | `verify_projection(γ=0)` panicked on a shift | ✅ validated at the trust boundary, returns `false` |
| F5 | low (documented) | hyperball challenge budgets that are infeasible `expect`-panic (the FS derivation is identical on both sides, so consistency is never broken; this is a parameter precondition) | 📌 recommendation: a `Result`-returning variant later |

Process note: the F2 analysis initially produced a *wrong* alternative
characterization (evaluation at `a`, index 2^32) — the newly written test
falsified it immediately (`f ↦ f(a)` is not a well-defined homomorphism
on the negacyclic quotient; it would require `a^64 ≡ −1 mod 2^32`). The
final χ-based characterization is the one that survives the tests. The
incorrect intermediate version never landed.

## 3. Accepted trade-offs (documented, not regressions)

- **K1**: full relation soundness for Z2/IPA requires the LaBRADOR
  recursion (masked terms committed under a second key before the
  challenges open them) — roadmap milestone; the recursive mode
  (`opening::prove_recursive`) now provides the transparent full-relation
  behavior at O(gates) size, with amortization still open.
- **K2**: ZK blinding — `sigma::z2` brings HVZK blinded responses to the
  Z2 line; the full LaZer integer-statement protocol remains open.
- **K3**: `latticefold` is the simplified core (batch decomposition +
  splitting query); the multilinear evaluation assertion (carried by the
  sumcheck) and the full SZ extraction are not reproduced.
- **K4**: no concrete security levels claimed; estimator calibration open
  (`algebra::security` ships the Core-SVP base).

## 4. Test and gate evidence

- 70+ unit tests (including the new
  `forged_table_fails_under_fs_binding` and
  `verifier_equation_is_single_bit_parity`), 6 contract tests, doc tests;
- `cargo fmt --check`, `cargo clippy --all-targets -- -D warnings`,
  `RUSTDOCFLAGS="-D warnings" cargo doc` all clean;
- the full workspace gate passes.
