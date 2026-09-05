# Security Policy

## Supported state

This project is **pre-1.0 research tooling**. The honest claims register —
including what is *not* provided (constant-time execution, audits, official
KAT alignment) — lives in the
[security status page](./docs/src/pages/introduction/security-status.mdx).
Reading it is the fastest way to decide whether your report is in scope.

## Reporting a vulnerability

- **Preferred**: open a GitHub security advisory
  ("Report a vulnerability" on the repository's Security tab) — private by
  default.
- **Alternative**: contact the maintainers directly (see the GitHub profile
  of @SuccinctPaul) before filing a public issue.

Please include a minimal reproducer (a failing test is ideal), the crate and
version (`crates/*/Cargo.toml`), and which claim on the security status page
you believe is violated.

## In scope

- Correctness violations of the claims table: wrong signatures accepted,
  honest proofs rejected, encodings that do not round-trip, determinism
  guarantees breaking.
- Soundness issues in the implemented protocol layers (Z1–Z4): extractor
  failures, rejected tampering that verifies, slack-bound violations.
- Panics reachable from public APIs on malformed *but length-valid* inputs
  (decoders are expected to return `None`/errors, not panic).

## Out of scope

- Side channels and timing leaks: **the codebase is not constant-time**;
  this is a documented, non-claimed property, not a vulnerability.
- Missing production hardening (zeroization, fuzzing, `no_std`): roadmap
  items, tracked on the [roadmap](./docs/src/pages/roadmap.mdx).
- Parameter insecurity: concrete levels are not yet claimed; estimator
  calibration is open.

## Disclosure process

1. Report received; acknowledgement within 7 days.
2. Joint triage against the claims register; fix or reclassify.
3. Fix lands through the normal review gate; credit unless you prefer
   otherwise. There is no bug bounty.
