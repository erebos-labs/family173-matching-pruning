# Public status, v1.0.1

Date: 14 October 2026. Antecedent: openai/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a.

The exact capacity bound, admissible-pruning consequence, objective identity and
all-n sharpness have an ordinary structural proof. Separate agent proof review
and independent archive/code audit found no gap. No human referee review or
Lean compilation/axiom audit occurred.

Fresh public-package checks on CPython 3.14.7, macOS arm64:

- 20 named certificates.
- All 4105 labeled inputs for |X|=0,1,2, with loops and opposite pairs allowed:
  104995 retention masks and 17241 feasible admissible prunings.
- 360 seeded larger inputs on |X|=3,4,5; at most six originals per side.
- Exact coordinate transposition of corner sets, all graph supports and optima.
- Six supplied graph optima independently enumerated as matchings.
- Twelve supplied damaged certificates and four invalid input forms rejected.
- Standalone verifier execution without the constructor, byte-identical sharp-2x2
  CLI reproduction and syntax compilation.
- The same test suite passed with Python optimization enabled.
- An audit-owned oracle checks minimum covers by subset enumeration, with no
  matching algorithm. It agrees on 12495 graph optima from all 4105 small inputs
  and 60 new seeded n=3 cases, plus direct deletion-objective enumeration.
- All 20 stored instance/certificate pairs checked directly. Direct objective
  enumeration ran for the 18 pairs within the stated size cap.
- Six additional optimized CLI certificate corruptions rejected. A disposable
  modified-file check demonstrated manifest integrity rejection.

These are finite regression results, separate from the general proof.
Portable execution output is in logs/. Linux/macOS CI runs the same bounded
commands and reports its actual outcome on GitHub.

The public edition changes packaging, status, attribution and CI. Sections 1–9
of the mathematical note, all five original src/tests scripts, all example JSON
files and verify_all.py remain byte-identical to the audited
v1.0 input. verify_manifest.py only adds Git metadata exclusion for a checkout.
The independent checker is adapted to a portable public-tree layout.

Novelty/priority is unestablished. This is a short source corollary, not a new
Seymour proof strategy. The full manuscript and downstream consequences are
outside scope. No Lean formalization is delivered.

## Additive v1.1.0 status

The original v1.0.1 capacity proof and evidence above are preserved. The
[combinatorial addendum](combinatorial-pruning/STATUS.md) supplies audited partial
exposure-transfer/mandatory-core proofs and a failed-shortcut counterexample.
Its full rank-free residual remains unresolved. Strict certificate decoding
and fresh normal/optimized controls are included; no Lean result is claimed.

## Additive v1.2.0 status

The [residual-cover addendum](residual-cover/STATUS.md) supplies an independently
audited ordinary rank-free proof of the previously missing residual step.
It completes the combinatorial capacity accounting while preserving earlier
proofs and releases. Two diagnostic/integrity repairs and fresh normal/optimized
controls are included. Novelty remains unestablished and no Lean result is
claimed. The earlier unresolved status above describes v1.1.0 history.
Local preparation results are recorded in the addendum. Hosted CI reports its
actual outcomes on GitHub separately.
