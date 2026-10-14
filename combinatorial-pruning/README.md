# Partial combinatorial pruning addendum

Public edition v1.1.0, Erebos Labs, 14 October 2026.

**Outcome: PARTIAL.** [NOTE.md](NOTE.md) gives complete ordinary rank-free
proofs of exposure transfer and mandatory-core separation:

    nu(B0) = |T| + nu(B0[R minus T, H]).

The construction preserves saturated vertices, with matching edges allowed to
change. A legal two-element counterexample refutes a proposed Hall-set shortcut.
It does not refute the already established capacity bound.

The remaining rank-free accounting
nu(B0[R minus T,H]) >= ell+t-|Z| is **unresolved**. A stronger routing lead
was only finitely tested. The complete capacity inequality has the existing
[v1.0.1 rank proof](../MATHEMATICAL_NOTE.md); this partial addendum supplies no
complete rank-free proof. Novelty and priority are unestablished.

Separate agent proof review and independent archive/code audit found no gap in
the stated partial results. Preparation, implementation and review were
AI-assisted. No human referee review, Lean verification, or endorsement of the
full Seymour manuscript is claimed.

## Reproduce the checks

Python 3.10+; standard library only. From this directory:

```sh
python3 -B src/check_manifest.py
python3 -B src/verify.py
python3 -B src/reproduce.py
python3 -B src/replay_probes.py
python3 -B tests/decoder_mutations.py
python3 -B independent/checks.py
python3 -B -O src/verify.py
python3 -B -O src/replay_probes.py
python3 -B -O tests/decoder_mutations.py
python3 -B -O independent/checks.py
```

The producer and standalone verifier independently reconstruct supports from
the original relation. Equal-size matchings and covers certify all finite
graph optima. Vertex-deletion certificates classify exposure; alternating
paths certify normalization and saturated-vertex extension. The verifier
imports neither the producer nor an optimizer.

Eleven fixtures include loops, opposite arrows, coordinate coincidences, empty
cases, the failed shortcut, asymmetric auxiliaries, preserved isolates, the
negative integer pruning objective, and the inherited sharp example. The fixed
original Z is used throughout.

The certified replay checks 4000 seeded inputs and 4000 transposes, including
215823 finite certificates. Independent minimum-cover enumeration adds 4105
exhaustive small inputs and 80 fresh cases. These are finite software evidence,
separate from the unbounded handwritten partial proofs.
[STATUS.md](STATUS.md), [audit/REVIEW.md](audit/REVIEW.md) and [logs/](logs/)
give actual counts and limitations.

## Certificate hardening in this edition

Every certificate vertex now requires a known string tag and two exact integer
coordinates. Boolean/float aliases are rejected in matching, cover, path,
removed-vertex and normalization records. The schema version also requires an
exact integer. All eleven original fixture files remain byte-identical.
Twenty-eight targeted malformed certificates reject in normal and optimized
Python; additional semantic/path corruptions are retained.

The original source normalization exports a maximum starting Gamma matching
and later paths. An optional supplied hint is not a fully exported hint-to-
maximum trace. See NOTE.md for that explicit limitation.

## Attribution, licence and scope

The unchanged [OpenAI pruning source](sources/02-pruning.pinned.tex) is pinned
to openai/math commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a. Its normalization
and the earlier rank argument are inherited; the new capacity inequality and
sharpness are already the repository's baseline, not contributions claimed by
this addendum. Classical matching antecedents are attributed in the note.

[NOTICE.md](NOTICE.md) and the root [Apache-2.0 licence](../LICENSE) apply.
The unchanged upstream licence is retained in sources/LICENSE.openai-math.
No external literature text or PDF is redistributed. The original preparation
archive is preserved separately; its SHA256 is
62f2fb43b68e8076b9b491db03c0c7c1db84a8b98c1c296fa6ea2e079cbf9b3b.

The [v1.1.0 release](https://github.com/erebos-labs/family173-matching-pruning/releases/tag/v1.1.0)
is additive. Earlier commits, v1.0.1 tag/release/assets and their proof remain
available unchanged. No toolchain installation or Lean result accompanies
this ordinary-proof release.
