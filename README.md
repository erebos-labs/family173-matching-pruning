# Family 173: matching-capacity pruning

Erebos Labs. Capacity corollary **v1.0.1**, with historical partial addendum **v1.1.0** complete rank-free addendum **v1.2.0**, and scoped Lean proof package **v1.3.0**.

For the exact conflict and coverage definitions in [the note](MATHEMATICAL_NOTE.md),
let Z,H be the original corner sets, Gamma the augmented bipartite graph, and
B0,A0 the two auxiliary incidence graphs. Set beta=min(nu(B0),nu(A0)). Then

    nu(Gamma) <= |Z| + beta
    min_admissible_prunings(deletions - uncovered_original_Z_points)
        = nu(Gamma) - |Z| <= beta.

The infinite sharp family has |H|=n^2, beta=n and optimum deletions-q=n.
The coefficient 1 is sharp, and the improvement over the |H| budget is unbounded.

This is a **short structural corollary of OpenAI's pinned rank argument**.
The substantive generic-rank and kernel-lift construction is inherited.
Novelty and priority are unestablished. The primary finite-X theorem now has
a scoped Lean proof in [lean-proof/](lean-proof/README.md). No human referee
review or endorsement of the full Seymour conjecture proof is claimed.
Preparation, implementation and agent review were AI-assisted.

## Read and check

[MATHEMATICAL_NOTE.md](MATHEMATICAL_NOTE.md) supplies all definitions and the
general structural proof, allowing loops, opposite arrows and coincident
coordinate roles. R and C remain separate tagged sides. The objective uses
ordinary integer subtraction and the fixed original Z; negative optima are valid.

Python **3.10 or newer**, standard library only:

```sh
python3 verify_all.py
python3 -O tests/run_tests.py
python3 independent/checks.py
```

The first command checks payload integrity, the original capacity finite suite, isolated
verifier execution and constructor CLI reproduction. The optimized command
runs the checks with assertions disabled. The last command is the audit-owned
minimum-cover oracle and additional corruption controls.

For an individual certificate:

```sh
python3 src/verify.py examples/sharp_2x2.instance.json examples/sharp_2x2.certificate.json --bruteforce
python3 src/verify.py examples/grid_3.instance.json examples/grid_3.certificate.json --bruteforce
```

The grid example has d=6,q=9 and true optimum d-q=-3. Direct retention
enumeration is exponential and defaults to at most 18 original vertices.
Larger examples use exact matching/equal-size-cover certificates; exceeding the
enumeration cap is a resource limit.

To generate new examples without overwriting shipped files:

```sh
python3 src/examples.py /tmp/family173-generated-examples
python3 src/construct.py examples/sharp_2x2.instance.json /tmp/family173-new-certificate.json
python3 src/verify.py examples/sharp_2x2.instance.json /tmp/family173-new-certificate.json --bruteforce
```

The standalone verifier reconstructs the exact original definitions. It checks
matchings and equal-size covers for Gamma,B0,A0, admissibility and the canonical
pruning cover. It imports neither the constructor nor a matching library.

## Evidence and limits

[STATUS.md](STATUS.md) and [audit/REVIEW.md](audit/REVIEW.md) distinguish
the general proof from finite testing. Fresh normal and optimized macOS runs
passed 20 named examples, all 4105 labeled inputs on |X|<=2, 360 seeded larger
cases and deliberate invalid certificates/inputs. The independent oracle adds
12495 minimum-cover optima over those 4105 inputs and 60 fresh cases.
[logs/](logs/) retains portable output from the public package.
[CI](https://github.com/erebos-labs/family173-matching-pruning/actions) runs
the bounded checks on Linux and macOS. CI outcomes are available on GitHub.

The finite checks support the software; they do not prove the general theorem.
See [LIMITATIONS.md](LIMITATIONS.md). Lean verification is limited to the
exact named statements in [lean-proof/](lean-proof/README.md); Python equivalence
and the entire manuscript are outside that scope.

## Attribution, licensing and releases

Pinned antecedent: [openai/math at 1581d4cb](https://github.com/openai/math/tree/1581d4cbdd69a0faf34b2089614fe2a814316a6a),
`preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/02-pruning.tex`.
The source already supplies independent images Bu^r in ker(A). Restricting A
to im(B), then applying a support-matching bound and the exact transpose, yields
the capacity refinement. The converse-cover identity and sharpness are explicit
companion calculations; no priority claim is made for them.

[LICENSE](LICENSE) is Apache-2.0. [NOTICE](NOTICE) identifies Erebos Labs'
material and the unchanged OpenAI source snapshot. No other literature text,
PDF or third-party mathematical implementation is redistributed.

The [v1.0.1 release](https://github.com/erebos-labs/family173-matching-pruning/releases/tag/v1.0.1)
contains a clean package ZIP, SHA256SUMS and release provenance. The original
audit input has SHA256 b2434d3008af12f7c7f4b0e495b8439cf25f36461987773752e6d79fc7118b83;
the public ZIP has its own hash. Private preparation records are not distributed.

To seal and deterministically package an intentional source update:

```sh
python3 tools/seal_package.py
python3 verify_manifest.py
python3 tools/package_release.py --output /tmp/family173-release-assets
```

The packager refuses an existing output asset. Do not reseal merely to accept
unexpected changes.

## Partial combinatorial addendum — v1.1.0

[combinatorial-pruning/](combinatorial-pruning/) adds independently audited
rank-free exposure transfer, mandatory-core separation and a checked failed-
shortcut counterexample. The complete rank-free residual proof was unresolved in that edition;
[residual-cover/](residual-cover/) now supplies it in v1.2.0.
The original capacity theorem and its v1.0.1 rank proof above are unchanged.

The addendum includes hardened certificate decoding, 28 targeted rejection
regressions, its ordinary partial proof, reproducible fixtures and independent
finite checks. Novelty is unestablished and no Lean claim is made. See its
[status](combinatorial-pruning/STATUS.md) and
[limitations](combinatorial-pruning/LIMITATIONS.md). The
[v1.1.0 release](https://github.com/erebos-labs/family173-matching-pruning/releases/tag/v1.1.0)
is additive; the earlier v1.0.1 tag, release and assets remain available.

## Constructive residual cover addendum — v1.2.0

[residual-cover/](residual-cover/) supplies the independently audited shared-order
matching-selector proof of the residual-cover statement. Together with inherited
exposure/mandatory-core results, it completes the rank-free accounting for the
already established capacity refinement. The v1.0.1 rank proof and historical
v1.1.0 partial addendum are preserved. Novelty is unestablished; no Lean theorem,
human referee review or full Seymour endorsement is claimed.

From the root, run `python3 -B residual-cover/src/reproduce.py`, then
`python3 -B -O residual-cover/src/reproduce.py` and the independent oracle
`python3 -B residual-cover/independent/checks.py` (also with -O).
Diagnostic checks stay active under optimization; original corner geometry,
strict certificate parsing and exact manifest inventory are verified.
This additive edition preserves the preceding releases. The v1.2.0 release
contains the selected package, checksum list and committed-source provenance.

## Scoped Lean proof package — v1.3.0

[lean-proof/](lean-proof/README.md) supplies the independently AI-reviewed
prose-to-formal mapping and kernel-checked finite-X capacity bound, actual signed
pruning minimum/attainment, beta budget and unbounded coefficient-one sharpness.
It preserves36 frozen proof/audit sources and all earlier releases. Fresh clean
source builds cover999 external+36 local modules, with only standard logical
axioms in the audited declarations. A portable source-only rebuild retains all
commands/logs/hashes. The compiler distribution remains trusted.

Run `python3 -B lean-proof/reproduce.py --fetch --output /tmp/family173-lean-clean-1`
with the pinned Lean4.34.1 compiler available, following its README. The existing
CI workflow runs Python/integrity checks; it does not run Lean. This is a
formalization of this specific structural corollary, not a novelty claim or a
proof of the wider conjecture.
