# Constructive residual cover conversion

Additive public edition v1.2.0, Erebos Labs, 14 October 2026.

[NOTE.md](NOTE.md) gives an ordinary rank-free proof of the following statement.
For the exact original conflict corners Z,H, every W subset of R matchable into
Z in L0 and every vertex cover K_B of B0[W,H] admit a constructible cover K_N
of the original N0 satisfying

    |K_N| <= |Z| - |W| + |K_B|.

One shared total order yields the ordered matching selectors and their cover
containment. Loops, opposite arrows, coincident coordinates, empty graphs and
nonminimum covers are allowed. Subtraction is ordinary integer subtraction;
the output cover need not be minimum. The construction retains the ORIGINAL
corners after restricting W.

Combined with the inherited exposure/mandatory-core arguments, this closes the
rank-free residual step and proves the already established capacity refinement

    nu(Gamma) <= |Z| + min(nu(B0), nu(A0)).

The [v1.1.0 partial addendum](../combinatorial-pruning/README.md) retains its
historical status unchanged. The [v1.0.1 rank proof](../MATHEMATICAL_NOTE.md),
objective identity and sharpness remain the baseline. No new inequality,
novelty or priority claim is made. Separate agent proof review and independent
archive/code audit found no gap; preparation and review were AI-assisted.
No human referee review, Lean verification or full Seymour endorsement is claimed.

## Reproduce

Python 3.10+, standard library only; from this directory:

```sh
python3 -B src/reproduce.py
python3 -B -O src/reproduce.py
python3 -B independent/checks.py
python3 -B -O independent/checks.py
```

The runner propagates optimization to all child commands. Explicit diagnostic
checks remain active under -O. The standalone verifier reconstructs supports
separately and checks equal-size matching/cover witnesses, prefixes, containment,
budgets, accounting, extension paths and transposition. It imports neither the
producer nor an optimizer. The release controls deliberately damage witnesses,
inject false diagnostic oracles, reject an unlisted nested MANIFEST.sha256, and
check that intentional packaging includes that nested filename.

[STATUS.md](STATUS.md), [audit/REVIEW.md](audit/REVIEW.md) and [logs/](logs/)
record the finite evidence and limitations. The mathematical proof is independent
of the bounded tests. Runtime on large inputs was not benchmarked. The checker
does not prove a formal encoding-to-mathematics equivalence theorem.

## Attribution and licence

The unchanged OpenAI pruning source is pinned to openai/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a. OpenAI's definitions, normalization
and rank machinery retain their attribution. Prior Erebos Labs capacity,
pruning-optimum and mandatory-core work remains explicitly inherited.
The augmenting-path and bipartite-cover antecedents are attributed to Berge
and Konig; the exact forms used are proved in the note. Novelty is unestablished.

The root [Apache-2.0 licence](../LICENSE) and [NOTICE.md](NOTICE.md) apply.
The unchanged upstream licence is retained in sources/LICENSE.openai-math.
Original handoff archives and private transfer records remain preserved locally
and are not redistributed in this selected public package. This is the selected public edition; the original private handoffs remain
preserved separately.
