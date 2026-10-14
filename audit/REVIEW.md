# Independent review summary

14 October 2026, public edition v1.0.1. Verdict: PASS for the bounded corollary.

A separate proof reviewer checked the entire mathematical note and pinned
source and found no gap. A second archive/code auditor independently checked
the same structural dependency chain, source identity and executable evidence.
Both reviews were AI-assisted; no human referee or Lean verification is claimed.

The reviewed chain is: auxiliary matching maximality; blockwise minors and
simultaneous polynomial selection despite variable sharing; NL=AB; maximum-
support kernel restriction with absent-coordinate handling; normalized lifts
and independent images; restricted-image rank-nullity; support-matching bound;
same-relation coordinate transposition; matching-cover equality; isolate
preservation; exact converse-cover charge; and separate all-n sharpness arguments.

The refinement retains im(B) in the source's independent-image construction:
rank(B)>=k+rank(NL). The source already supplies the substantive rank argument.
Neither novelty nor a new proof strategy is established.

The original archive was 103616 bytes with SHA256
b2434d3008af12f7c7f4b0e495b8439cf25f36461987773752e6d79fc7118b83.
A fresh pinned-source retrieval exactly matched the supplied 16261-byte snapshot
and Git blob 4fe3b01285d67d6fb5a5e7a8798a3c12f432ff76.
Manifest checks and all reported regressions were independently replayed.

The audit-owned portable script independent/checks.py supplies a third graph
optimum method: enumerate minimum vertex covers by side subsets, rather than
run a matching algorithm. It agrees on 12495 optima across 4105 exhaustive
small inputs and 60 fresh n=3 inputs. Direct deleted-subset enumeration checks
the objective, all 20 stored certificates are read, and six additional
optimized CLI corruptions reject. A disposable manifest-corruption control
was also rejected. See STATUS.md and logs/.

No required mathematical or implementation repair was found. Malformed derived
or pruning objects are rejected with clean nonzero CLI FAIL exits; an optional
usability improvement could replace their AttributeError wording with explicit
schema labels. This does not affect certificate acceptance soundness.

Scope remains the exact finite-relation theorem, separate from finite testing.
No full Seymour proof review, novelty establishment, Lean audit, or human
review follows. Private audit evidence remains preserved outside this public
package.
