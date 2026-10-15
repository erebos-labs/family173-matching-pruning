> Historical development inventory. Its hold/review/cache wording describes the earlier work. See ../README.md and ../review/PROCESS.md for this release.

# Primary pruning theorem: exact coverage inventory

Status: PASS. Clean rebuild checks all 36 modules at trust level zero with
autoImplicit=false; all 120 named Family173 theorem axiom reports and literal
acceptance reports use only standard axioms.
Publication remains on hold. This is the finite-X pruning theorem, not a proof
of Seymour's conjecture or a formalization of the entire source manuscript.

| Published mathematical claim | Kernel theorem / source | Coverage |
|---|---|---|
| Original Z,H and L0/N0/B0/A0/Gamma, with separate tags | IndependentAcceptance.lean, CapacityAcceptance.lean; pinned PruningDefinitions/AugmentedGraph | Literal corner and graph relations; loops/opposites/coincident coordinates admitted |
| Shared-order CC for arbitrary feasible W and input cover | Family173.cover_conversion; exact_published_CC | Original corners, arbitrary matching/cover; signed integer budget |
| Generalized residual G_W | Family173.generalized_residual_bound; exact_generalized_residual | Only the published W-feasibility premise |
| nu(Gamma)<=|Z|+min(nu(B0),nu(A0)) | Family173.matching_capacity; exact_published_matching_capacity | All finite X and arbitrary relation/R/C; no extra caller premise |
| Exact admissibility | Family173.AdmissiblePruning; FinalPruningAudit.admissible_exact | Subfamilies, conflict-free, every initially conflict-free original member retained |
| Exact q, with no clipping or multiplicity | FinalPruningAudit.qNote_exact | Distinct points of fixed ORIGINAL Z, covered by neither retained side |
| Converse pruning-to-cover charge | Family173.canonical_cover_bound | nu(Gamma)+q<=d+|Z| for every conflict-free subfamily pair |
| Cover-to-admissible-pruning charge | Family173.admissible_pruning_of_cover | d+|Z|<=cover size+q; original isolated vertices retained |
| Admissible optimum attained | Family173.exists_admissible_optimal; pruning_optimum_identity | An actual admissible pair attains nu(Gamma)-|Z|; every admissible pair has at least that value |
| Actual finite minimum F=nu(Gamma)-|Z| | Family173.minimum_pruning_identity | F is Finset.min' over all admissible pairs' INTEGER d-q values; not defined by the matching formula |
| F<=beta and an admissible pruning with d<=beta+q | Family173.minimum_pruning_le_beta; exists_beta_pruning; FinalPruningAudit.exact_published_optimum_and_attainment | The attaining pair also satisfies the capacity budget |
| Arbitrary positive-size sharp family | FinalPruningAudit.exact_arbitrary_size_family | n=k+1 for every natural k: |Z|=1, |H|=n*n, nu(B0)=nu(A0)=F=n, nu(Gamma)=n+1 |
| Sharp examples remain loopless and have no opposite pairs | Family173.Sharp.oriented; Sharp.no_two_step | In fact, no directed path of length two exists |
| No smaller universal real coefficient, even with fixed additive constant | Family173.coefficient_one_sharp; FinalPruningAudit.exact_real_coefficient_one_sharpness | For EVERY real c<1 and EVERY real K, one family input violates d<=c*beta+q+K for EVERY admissible pruning |

## Definitions and proof dependence

AdmissiblePruning has exactly the five published structural conditions and no
cost bound. The minimum is computed over powerset(R) product powerset(C),
filtered by those conditions and mapped to d-q in Z (the integer type).
Its nonemptiness is proved by cover-to-pruning attainment before the minimum
is defined. The matching formula is a subsequent theorem, never a premise.
Negative optimum values are allowed. q is not recomputed from retained corners.

The lower charge uses the canonical tagged Gamma cover from any conflict-free
pruning. Retained left and right families cannot both cover the same original
corner; consequently exactly one tagged copy is charged per covered point.
The upper charge adapts the pinned OpenAI CoverPruning construction, preserving
its precise charge rather than substituting the coarser H bound. Minimum Gamma
covers omit isolated vertices; original corner witnesses prove initially
conflict-free members are Gamma-isolated. These charges give equality and
admissible attainment. Konig and all matching/cardinality inputs were already
kernel checked. The capacity proof is the prior direct Gamma-cover lift, which
does not assume the source's mandatory-core accounting.

The sharp family is the published symbol family, represented by disjoint sum
constructors for i,j,p_a,s_b and Fin(n) indices. All sizes n>=1 occur as k+1.
The B0 and A0 lower bounds use indexed injective matchings; Gamma's explicit
matching uses an Option(Fin n) index with two auxiliary edges and n-1 original
edges. Its optimum value uses the now-proved general identity. This certifies
the same sharpness conclusion; it does not separately formalize the note's
alternative independent case-by-case proof of that value.

For real c<1, positivity of 1-c and the Archimedean property choose unbounded
n with n*(1-c)>K. Every admissible pruning satisfies d>=n+q, so all fail the
proposed improved budget. This is a quantified theorem, not finite testing.
There is no assumption K>=0 and no bounded upper limit on n.

## Preservation, verification and exclusions

The accepted CC archive and all existing CC/capacity proof sources remain
unchanged. Work is in a separate versioned workspace. Lean 4.34.1 and exact
pinned Mathlib/dependency sources are reused. Missing Real/Archimedean modules
were compiled locally from those sources at trust level zero, including pinned
Batteries imports. There was no download, installation or external communication.

The final verifier removes all LOCAL proof objects and compiles 36 local/copied/
audit modules with -t 0 and -DautoImplicit=false. It checks the exact 120 named
Family173 theorem axiom reports plus all literal acceptance reports. Only
propext, Classical.choice and Quot.sound are permitted. Source admission scanning
covers local/copied proof and audit targets. External standard libraries retain
compatible cached or locally source-compiled artifacts; a complete compiler or
whole-Mathlib rebuild is not claimed. Finite diagnostics are not used as proofs.

No substantive primary-theorem proof blocker is known. Independent separate-
model/human review, Python/JSON equivalence, execution/complexity refinement,
novelty/priority, and the full Seymour manuscript are outside this result.
Ancillary source arguments and examples (matrix proofs, mandatory-core/extraction
algorithm, rectangular exact formulas, the second q-guard family, and the
arbitrary-ambient-set reduction beyond the stated finite-X theorem) are not
separately exported formalizations. Do not claim the whole note is formalized.
No commit, push, publication or global toolchain/default change occurs.
