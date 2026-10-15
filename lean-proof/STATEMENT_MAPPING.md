# Primary finite-X theorem: statement mapping for critical review

This is a same-driver mapping, not an independent review verdict. Frozen input:
`family173-primary-pruning-lean-v0.1.0.zip`, SHA256
`3887ead9fe316e3c5fda1dd547db092bb5664cfd4243d10149bccabc76fd9257`.
The prose reference is `project/reference/PRIMARY_PRUNING_NOTE.v1.0.1.md`,
identical to `MATHEMATICAL_NOTE.md` at public commit
`3ab126e27a272ae2905382793265eb1bf74e2892`. Review sections 1, 7 and 8.
Formal source names below are relative to `project/` unless explicitly prefixed
with `project/`. This table is a claim to check, not an acceptance oracle.

| Claim or risk | Formal source and review finding |
|---|---|
| Domain and inputs | `exact_published_matching_capacity` in `CapacityAcceptance.lean` has arbitrary finite `X`, decidable equality, arbitrary relation `r`, and finite pair sets `R,C`. Decidable equality is classically available; no orientation, symmetry, nonemptiness, feasibility, optimal witness, or budget hypothesis is added. |
| Original corners | `IndependentAcceptance.lean` spells `Znote` and `Hnote` by their original quantified definitions, then proves equality to the underlying definitions. No retained pair set occurs in those corner arguments. |
| Separate roles | `CapacityAcceptance.lean` spells Gamma using left `R ⊕ Z` and right `C ⊕ Z` tagged subtypes. Identical coordinates do not identify tagged vertices. The three allowed edge blocks are literal, and the `Z--Z` block is `False`. |
| Auxiliary capacities | The same acceptance theorem expands the B0 and A0 edges with the unchanged-coordinate equalities and the exact arrow directions. The conclusion takes the minimum of their matching numbers. |
| Actual matching number | `Family173/MatchingNumber.lean` defines the number using a maximum matching in a finite graph and proves the matching/cover inequalities used later. It is not a predicate that assumes a capacity bound. |
| No hidden order restriction | `Family173/CapacityCover.lean` introduces a finite classical linear order internally to use the shared-order selector. The final capacity theorem does not demand an order or selector premise from its caller. |
| Transposition | `Family173/Transposition.lean` swaps pair coordinates and original sides while retaining the same relation `r`. It proves both corner correspondences and the graph matching comparisons needed for the A0 bound. |
| Admissibility | `AdmissiblePruning` in `Family173/PruningOptimum.lean` contains exactly subset-left, subset-right, no retained conflicts, retention of original left isolates, and retention of original right isolates. `FinalPruningAudit.admissible_exact` expands these literally. There is no cost or optimum condition in the predicate. |
| Uncovered count | `FinalPruningAudit.qNote` filters the original `Znote r R C` by absence of left and right coverage from `R',C'`; `qNote_exact` proves equality to `uncoveredZ`. Finsets count distinct points; neither tags nor conflicts are counted. |
| Signed objective | `pruningObjective` casts both the natural deletion count and original uncovered count into integers before subtraction. It is not truncated natural subtraction and is not clipped at zero. |
| Actual minimum | `admissibleObjectives` filters `powerset(R) × powerset(C)` by admissibility and maps every surviving pair to its integer objective. `minimumPruningObjective` is its `Finset.min'`. Nonemptiness is proved before this definition, using matching/cover attainment, without assuming the proposed minimum value. |
| Lower bound and attainment | `canonical_cover_bound` converts every conflict-free retained pair to a tagged cover. `admissible_pruning_of_cover` retains original isolates. `exists_admissible_optimal` combines both charges with a minimum Gamma cover; it does not use the capacity bound to establish existence. |
| Primary target | `FinalPruningAudit.exact_published_optimum_and_attainment` states the actual minimum formula, its beta bound, and an admissible pair attaining that minimum and satisfying `d <= beta + q`. |
| Unbounded sharp family | `Family173/SharpFamily.lean` represents the distinct symbols by disjoint sum constructors with indices `Fin(k+1)`. Only the specified arrows occur. All natural `k` are allowed, so all positive sizes occur. Exact corner, matching and optimum counts are proved. |
| Real coefficient and additive allowance | `Family173.coefficient_one_sharp` and `FinalPruningAudit.exact_real_coefficient_one_sharpness` quantify over every real `c,K`, with only `c<1`. The chosen input defeats the smaller coefficient for every admissible pruning. `K` need not be nonnegative. |
| Nonvacuity | General admissible attainment supplies an actual pruning on every input. The preserved `LocalSemanticAudit.lean` additionally derives actual-minimum semantics directly from the finite objective set, covers every positive sharp size, and adds an explicit admissible witness to the real sharpness obstruction. Existing `Nonvacuity.lean` instantiates the relation with loops/opposite arrows and an empty finite type. |

The formal capacity proof uses a direct cover lift from the accepted shared-order
selector argument, rather than formalizing the note's matrix proof line by line.
Statement agreement does not imply proof-method agreement or executable extraction.

## Deliberate exclusions

This review target is the primary finite-X theorem and coefficient-one sharpness.
It excludes the arbitrary infinite ambient-set reduction, the whole Seymour
manuscript, all ancillary source examples and alternative proofs, Python/JSON
encoding equivalence, algorithm complexity, and novelty or priority. The negative
grid objective is not separately exported as a formal example; the signed integer
definition permits negative values. Finite diagnostics are not general-proof premises.

## Independent reviewer task

Check every row against the actual frozen source and prose. A theorem named
`IndependentAcceptance` is an independently spelled statement, not evidence of an
independent author or reviewer. Reject the mapping if a definition, quantifier,
premise or type coercion weakens the primary theorem. Report execution limitations
separately from mathematical objections. Do not accept this table as an oracle.
