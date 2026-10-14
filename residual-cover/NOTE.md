# Family 173: constructive residual cover conversion

Additive public edition v1.2.0, Erebos Labs, 14 October 2026.

Complete ordinary rank-free proof of the residual-cover statement. Separate
agent proof review and independent archive/code audit found no gap. The
capacity inequality is already established; novelty is unestablished. No
Lean verification, human referee review or full Seymour endorsement is claimed.
Preparation, implementation and review were AI-assisted. Earlier public editions and original handoffs remain preserved.

## 1. Exact definitions, assumptions, and target

For every finite set X, every binary relation → on X, and every pair of
subsets R,C of X², treat all named graph vertex sets as separately tagged
copies. Loops, opposite arrows, and coincident coordinates are allowed.
For (p,j) in R and (i,s) in C a conflict means p→i and s→j. Define

    Z = {(i,j): some original conflict ((p,j),(i,s)) exists},
    H = {(p,s): some original conflict ((p,j),(i,s)) exists}.

These are the ORIGINAL corner sets throughout. Do not recompute them after
restricting R to W or removing cover vertices. The graphs are:

    L0: R -- Z,  (p,j)--(i,j) iff p→i;
    N0: Z -- C,  (i,j)--(i,s) iff s→j;
    B0: R -- H,  (p,j)--(p,s) iff s→j;
    A0: H -- C,  (p,s)--(i,s) iff p→i.

All other edges are absent. Gamma has left R disjoint-union Z_L and right
C disjoint-union Z_R, with original conflicts and the L0,N0 auxiliary
edges, and no Z_L--Z_R edges. Even identical coordinate pairs have distinct
tags. Write nu(G) for maximum matching cardinality.

**Theorem 1 (cover conversion).** For every W subset R admitting an L0
matching that saturates W, and every vertex cover K_B of B0[W,H], there is
an explicitly constructible vertex cover K_N of the ORIGINAL N0 with

    |K_N| <= |Z| - |W| + |K_B|.                         (CC)

All subtraction is ordinary integer subtraction. K_B need not be minimum.
A matching witnessing saturation of W can be supplied to the algorithm.
For b=|K_B| >= |W| the cover Z itself proves (CC). The construction below
handles b<|W| and, in fact, the same formula also works without that branch.

A total order on X will be chosen solely for the construction. It imposes
no symmetry, orientation, invariance, or other restriction on the input.
Every total order works, provided the SAME order is used in all selectors.

## 2. An elementary ordered matching selector

For subsets P,I of X, let F(P,I) be the bipartite graph on distinct copies
of P and I with edge p--i exactly when p→i. In this section the same argument
works for any fixed bipartite edge relation.

Fix a total order < on X. For i in I define I_<=i and I_<i using this order.
Define the ordered selector

    S(P,I) = {i in I: nu(F(P,I_<=i)) = nu(F(P,I_<i)) + 1}.  (S)

This is a definition in terms of finite graph matchings, not matrix rank.
Its computation consists entirely of augmenting paths.

### Lemma 2 (selector properties)

The selector satisfies:

(a) |S(P,I)| = nu(F(P,I)). In particular it has size |P| if P can be
    saturated into I, and always has size at most |P|.

(b) If P subset P', then S(P,I) subset S(P',I).

(c) If I' subset I, then S(P,I) intersect I' subset S(P,I').

(d) Adding/deleting isolated vertices has no effect on selected existing
    vertices, and an isolated right vertex is never selected.

**Proof.** Call a vertex exposable if some maximum matching avoids it, and
mandatory if every maximum matches it. Adding a single vertex changes a
maximum matching cardinality by zero or one. Thus i belongs to S(P,I)
exactly when i is mandatory on the right of F(P,I_<=i). The differences in
(S) telescope, proving (a).

For completeness, the two elementary exposure rules needed here are
proved using alternating paths. For a right-exposable v, choose a maximum
matching M avoiding v, of size m.

* Add a right vertex w. If the new maximum is m, retain M. If it is m+1,
  there is an augmenting path. It must end at w: otherwise w, being free,
  cannot be internal, and the same path would augment the old maximum.
  Flipping therefore leaves v free.
* Delete a left vertex x. If x is free in M, retain M. Otherwise delete
  its edge x--w. The new maximum is m-1 or m. In the first case the
  restricted matching witnesses exposure of v. In the second, augment
  once. The path must end at w, the only newly free right vertex: a path
  ending at an old free right vertex would also augment M in the old
  graph. Flipping again leaves v free.

In both arguments an internally visited vertex was matched before the
flip, so the old free v cannot be internal. Existence of an augmenting
path follows by decomposing the symmetric difference with a larger
matching into alternating paths and even cycles. A component with one
more edge of the larger matching is an augmenting path. This also proves
that successive augmentations terminate at a maximum and preserve all
previously saturated vertices on both sides.

Taking contrapositives of the exposure rules shows that a mandatory right
vertex stays mandatory after deleting OTHER right vertices or adding left
vertices. Apply this to the prefix graphs in (S). Adding left vertices
proves (b). Deleting right vertices outside I' in each prefix proves (c).
Isolated vertices do not affect any prefix maximum, proving (d). QED.

These primitive matching/exposure facts are inherited standard machinery;
compare the earlier archive's Lemmas 2.1 and 2.2. They are not claimed as
new results of this handoff.

**Algorithm for S.** Begin with an empty right side and empty matching.
Add the vertices of I in the fixed order. After each addition, search for
an augmenting path. If one exists, flip it and mark the new right vertex;
otherwise keep the matching. The previous matching was maximum before
the addition, so at most one augmentation is required. Any augmenting
path must end at the newly added vertex. The marked vertices are exactly
S(P,I); previously marked right vertices remain saturated. Thus the
selector is constructive without a generic coefficient choice or a
matroid representation.

## 3. Explicit conversion of the cover

Decompose the supplied cover using its tags:

    U = K_B intersect W,        V = K_B intersect H,
    W' = W \ U.

For every j,s in X define the following subsets of X:

    P_j = {p : (p,j) in W'},      I_j = {i : (i,j) in ORIGINAL Z},
    V_s = {p : (p,s) in V},       I^s = {i : (i,s) in ORIGINAL C}.

Using the one fixed order, set

    Q_j = S(P_j,I_j),             D_s = S(V_s,I^s),
    Q   = {(i,j) in Z : i in Q_j},
    D   = {(i,s) in C : i in D_s}.

The output is

    K_N = (Z \ Q)_L disjoint-union D.                    (K)

Here Z has its left tag in N0 and D has its right C tag. The left input
matching is used as a feasibility certificate; the construction is allowed
to choose different Z endpoints. It is NOT required to preserve the
particular edges or image of that supplied matching.

### Cardinality

Restrict the supplied L0 matching to W'. Since L0 edges preserve j, its
j-block saturates P_j into I_j in F(P_j,I_j). Lemma 2(a) therefore gives

    |Q| = sum_j |Q_j| = sum_j |P_j| = |W'|.

Likewise, Lemma 2(a) gives

    |D| = sum_s |D_s| <= sum_s |V_s| = |V|.

The tags in (K) are distinct. Consequently

    |K_N| = |Z| - |W'| + |D|
          <= |Z| - (|W|-|U|) + |V|
           = |Z| - |W| + |K_B|.                          (count)

The remaining issue is whether (K) covers every edge of N0. This is where
the original pair geometry, rather than Boolean commutation alone, does
real work.

### The geometry-to-selector step

Fix j,s with s→j. Consider any edge p--i of F(P_j,I^s). Then

    (p,j) in W' subset ORIGINAL R,
    (i,s) in ORIGINAL C,
    p→i and s→j.

These endpoints are an ORIGINAL conflict, so both (i,j) in Z and (p,s) in
H. Furthermore, (p,j)--(p,s) is an edge of B0[W,H]. Its W endpoint is not
in K_B, so its H endpoint is in V. Therefore i in I_j and p in V_s.

It follows that in F(P_j,I^s):

    every right vertex in I^s \ I_j is isolated, and
    every left vertex in P_j \ V_s is isolated.          (isolated)

Apply the selector restriction, isolated-vertex, and enlargement rules:

    S(P_j,I_j) intersect I^s
        subset S(P_j,I_j intersect I^s)                  [Lemma 2(c)]
         = S(P_j,I^s)                                    [isolated right vertices]
         = S(P_j intersect V_s,I^s)                      [isolated left vertices]
        subset S(V_s,I^s) = D_s.                        [Lemma 2(b)]

Thus

    Q_j intersect I^s subset D_s whenever s→j.          (containment)

Now take an arbitrary N0 edge (i,j)--(i,s). If (i,j) is not in Q, its Z
endpoint belongs to K_N. Otherwise i belongs to Q_j intersect I^s and
s→j, so containment gives i in D_s. Its C endpoint belongs to D and hence
to K_N. Every edge is covered. Combined with (count), this proves
Theorem 1. QED.

**Equivalent Hall conversion.** The construction proves the stronger
explicit statement

    |Q| = |W\U|,   N_N0(Q) subset D,   |D| <= |V|.

In particular |Q|-|N_N0(Q)| >= |W|-|K_B|. No assertion is made that the
union of all exposable vertices is a suitable Hall set.

## 4. G+, G, and the full matching-capacity accounting

### Corollary 3 (the requested generalized residual inequality)

For every W satisfying the hypothesis of Theorem 1,

    nu(B0[W,H]) >= |W| + nu(N0) - |Z|.                  (G_W)

**Proof.** Choose a minimum cover K_B of B0[W,H]. By the finite bipartite
matching-cover theorem of Konig, |K_B|=nu(B0[W,H]). Apply Theorem 1. Every
matching of N0 has cardinality at most any cover of N0, so

    nu(N0) <= |K_N| <= |Z|-|W|+nu(B0[W,H]).

Rearrange using ordinary integer arithmetic. QED.

For reference, the only use of Konig here has a self-contained
alternating-path proof. Given a maximum matching in a finite bipartite
graph, start from free left vertices; traverse nonmatching edges left to
right and matching edges right to left. No free right vertex is reached.
If reached sets are A_L,A_R, then (left\A_L) union A_R is a cover: an edge
from a reached left vertex to an unreached right vertex would violate the
traversal rules, including the matched-edge rule. Both endpoints of a
matched edge have the same reachability status. The cover contains exactly
one endpoint of each matched edge and no free vertices, so its size equals
the matching size. This verifies all hypotheses of the theorem used above.

### Inherited dependencies, explicitly not new claims

Let M* be a maximum Gamma matching chosen to minimize the number of original
R--C edges. Let their left endpoints be T, put RT=R\T and k=|T|, and write
alpha,eta for the two auxiliary parts of sizes ell,t. The earlier archive
proves, and the user's reported independent ordinary mathematical review
accepted:

    alpha is maximum in L0, eta is maximum in N0;
    every r in T is mandatory in B0;
    nu(B0) = k + nu(B0[RT,H]).                           (core)

It also proves that augmenting a matching in B0[RT,H] to a maximum in B0
preserves its saturated left vertices and eventually saturates T. It does
not preserve the original edges. The earlier public addendum is retained unchanged in
../combinatorial-pruning; original archives remain preserved locally.
A compact dependency reconstruction appears in Appendix A below.

Now choose W=R_alpha. Its matching alpha saturates W, and t=nu(N0), so
Corollary 3 gives exactly

    nu(B0[R_alpha,H]) >= ell+t-|Z|.                     (G+)

Since R_alpha subset RT, it follows that

    nu(B0[RT,H]) >= ell+t-|Z|.                          (G)

Combining (G) with the INHERITED identity (core) gives all three terms:

    nu(B0) = k + nu(B0[RT,H])
           >= k + ell + t - |Z|
            = |M*| - |Z|.

Hence

    nu(Gamma) <= |Z| + nu(B0).                          (capacity-B)

The k contribution is not counted twice, and no loss in ell or t has been
silently replaced by a symmetric assumption.

### Same-relation transposition

Keep the relation → unchanged, and replace R,C by tau(C),tau(R), where
 tau(x,y)=(y,x). The old conflict (p,j)--(i,s) becomes
(s,i)--(j,p), with the SAME conditions s→j and p→i. Thus

    Z^tau=tau(Z), H^tau=tau(H),
    Gamma^tau is Gamma with bipartition sides exchanged,
    B0^tau is A0 with bipartition sides exchanged.

Applying capacity-B to that input gives capacity-A and therefore

    nu(Gamma) <= |Z| + min(nu(B0),nu(A0)).

This is the established inequality, now supplied with the missing
rank-free residual proof. It is not claimed as a new bound. The inherited
ordinary-integer pruning optimum min(d-q)=nu(Gamma)-|Z| is unchanged.

### Constructive matching extraction using the inherited core procedure

For any supplied Gamma matching M:

1. Augment it to a maximum and normalize by reducing original core edges
   whenever an auxiliary augmenting path is available. The inherited
   proof shows that both auxiliary parts then have their maximum sizes.
2. Compute a maximum matching D in B0[R_alpha,H] using augmenting paths.
   G+ proves |D|>=ell+t-|Z|. This is a proved guarantee, not an observation
   obtained by comparing two separately computed maxima.
3. Augment D inside B0 to a maximum. All originally saturated left vertices
   stay saturated, and mandatory-core vertices T are saturated too.
4. Retain just the edges at T and the original left endpoints of D.

The retained edges form a matching of size k+|D|, at least
max(0,|M|-|Z|). Old edges of D may have changed. The fixture producer's
`normalized_accounting` accepts an optional supplied seed matching and
implements this procedure, while the independent checker validates the
resulting saturation-preserving augmentations. The main cover-conversion
CLI does not need to optimize N0 or B0: it uses only the supplied cover and
ordered matching selectors on the arrow relation.

## 5. Algorithm, inherited obstructions, and limitations

The cover algorithm is deterministic after choosing the total order and
matching-search tie-breaking. It makes at most 2|X| selectors, each on at
most |X| vertices per side. Each selector is computed by successively
augmenting along right prefixes. This is an elementary polynomial-time
construction. The Python code favors short, auditable routines, not
large-instance performance.

The converted cover need NOT be minimum. For `mixed-cover-positive`,
|W|=8,b=4,|Z|=9 and the algorithm returns five vertices, exactly its
budget, whereas nu(N0)=3. A minimum output was not required.

The inherited Hall-shortcut obstruction is preserved exactly:

    X={0,1}, arrows={(0,0),(0,1)},
    R={(0,0),(0,1)}, C={(0,0),(1,0)}.

Here Z=X²,H={(0,0)}, and the union of all B0-left-exposable and
N0-left-exposable vertices has Gamma deficiency 0 rather than the required
1. This does not refute the established bound: nu(Gamma)=4<=4+1.
`check_obstructions.py` verifies exposure using equal-size matching/cover
certificates after each relevant vertex deletion, rather than trusting the
old exposability labels.

The shared order really matters to this construction. In that same
example, using order 0<1 for j=0 but 1<0 for j=1 selects
Q={(0,0),(1,1)}. A single C choice cannot cover its two neighbors. Taking
D={(0,0)} makes the purported budget-three cover miss the edge
Z_L(1,1)--C(1,0); adding the missing C vertex costs four. This is a checked
failure of arbitrary independent local choices, not of Theorem 1.

The user-supplied Boolean-support obstruction is also preserved:

    L=I_2, N=all-ones 2x2, B=all-ones 1x2, A=all-ones 2x1.

The Boolean composites agree, but nu(B)=1<nu(L)+nu(N)-2=2. The proof above
uses neither that invalid abstraction nor an implicit assertion that
Boolean commutation suffices. Its two isolated-vertex conclusions use
actual original conflicts and the covering property of K_B.

Repeated H resources are genuinely handled, even with positive residual.
For `repeated-H-positive`, let X={0,1}, let → be all of X², let R=X² and
C={(0,0),(1,0)}, and take W=R and K_B=H. Then

    |Z|=4, |W|=4, |H|=b=2, nu(N0)=2,
    |W|+nu(N0)-|Z|=2.

Two disjoint auxiliary paths, using the supplied adversarial L matching,
both demand H(0,0). The conversion nevertheless returns the two C vertices
as a cover, meeting the budget exactly. This is not a restriction to
instances without collisions or with nonpositive residual.

`original-corners-retained` adds an independent original conflict at (2,2)
but leaves that R vertex outside W. Its original Z,H retain that corner;
the output includes its Z copy. Recomputing Z from W would lose a required
edge of the original N0. This fixture tests the original-corner convention.

## 6. Actual computational checks

All runs used only Python's standard library and exact integer/set
arithmetic. Source was inspected before execution. The producer builds
corners by projecting original conflicts. The separate verifier builds Z
and H from their independently factored existential definitions and then
rebuilds every graph using literal unchanged-coordinate edge predicates.
It imports neither the producer nor a matching optimizer. Every claimed
optimum is certified by a legal matching and an equally sized vertex cover.

Nine named fixtures checked 160 matching/cover certificates, the conversion,
full inherited-core-plus-G+ accounting, and same-relation transposition of
all five graph supports and their optimality certificates.

A predeclared selector diagnostic covered all 512 labelled 3x3 bipartite
supports and all 64 choices of the two vertex subsets per support. Its
32,768 selector systems passed 221,184 enlargement/restriction inclusions.
All 81,920 prefix matching/cover certificates were verified; an independent
exhaustive dynamic program also checked the matching sizes. This is a
finite diagnostic of a lemma proved above, not a proof by enumeration and
not an exported atlas.

A second fixed diagnostic tried every vertex cover of B0[W,H] and every
order on X for the eight named fixtures of size at most three, with W fixed
as named. It checked 2,806 cover/order combinations, including 1,540 with
b<|W| and 2,793 with positive |W|+nu(N0)-|Z|. The counts overlap. It also
constructed eight same-relation transpose conversions separately. This
run verified 27,441 matching/cover certificates. No random input search or
isomorphism classification was used.

The obstruction check verified another 14 exact matching/cover
certificates. Parser tests rejected float replacements at all 587 integer
positions across the mixed-cover and inherited-sharp fixtures, bool aliases
at all 405 eligible positions, and 15 other malformed records/JSON inputs.
These include coordinates inside prefix certificates and extension paths,
not merely original-instance coordinates. They are robustness diagnostics,
not a security or formal-verification claim.

The original authoring tests above were reproduced independently in the
selected macOS environment. New explicit-check repairs retain the DP,
monotonicity and all 14 obstruction certificate checks under optimization.
The runner propagates -O to children. See STATUS.md and logs/ for actual
candidate runs, independent cover-oracle counts and regression controls.
The finite checks are software evidence, separate from the general proof.
No Lean compilation, axiom audit or human referee review was performed.

## 7. Attribution, provenance and edition scope

The exact OpenAI source, its licence and byte identity are preserved.
Commit: 1581d4cbdd69a0faf34b2089614fe2a814316a6a; source:
preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/02-pruning.tex.
Git blob: 4fe3b01285d67d6fb5a5e7a8798a3c12f432ff76; SHA256:
ba7ce7351b1edf1429c8e01533be6172e9e89ac6fca770c2ef5f1c59e918fdb0.
No moving-HEAD claim is made.

OpenAI's definitions, original pruning bound, generic-rank and kernel-lift
argument and source normalization retain their attribution. The capacity
refinement, generalized W inequality, pruning objective identity and sharpness
are inherited from this repository's baseline. Exposure transfer, mandatory
core separation and its identity are inherited from the prior partial addendum.
The new proof supplies the ordered-selector cover conversion and closes the
residual accounting; it is not a new capacity inequality.

The only named classical results used in the conversion are the augmenting-path
characterization (Berge) and finite bipartite matching-cover theorem (Konig),
proved above in their required forms. Edmonds' support-rank comparison belongs
to the inherited algebra. PRIOR_ART.md preserves the author's original limited
search record; it was not re-executed during release preparation. Novelty and
priority are unestablished.

Original archive SHA256:
3812f68f1330b0a1e5d08ea325df2b75107c9f09dc5acf98c2dff0853170e4de.
Its embedded prior archive SHA256:
62f2fb43b68e8076b9b491db03c0c7c1db84a8b98c1c296fa6ea2e079cbf9b3b.
Both remain preserved locally; neither opaque ZIP nor private transport records
are redistributed here. Earlier release material remains unchanged. New public
material uses Apache-2.0, with upstream notices retained; see NOTICE.md.

This public edition follows ordinary proof and independent code
review. LIMITATIONS.md distinguishes those results from formalization,
novelty, large-instance performance and verification of the full manuscript.

## Appendix A. Compact reconstruction of the inherited core dependencies

This appendix is inherited material, not a new contribution.

For a maximum Gamma matching minimizing core edges, suppose its L auxiliary
part were not maximum. An auxiliary augmenting path starts at an unmatched
R vertex of that part and ends at a Z_R vertex free in Gamma. Its internal
vertices are already auxiliary-matched. If the start were free in Gamma,
the path would increase the total matching. Otherwise the start lies on a
core edge; remove that edge and flip the path to reduce k at fixed total
size. Both contradict the choice of matching. The N argument is the dual.
Conversely, a maximum Gamma matching with both auxiliary parts maximum has
k=nu(Gamma)-nu(L0)-nu(N0), so it has the minimum possible k.

For the exposure transfer, fix a B0-left-exposable r=(p,j) covering (i,j),
so p→i. The p-block of B0 has left J_p={j':(p,j') in R} and right
H_p={s:(p,s) in H}, with j'--s iff s→j'. Exposure of j is preserved after
deleting right vertices not in S_i={s:(i,s) in C}. Missing vertices in
S_i\H_p are isolated: a neighbor j' would give an original conflict and
put (p,s) in H. Similarly every j' in J_p\Z_i, where
Z_i={j':(i,j') in Z}, is isolated. Delete those isolated vertices and add
Z_i\J_p as new left vertices. Left exposure is preserved under opposite-side
deletion and own-side addition, the dual of the exposure rules in Lemma 2.
The resulting graph is the i-block of N0. Thus (i,j) is N0-left-exposable.

Opposite-side exposable vertices cannot be adjacent. To see this, take
maximum matchings avoiding the two respective vertices. In their symmetric
difference, an alternating component beginning at one vertex either
permits transferring its exposure without touching the other free vertex,
or yields an augmenting path after their connecting edge is prepended.
More explicitly: choose M avoiding the left x and M' avoiding the right y.
If M also avoids y, xy augments it. Otherwise the component at y begins
with an M edge. It must contain equal numbers of M and M' edges, since an
excess would augment one maximum. It therefore ends at an M-free right
vertex. Its internal left vertices are M-matched, hence not x. Prepend xy
to obtain an M-augmenting path, a contradiction.

For each core edge r--c, its c endpoint is free in the maximum N auxiliary
matching. If r were B0-left-exposable, its conflict corner would be an
N0-left-exposable neighbor of the N0-right-exposable c, impossible. Thus
all k vertices of T are mandatory in B0.

Removing their k edges from a maximum B0 matching gives
nu(B0[RT,H])>=nu(B0)-k. Conversely, start with a maximum of B0[RT,H] and
augment it inside B0. Every previously saturated left vertex survives, and
the final maximum also saturates T. Hence
nu(B0)>=nu(B0[RT,H])+k. These two inequalities give the inherited exact
identity and its constructive saturation statement. No edge-preservation
claim is used. QED.
