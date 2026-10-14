# Family 173: a rank-free core separation, but not the full capacity proof

Public addendum v1.1.0. Erebos Labs, 2026-10-14.

Edition changes: review/execution/publication status and certificate-format
checks are updated from the audited v1.0 handoff. Mathematical Sections 1–7
are unchanged. The full rank-free capacity target remains unresolved.

**Verdict: PARTIAL.** This note proves a combinatorial exposure-transfer lemma,
a mandatory-core theorem, and an exact core-deletion identity. It gives a
constructive matching procedure for those results. It does **not** supply a
complete rank-free proof of the requested matching-capacity inequality.
A two-element example refutes a proposed intermediate Hall-set rule, not the
established capacity inequality. No novelty claim is made.

## 1. Exact scope, definitions and target

For every finite set X, every binary relation `→` on X, and every pair of
subsets R,C of X×X, use distinct tags for all graph vertices. The relation may
have loops and opposite arrows; coordinates may coincide. R and C remain
separate copies even when the same ordered pair belongs to both.

For r=(p,j)∈R and c=(i,s)∈C, a conflict means p→i and s→j. Define, using **all
original conflicts**,

    Z = {(i,j): there exist p,s with (p,j)∈R, (i,s)∈C, p→i, s→j},
    H = {(p,s): there exist i,j with (p,j)∈R, (i,s)∈C, p→i, s→j}.

A left member (p,j) covers (i,j) exactly when p→i. A right member (i,s)
covers (i,j) exactly when s→j. The unchanged coordinate is required.
Define five finite bipartite graphs:

* L₀: R to Z_R, with the left-coverage edges.
* N₀: Z_L to C, with the right-coverage edges.
* B₀: R to H, with (p,j)–(p,s) exactly when s→j.
* A₀: H to C, with (p,s)–(i,s) exactly when p→i.
* Γ: R⊔Z_L to C⊔Z_R, with the original conflicts and the edges of L₀,N₀.
  There are no Z_L–Z_R edges.

Write ν(G) for maximum matching size. The requested target, for all such
inputs, is

    ν(Γ) ≤ |Z| + ν(B₀),                                      (T)

followed by transposition to A₀. Ideally a proof would turn any supplied
matching M of Γ into a B₀ matching of size at least max(0,|M|−|Z|).
No symmetry or orientation assumption is introduced here.

### Inherited results, not claims of this handoff

The user supplied the established baseline

    ν(Γ) ≤ |Z| + min(ν(B₀),ν(A₀))

and the integer identity min(d−q)=ν(Γ)−|Z| for admissible conflict-free
prunings. Here d counts deleted original members, q counts distinct uncovered
points of original Z, and initially conflict-free members must survive.
These statements, their known sharp family, and their earlier rank proof are
not presented as new. They are not dependencies of the rank-free partial
proof in Sections 2–5.

OpenAI's pinned source [P] proves the pruning bound using |H| and a matrix
argument. The matching-capacity refinement above is the prior baseline in
the task, not a claim that the source explicitly states the ν(B₀) refinement.
This investigation does not audit the full Seymour manuscript.

## 2. Elementary matching facts, with proofs

All graphs in this section are finite and bipartite. A vertex is **exposable**
if some maximum matching leaves it unmatched. A vertex is **mandatory** if
every maximum matching matches it. Exposability is an existential condition;
it is not the condition of being free in one arbitrarily chosen matching.
Let E_L(G),E_R(G) denote exposable vertices on the indicated sides.

### Lemma 2.1. Augmentation and preservation of saturated vertices

A nonmaximum matching has an augmenting path. Flipping along one increases
its cardinality by one and preserves every previously saturated left vertex
(and every previously saturated right vertex).

**Proof.** Compare it with a larger matching. Their symmetric difference has
degree at most two, so decomposes into alternating paths and even cycles.
Since the larger matching has more edges, one path has one more of its edges
than of the smaller matching's edges. That path has two endpoints free in
the smaller matching and is augmenting. Flipping it changes only its two
endpoints from free to matched; internal vertices remain matched. Conversely
an augmenting path increases size, so cannot occur for a maximum matching.
Repeating augmentation terminates because matching size is bounded by the
finite number of vertices. This also proves the stated characterization of
maximum matchings without invoking a solver or a rank theorem. □

### Lemma 2.2. Two monotonicity rules for exposure

If a left vertex x is exposable, then it remains exposable when vertices
are deleted from the right side, or when vertices are added on the left
side with arbitrary incident edges. Adding or deleting isolated vertices
other than x also preserves its exposability. The dual rules hold on the
right side.

**Proof.** It suffices to treat one modification. Choose a maximum matching
M that avoids x, and let m=|M|.

Delete a right vertex y. If y is unmatched, M survives and stays maximum.
If y is matched to w, remove that edge. The new maximum size is m−1 or m.
In the first case the restricted matching witnesses exposure of x. In the
second, augment it once. An augmenting path cannot start at a left vertex
that was free in M: the same path, avoiding the deleted y, would augment M
in the old graph. It therefore starts at w, the only newly free left
vertex. Internal left vertices are matched, so x is not on the path and
remains free. This gives a maximum matching avoiding x.

Add a left vertex w. The new maximum size is m or m+1. In the first case
use M. In the second case an augmenting path for M must start at w: if it
started at an old free vertex, it could not have w internally, since w is
unmatched, and would augment the old graph. Flipping therefore keeps x
free. Isolated vertices cannot affect any matching. Iterate these arguments
for finitely many changes. □

### Lemma 2.3. Opposite exposable vertices are nonadjacent

There is no edge between E_L(G) and E_R(G).

**Proof.** Suppose x on the left and y on the right are exposable and xy is
an edge. Choose maximum matchings M avoiding x and M' avoiding y. If M also
avoids y, xy augments M. Otherwise the symmetric-difference component
starting at y begins with an M edge. It cannot have more M than M' edges,
since that would augment M', and an alternating path starting with an M
edge cannot have more M' edges. It consequently has equally many of both,
ends on the right at a vertex free in M, and is an even alternating path.
All internal left vertices are matched by M, so none is x. Prepending xy
gives an augmenting path for M, a contradiction. □

A graph that is the disjoint union of coordinate blocks has maximum size
equal to the sum of the block maxima. Every global maximum is maximum in
each block, and local maximum matchings can be combined. Hence a vertex is
exposable globally exactly when it is exposable in its block. This assertion
includes empty blocks and isolated vertices.

## 3. Exposure transfer in the pinned pair geometry

### Theorem 3.1. Left exposure transfers through left coverage

Identify the coordinate sets underlying Z_R and Z_L only for stating this
inclusion, not as graph vertices. Then

    {z∈Z: some r∈E_L(B₀) covers z} ⊆ E_L(N₀).               (E)

Consequently no original conflict joins a vertex of E_L(B₀) to a vertex
of E_R(N₀).

**Proof.** Fix r=(p,j)∈E_L(B₀) and a point z=(i,j) it covers. Thus p→i
and (i,j)∈Z. Set

    J_p={j':(p,j')∈R},   H_p={s:(p,s)∈H},
    S_i={s:(i,s)∈C},     Z_i={j':(i,j')∈Z}.

The p-block of B₀ is the graph J_p to H_p with edges j'–s iff s→j'.
By the block observation, j is exposable in it.

Delete right vertices H_p\S_i. Now add each right vertex in S_i\H_p as
an isolated vertex. This yields exactly the graph J_p to S_i with edges
s→j': if such an edge existed for s∈S_i\H_p and j'∈J_p, then
(p,j') and (i,s) would be an original conflict, putting (p,s) in H,
which is impossible. Lemma 2.2 preserves exposure of j.

Any j'∈J_p\Z_i is isolated in this graph. Indeed, an edge to s∈S_i,
together with p→i, would put (i,j') in original Z. Remove those isolated
left vertices, none of which is the distinguished j. Finally add the left
vertices of Z_i\J_p, with their actual edges to S_i. By Lemma 2.2, j
is still exposable. The resulting graph is exactly the i-block of N₀,
so z is exposable in N₀.

If r conflicts with c=(i,s), its corner z=(i,j) is in Z, r covers z,
and z–c is an N₀ edge. Exposure of r and c would, by (E), contradict
Lemma 2.3. This proves the consequence. □

Both uses of a missing corner being isolated relied on an **original
conflict**, not on a conflict surviving a later deletion. No arrow was
reversed and no coordinates were assumed distinct.

## 4. Mandatory core endpoints and constructive separation

### Theorem 4.1. Mandatory-core theorem

Let M be any matching of Γ whose N₀ part η is a maximum matching of N₀.
Let T be the set of R endpoints of the original R–C edges of M, and put
k=|T|. Then every member of T is mandatory in B₀.

For every B₀ matching D whose saturated left vertices lie in R\T, one
can construct a B₀ matching saturating both T and all the left vertices
saturated by D. The edges of D need not be preserved. In particular,

    ν(B₀) = k + ν(B₀[R\T,H]).                              (C1)

If α is the R–Z_R part of M and R_α its set of R endpoints, then

    ν(B₀) ≥ k + ν(B₀[R_α,H]).                              (C2)

**Proof.** For a core edge r–c of M, c is unmatched by the maximum
N₀ matching η, so c∈E_R(N₀). If r were exposable in B₀, the consequence
of Theorem 3.1 would forbid this conflict. Thus r is mandatory.

Start from D and repeatedly augment in B₀ until a maximum matching is
obtained. Lemma 2.1 preserves every initially saturated left vertex. The
final maximum also saturates every vertex in T. Retain only its edges at
T and at the original left endpoints of D. This is a matching of size
k+|D|, proving the constructive assertion.

For (C1), removing the k edges at T from any maximum B₀ matching gives
ν(B₀[R\T,H])≥ν(B₀)−k. Conversely, apply the constructive assertion to
a maximum matching in B₀[R\T,H]. This gives the reverse inequality.
For (C2), the matching property of M implies R_α∩T=∅; start instead
with a maximum matching of B₀[R_α,H]. □

This is a cardinality and saturated-vertex extension, not an assertion
that D as an edge set extends to a larger matching. That distinction is
important for an alternating-path algorithm.

### Source normalization and what the supplied code does

Starting with any maximum matching of Γ, repeatedly augment its L₀
submatching whenever it is not maximum. An auxiliary augmenting path ends
at a Z_R vertex free in Γ. Its starting R vertex cannot also be free in
Γ, since then the path would augment the Γ matching. It must be matched
to C. Delete that one core edge and flip the auxiliary path. Total size
is unchanged and the core count drops by one. Repeat on N₀ with sides
reversed. N₀ normalization does not disturb the L₀ matching. Both
processes terminate, giving maximum auxiliary matchings of sizes ℓ,t.
Then k=ν(Γ)−ℓ−t is minimal among maximum Γ matchings. This is the
normalization from [P], reproduced for the partial algorithm, not new work.

`src/producer.py` implements augmentation, this normalization, and the
construction in Theorem 4.1. It may use an optional supplied matching as a
starting hint. The exported trace begins at a maximum Γ matching; initial
augmentation from a hint to that maximum is computed but is not retained
as a trace. The normalized maximum and all later paths are certified.
The proved output size for the core construction is k+ν(B₀[R_α,H]).
A rank-free proof that this reaches the requested target is **not supplied**.

## 5. Same-relation transposition, explicitly

Keep exactly the same set X and the same arrows. Replace the families by

    R^τ={(s,i):(i,s)∈C},    C^τ={(j,p):(p,j)∈R}.

An old conflict (p,j)–(i,s) becomes the new conflict (s,i)–(j,p):
its two conditions are s→j and p→i, precisely the old conditions in the
opposite order. Therefore

    Z^τ=τ(Z),  H^τ=τ(H),  where τ(a,b)=(b,a).

The vertex bijection swaps R with C, swaps Z_L with Z_R, swaps the two
coordinates, and maps H to τ(H). It reverses the graph bipartitions and
identifies

    Γ^τ ≅ Γ,   B₀^τ ≅ A₀,   A₀^τ ≅ B₀,
    L₀^τ ≅ N₀, N₀^τ ≅ L₀.

Every edge predicate follows from the unchanged-coordinate conditions
above; for example, an old A₀ edge (p,s)–(i,s) becomes a new B₀ edge
(s,i)–(s,p), with condition p→i. Tagged copies remain distinct even when
τ fixes their coordinates.

Thus a proof of (T) would give ν(Γ)≤|Z|+ν(A₀) with no reversal of the
relation. Applying the **proved partial theorem** instead gives: if α is
maximum in L₀, every core C endpoint is mandatory on the right of A₀.
For a normalized matching, if U is that set of k core C endpoints, then

    ν(A₀)=k+ν(A₀[H,C\U]).

This is the exact dual partial result, not a completed proof of the A₀
capacity target.

## 6. Where global accounting remains unresolved

For a normalized maximum M, |M|=k+ℓ+t. By (C1), the requested bound is
now **equivalent** to

    ν(B₀[R\T,H]) ≥ ℓ+t−|Z|.                              (G)

A stronger sufficient statement is

    ν(B₀[R_α,H]) ≥ ℓ+t−|Z|.                              (G+)

Neither (G) nor (G+) is proved rank-free in this handoff. They are not new
conjectures: the inherited algebraic argument supplies the required
accounting. They identify exactly which part has not been translated.
If ℓ+t≤|Z|, (C1) already suffices, but that special case is not the full
target and is not offered as a substitute success.

For comparison only, the prior rank proof uses the commuting square
NL=AB. Restricting L,B to the columns R_α gives

    rank(B|R_α) ≥ rank(N L|R_α) ≥ ℓ+t−|Z|,
    rank(B|R_α) ≤ ν(B₀[R_α,H]).

These are explicitly algebraic inequalities, not a combinatorial proof
hidden under different notation. The source's generic coefficient choice
and its local maximum-support conditions are inherited machinery, not
independently eliminated here. The partial theorem replaces the local
kernel restriction and the k separation by exposure and augmentation;
it does not replace the remaining dimension-loss estimate.

A finite exploratory routing test fixed maximum α,η and asked whether
all C endpoints of η could be matched into H⊔(Z\V(α)), using reversed
A₀ edges and right-coverage edges. The 4,000 seeded probes found no
failure, and their sizes were subsequently checked with matching/cover
certificates. No universal routing theorem or sufficient global reduction
was established. This lead is recorded as unproved, not promoted to a
solution on the strength of those tests.

## 7. A checked failure of the natural Hall-set shortcut

For a bipartite graph, a left set S forces any matching to leave at least
|S|−|N(S)| left vertices unmatched. A plausible transfer rule was to set

    E=E_L(B₀), F=E_L(N₀), S=E ⊔ F_L,

and hope that

    |S|−|N_Γ(S)| ≥ |R|−ν(B₀).                             (FALSE)

This would imply (T), since Γ has |R|+|Z| left vertices. The exposure
inclusion (E), however, does not justify this cardinality claim.

Here is a counterexample to **(FALSE)**. Let

    X={0,1}, arrows={(0,0),(0,1)},
    R={(0,0),(0,1)}, C={(0,0),(1,0)}.

All four pairs r–c conflict. Hence Z=X×X and H={(0,0)}. B₀ is K₂,₁,
so ν(B₀)=1 and E=R. N₀ is two disjoint copies of K₂,₁, so all four
of its left vertices are exposable and ν(N₀)=2. Consequently S is all
six Γ-left vertices and N_Γ(S) is all six Γ-right vertices. Its
deficiency is zero, whereas |R|−ν(B₀)=1.

Exact optimality certificates are easy to read. In B₀, use matching
R(0,0)–H(0,0) and cover {H(0,0)}, both of size one. In Γ, use

    R(0,0)–Z_R(0,0),  R(0,1)–Z_R(1,1),
    Z_L(0,0)–C(0,0),  Z_L(1,1)–C(1,0).

These four edges form a matching. R⊔C is a cover of size four. Thus
ν(Γ)=4, and the established bound remains true: 4≤4+1. In fact
Z_L alone has deficiency 4−2=2; the failed rule chose the wrong Hall
set, not a graph that violates the theorem.

The same fixture exposes a naive path-concatenation error. The two paths
R(0,0)→(0,0)→C(0,0) and R(0,1)→(1,1)→C(1,0) use distinct R,Z,C
vertices but both route through H(0,0). Their B₀ edges cannot both belong
to a matching. Here ℓ+t−|Z|=0, so this collision also does not refute
(G) or (G+). The JSON fixture preserves a supplied matching with precisely
these paths. No minimality claim for this counterexample is made.

## 8. Verification, reproducibility and limits

The handwritten partial proofs are unbounded arguments. The following
computations challenge them; they are not proofs for all finite X.

The independent checker reconstructs Z and H by separately testing their
two existential coordinate conditions, rather than projecting the
producer's conflict list. It then rebuilds every graph from literal edge
predicates. It imports neither the producer nor the exploratory probe and
runs no matching optimizer. Each claimed optimum comes with a legal
matching and an equally sized legal vertex cover. Any matching has size
at most any cover, so equal sizes certify both optima. Vertex-deletion
certificates classify exposability exactly. Separate path checks replay
normalization and saturated-vertex extension.

Eleven retained fixtures cover empty X, empty R, empty C, no conflicts,
a single loop with all coordinate pairs coincident, opposite arrows,
the failed Hall set, asymmetric auxiliary sizes, negative integer d−q,
the supplied sharp family at n=3, and that family with isolated original
members. The checker enumerates every keep/delete subset of the original
members on these fixtures, retains the initially conflict-free members,
and rejects surviving conflicts. It uses the fixed original Z for q and
checks every pruning-to-cover conversion. There are 69 admissible prunings
across these fixtures. This checks the inherited optimum identity, not a
new theorem. In particular the negative fixture gives ν(Γ)−|Z|=6−9=−3.
The known sharp fixture gives (|Z|,|H|,ν(B₀),ν(A₀),ν(Γ))=(1,9,3,3,4).

The fixture run checked 221 equal-size matching/cover certificates and
rejected six deliberately corrupted certificates. Every graph and its
certificates were checked under the exact same-relation transposition.

The bounded replay uses Python Random(173), 1,000 trials each for |X|=1,2,3,4,
with arrows,R,C selected independently at probability 0.45 from all ordered
pairs. All 4,000 inputs and their 4,000 transposes were checked. These are
samples, not 8,000 distinct isomorphism classes or an exhaustive census.
No symmetry reduction is used and no atlas of these inputs is exported.
The replay checked 215,823 matching/cover certificates, 925 L-normalization
steps, 936 N-normalization steps and 982 core-extension augmentations.
There were 102 records with nonempty core. The unproved fixed-α routing
lead was checked on the original 4,000 samples. The input-stream SHA256
and actual console output are in `logs/probe-certified-replay.log`.

The original v1.0 preparation ran on CPython 3.13.5, Linux. Independent
archive/code audit and the hardened public edition also ran on CPython 3.14.7,
macOS arm64, using the standard library. Separate agent proof review and a
third minimum-cover oracle support the stated partial results. These are
AI-assisted reviews, not human referee review. No Lean compilation or axiom
audit was performed; no installed local toolchain was located. Public-format
checks reject Boolean/float certificate coordinates. Current evidence and
limitations are in audit/REVIEW.md, STATUS.md and logs/.

## 9. Attribution, prior work and decision

[P] OpenAI, *A proof of Seymour's second-neighborhood conjecture*, paper
README dated 2026-09-23. Pinned repository commit
`1581d4cbdd69a0faf34b2089614fe2a814316a6a`; source file
`preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/02-pruning.tex`.
The relevant labels are `lem:pruning`, `lem:kernel-support`,
`eq:pruning-commute`, and `eq:conflict-kernel`. The unchanged source is
included, with its Apache-2.0 license. Its Git blob SHA-1 is
`4fe3b01285d67d6fb5a5e7a8798a3c12f432ff76`; its SHA256 is
`ba7ce7351b1edf1429c8e01533be6172e9e89ac6fca770c2ef5f1c59e918fdb0`.

The current source has the same blob. The observed repository head was
still the pinned commit; the file-specific history returned only initial
commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`. The small existing Lean
entrypoint `SecondNeighborhood/Pruning.lean` was read and imports
`AugmentedRankBound`; its dependency closure was not audited or compiled.

The source explicitly cites Jack Edmonds, *Systems of Distinct
Representatives and Linear Algebra*, J. Res. NBS 71B(4) (1967), 241–245,
DOI 10.6028/jres.071B.033, §5, Theorem 1, printed p.242. That theorem
identifies term rank with the rank of a matrix of distinct indeterminates.
Its primary text was checked, including a screenshot of that page. It is
an algebraic comparison point, not an acceptable rank-free replacement.

The targeted literature check also considered Berge's augmenting-path
work and Dulmage–Mendelsohn's *Coverings of Bipartite Graphs*. Full access
and search limitations are recorded in `PRIOR_ART.md`. No published
rank-free reduction completing (G) was located in the material actually
checked. This does **not** establish that none exists or that Theorems 3.1
and 4.1 are novel. The elementary matching facts and source normalization
are inherited mathematics; the presentation of exposure transfer and core
separation here is a reformulation prepared in this investigation.

**Correctness status:** complete self-contained proofs of the stated
partial results, self-reviewed and supported by exact finite checks;
separately agent-reviewed and archive/code-audited, not human-refereed or
formally verified. **Conceptual usefulness:**
the source's local obstruction and the k term now have an explicit
alternating-path interpretation, with the remaining global step isolated.
**Novelty status:** unestablished. **Full target:** not proved rank-free.

Stop this bounded investigation at this outcome. The smallest remaining
mathematical task is a rank-free proof of (G), or of the sufficient (G+),
without silently treating reused H vertices as distinct resources. The public edition records the focused independent review of the partial
transfer argument and its executable checks. It is published as a qualified
partial addendum, without promoting the unresolved target or routing lead.
