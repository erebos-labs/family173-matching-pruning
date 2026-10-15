# Matching-capacity refinement of pair-family pruning

Version 1.0.1. Published by Erebos Labs, 14 October 2026.

Public-edition changes: version, review status and publication wording were
updated from the audited v1.0 handoff. Sections 1–9 are unchanged.

**Status:** complete ordinary mathematical proof, with exact executable regression
checks. Separate agent proof review and an independent archive/code audit found
no gap. No human referee review or Lean verification has been performed.
This is a **short structural corollary of the pinned manuscript's rank argument**,
not a new proof strategy and not a claimed proof of Seymour's conjecture.
The source construction and kernel-lift argument are due to OpenAI [OAI].
The restricted-image rank calculation, explicit transposition, objective identity,
and sharpness calculations below are the refinements recorded in this note.
No novelty or priority claim is made.

## 1. Exact scope, definitions, and theorem

Fix a finite set X, an arbitrary relation E contained in X x X, and subsets
R,C contained in X x X. Write x -> y for (x,y) in E. Loops and opposite
arrows are allowed. R and C are distinct copies, even at identical coordinates.
All cardinalities below are integers; in particular, subtraction in the
optimization objective is ordinary integer subtraction, not truncated subtraction.

An original left vertex r=(p,j) and original right vertex c=(i,s) conflict if
p -> i and s -> j. Define, from the ORIGINAL families,

\[
 Z=\{(i,j):\exists p,s,\ (p,j)\in R,\ (i,s)\in C,
                          \ p\to i,\ s\to j\},
\]
\[
 H=\{(p,s):\exists i,j,\ (p,j)\in R,\ (i,s)\in C,
                          \ p\to i,\ s\to j\}.
\]

An r=(p,j) covers z=(i,j) precisely when p -> i. An original right
c=(i,s) covers z=(i,j) precisely when s -> j. Equality of the displayed
unchanged coordinate is part of each coverage definition. There are no other
ways to cover a point.

A pruning is a pair R' subset R, C' subset C with no surviving conflict.
It is **admissible** if every original member having no original conflict is
retained. Put

\[
 d=|R\setminus R'|+|C\setminus C'|,
 \qquad q=|\{z\in Z:z\text{ is covered by neither retained family}\}|.
\]

Thus q counts DISTINCT points of the fixed original Z, not conflicts, not
multiplicities, and not two tagged copies of a point.

Let B0 be the bipartite graph with parts R,H and edges
(p,j)--(p,s) whenever s -> j. Let A0 have parts H,C and edges
(p,s)--(i,s) whenever p -> i. Let nu(G) be the maximum cardinality of a
matching in a finite bipartite graph G, and put

\[
 \beta=\min\{\nu(B_0),\nu(A_0)\}.
\]

Define Gamma with left part R disjoint-union Z_L and right part C
disjoint-union Z_R. Its edges are the original conflicts, r--z_R whenever
r covers z, and z_L--c whenever c covers z. There are no Z_L--Z_R edges.
All four tags identify separate vertices, regardless of coordinate coincidences.

**Theorem 1 (matching-capacity pruning).** For every input just defined,

\[
 \boxed{\nu(\Gamma)\le |Z|+\min\{\nu(B_0),\nu(A_0)\}.} \tag{1}
\]

Moreover, writing F for the minimum of d-q over admissible prunings,

\[
 \boxed{F=\nu(\Gamma)-|Z|\le\beta.} \tag{2}
\]

In particular there is an admissible pruning with d <= beta+q. The coefficient
1 of beta cannot be replaced by any smaller universal real constant, even if
a fixed additive constant is allowed. Both the matching bound and the pruning
objective are attained by the infinite family in Section 8.

The assumptions are exactly those in the question. In fact, the same theorem
holds for an arbitrary ambient set X when R,C are finite: restrict to the finite
set of coordinates appearing in R or C. Every point of Z,H and every relevant
arrow endpoint belongs to that finite set. No orientation, symmetry, invariance,
density, disjointness of coordinate roles, or realizability assumption is added.

If there are no conflicts, Z=H=empty and Gamma has no edges, because a member
covering a point of Z would conflict with a member witnessing that point.
Retaining everything gives d=q=beta=F=0. Empty X and empty families are included.

## 2. Two elementary matrix facts

All vector spaces in the proof are over the reals with their coordinate bases.

**Lemma 2 (support rank and minors).** If a matrix is zero outside a bipartite
support T, its rank is at most nu(T). If every allowed position is assigned a
different indeterminate, any square minor whose support has a perfect matching
is a nonzero polynomial.

*Proof.* A nonzero determinant has a nonzero term, and its positions form a
matching. This proves the upper bound for every assignment, including matrices
with repeated entries. With different indeterminates in all allowed positions,
different determinant permutations give different monomials; hence a matching
monomial cannot cancel. Equivalently, setting one maximum matching's entries
to 1 and all other allowed entries to 0 realizes the maximum support rank.
This is the determinant argument of Edmonds [E67, Section 5, Theorem 1].

**Lemma 3 (maximum-support kernel restriction).** Suppose D has maximum rank
among all real matrices supported on T. For x in ker(D), y in ker(D^T), and
an allowed position (s,j), one has x_j y_s=0.

*Proof.* Otherwise choose nonzero tau and let D_tau=D+tau e_s e_j^T.
Then D_tau x=tau x_j e_s, so e_s lies in im(D_tau). For every w,
Dw=D_tau w-tau w_j e_s also lies in im(D_tau). Therefore im(D) is contained
in im(D_tau). But y annihilates im(D) and y_s is nonzero, so e_s does not
lie in im(D). The rank increases, contradicting maximality. The perturbation
is an argument about D alone; it need not preserve any ranks of other matrices.
This is [OAI, label lem:kernel-support], reproved here.

## 3. A suitable maximum matching and four maps

Choose a maximum matching M of Gamma that minimizes the number k of original
R--C edges among maximum matchings. This choice exists because Gamma is finite.
Let alpha consist of its R--Z_R edges and delta of its Z_L--C edges; write
ell=|alpha| and t=|delta|. We use delta rather than the source's beta notation,
reserving beta for the capacity in Theorem 1. Thus

\[
 |M|=k+\ell+t. \tag{3}
\]

Both alpha and delta are maximum matchings of their respective auxiliary
subgraphs. Here is the argument, including the possible interaction with the
original matching. If alpha is not maximum, its symmetric difference with a
larger matching has an alpha-augmenting path from an alpha-unmatched R vertex
to an alpha-unmatched Z_R vertex. The latter is unmatched in M. All internal
vertices are matched by alpha. If the first endpoint is unmatched in M, flipping
this path increases |M|. Otherwise its M-edge must be original R--C: remove
that edge and flip the path. The total size is unchanged and k decreases.
Both outcomes contradict the choice of M. The symmetric-difference assertion
follows by decomposing the union of two matchings into alternating paths and
even cycles; a size surplus requires a path with one more edge of the larger
matching.

For delta, use a delta-augmenting path from a delta-unmatched Z_L vertex to a
delta-unmatched C vertex. The Z_L endpoint is unmatched in M. The C endpoint
is either unmatched in M or is incident with an original M-edge. In the former
case flip to increase |M|; in the latter remove that original edge before
flipping, preserving |M| and reducing k. This proves the claim for delta.

Let R_alpha and C_delta be the original endpoints used by alpha and delta.
The k original left endpoints of M lie outside R_alpha, and the k original
right endpoints lie outside C_delta.

For every arrow x -> y introduce TWO independent real indeterminates a_xy,b_xy.
Different arrows, including opposite arrows, receive independent variables;
the a and b arrays are independent too. Set entries to zero outside E. Define

\[
 L:\mathbb R^R\to\mathbb R^Z,\quad
 N:\mathbb R^Z\to\mathbb R^C,\quad
 B:\mathbb R^R\to\mathbb R^H,\quad
 A:\mathbb R^H\to\mathbb R^C
\]

by the following possibly nonzero entries, with all unlisted entries zero:

\[
 L_{(i,j),(p,j)}=a_{pi},\qquad N_{(i,s),(i,j)}=b_{sj},
\]
\[
 B_{(p,s),(p,j)}=b_{sj},\qquad A_{(i,s),(p,s)}=a_{pi}. \tag{4}
\]

For column (p,j) in R and row (i,s) in C, the only possible intermediate
index for NL is (i,j), and the only possible one for AB is (p,s). When the
endpoints conflict, both intermediates belong to the required sets by definition,
and both entries equal a_pi b_sj. When they do not conflict, at least one factor
is zero in both products. Consequently, for every assignment,

\[
 NL=AB. \tag{5}
\]

This checks all support restrictions, including intermediate indices absent
from Z or H. It does not assume a full Cartesian product of coordinate sets.

## 4. The simultaneous choice and the shared-variable issue

We require one assignment at which (i) rank L=ell, with its R_alpha columns
forming an image basis, (ii) rank N^T=t, with its C_delta columns forming an
image basis, and (iii) certain smaller b-matrices attain their maximum support
ranks. We now prove this assignment exists.

Take the L minor whose rows and columns are the endpoints of alpha.
It is block diagonal by j: each block has equal numbers of selected rows and
columns because alpha matches inside that j-block. Within a fixed j-block,
the entry at row (i,j), column (p,j) is the distinct variable a_pi whenever
allowed. R is a set, so there are no repeated columns with the same p,j;
Z is a set, so there are no repeated rows with the same i,j. Lemma 2 shows
each block determinant is a nonzero polynomial. Their product is nonzero.
Variables can repeat ACROSS blocks; this causes no problem because a polynomial
ring over the reals has no zero divisors. The alpha minor therefore need not
have globally distinct variables to be a nonzero polynomial.

The same reasoning for N^T uses blocks with fixed i, rows (i,j), columns
(i,s), and distinct b_sj variables within each block. Its delta minor is also
a nonzero polynomial. By Lemma 2 and auxiliary maximality, every assignment
has rank L <= ell and rank N^T <= t. Thus nonvanishing of these two minors
forces both ranks and both asserted image-basis properties.

For every arrow p -> i define

\[
 J_p=\{j:(p,j)\in R\},\quad S_i=\{s:(i,s)\in C\},\quad
 D^{p,i}=(b_{sj})_{s\in S_i,\ j\in J_p}.
\]

Its support is T^{p,i}={(s,j) in S_i x J_p : s -> j}. The allowed entries
of each individual matrix D^{p,i} are distinct indeterminates. Choose one
minor of size nu(T^{p,i}) supported on a maximum matching. By Lemma 2 its
determinant is nonzero as a polynomial, and its nonvanishing forces maximum
support rank. If this rank is zero, choose the empty determinant 1.

Multiply all these finitely many minor polynomials and the two auxiliary
matching minors. The product is nonzero in the SINGLE polynomial ring on all
a,b variables. Sharing a b variable among several D^{p,i} and N-blocks does
not identify two distinct variables WITHIN any one of the required blocks,
and does not turn a product of nonzero polynomials into zero.

A nonzero polynomial on finitely many real variables has an evaluation that
is nonzero. For completeness, induct on the number of variables. Regard it
as a polynomial in the last variable. At least one coefficient is a nonzero
polynomial in the earlier variables; choose an evaluation making that
coefficient nonzero by induction. The resulting nonzero univariate polynomial
has finitely many roots, so choose the last coordinate outside them.
Fix such an assignment for the rest of Sections 5 and 6.

We do NOT assert unrestricted generic rank equals matching number for every
shared-variable matrix. In particular, no equality rank(B)=nu(B0), and no
simultaneous rank-maximization condition on B or A, is needed. Only the universal
support upper bound from Lemma 2 will be used for B.

## 5. Rechecking the kernel lifts and their independence

The basis properties yield, for every original matched edge (r,c), vectors

\[
 u^r=e_r+\sum_{a\in R_\alpha}\lambda_a^r e_a\in\ker L,
 \qquad
 v^c=e_c+\sum_{b\in C_\delta}\mu_b^c e_b\in\ker N^{\mathsf T}.
 \tag{6}
\]

Indeed, express the corresponding column as a combination of the basis
columns and subtract that combination. Restricted to the k original left
endpoints, the u^r are the corresponding unit vectors; also v^c_c=1.

The following restriction holds for ALL u in ker B and ALL v in ker N^T:

\[
 u_{pj}v_{is}=0\quad\text{whenever }((p,j),(i,s))\text{ is a conflict}. \tag{7}
\]

To prove it, fix p -> i. The restriction (u_pj) over j in J_p is in
ker D^{p,i}. For a row s in S_i having an allowed entry, there is some
j in J_p with s -> j, and hence a conflict witnessing (p,s) in H.
The equation (Bu)_(p,s)=0 is exactly

\[
 \sum_{j\in J_p}b_{sj}u_{pj}=0.
\]

For a row having no allowed entry this equation holds because every coefficient
is zero, including when its (p,s) coordinate is absent from H. Thus EVERY row
of D^{p,i} annihilates the restricted vector.

Similarly, the restriction (v_is) over s in S_i lies in ker (D^{p,i})^T.
A column j with an allowed entry has some s in S_i with s -> j, so (i,j)
belongs to Z. The equation (N^T v)_(i,j)=0 is exactly

\[
 \sum_{s\in S_i}b_{sj}v_{is}=0.
\]

A column without allowed entries satisfies this equation automatically.
Apply Lemma 3 to this maximum-support-rank D^{p,i}. This gives (7) on every
allowed (s,j), which is precisely every conflict for the fixed p,i.

For an original matched edge (r,c), substitute v=v^c in (7). Since v^c_c=1,
EVERY u in ker B has u_r=0. If a linear combination sum_r theta_r Bu^r
vanishes, then u=sum_r theta_r u^r lies in ker B. Its r coordinate at each
original matched left endpoint is theta_r by (6), so all theta_r vanish.
Therefore the k vectors Bu^r are independent. Furthermore,

\[
 A(Bu^r)=NLu^r=0.
\]

The key conclusion, retaining more information than the source's displayed
ambient-kernel count, is

\[
 \boxed{\dim(\operatorname{im}B\cap\ker A)\ge k.} \tag{8}
\]

All of Sections 3 through 5 reconstruct the source argument [OAI]; its output
vectors visibly lie in im B, which supplies the refinement in the next section.

## 6. Restricted-image rank and the exact transposition

Restrict A to im B. The image of that restriction is im(AB), and its kernel
is im B intersect ker A. Rank-nullity gives the IDENTITY

\[
 \operatorname{rank}B
 =\dim(\operatorname{im}B\cap\ker A)+\operatorname{rank}(AB)
 \ge k+\operatorname{rank}(NL). \tag{9}
\]

Also, by rank-nullity for N restricted to im L,

\[
 \operatorname{rank}(NL)
 =\ell-\dim(\operatorname{im}L\cap\ker N)
 \ge\ell-(|Z|-t). \tag{10}
\]

The matrix B is supported on the transpose of the incidence support of B0.
A nonzero minor supplies a matching in B0, irrespective of repeated b entries,
so rank B <= nu(B0) by Lemma 2. Combining (3), (9), and (10) yields

\[
 \nu(\Gamma)=k+\ell+t\le |Z|+\operatorname{rank}B
                         \le |Z|+\nu(B_0). \tag{11}
\]

The replacement of ambient dimension |H| by rank B in (9) is the short
structural improvement. The source already provides the independent lifts
needed for it.

We now obtain the A0 bound WITHOUT assuming symmetry of the relation.
Let tau(x,y)=(y,x), keep the SAME arrow relation, and define a new input

\[
 R^*=\tau(C)=\{(s,i):(i,s)\in C\},\qquad
 C^*=\tau(R)=\{(j,p):(p,j)\in R\}. \tag{12}
\]

A transformed pair (s,i) in R* and (j,p) in C* conflicts precisely when
s -> j and p -> i, the original two conditions in exchanged order. Thus

\[
 Z^*=\tau(Z),\qquad H^*=\tau(H).
\]

The isomorphism from Gamma to Gamma* exchanges bipartition sides and maps
original R_(p,j) to C*_(j,p), original C_(i,s) to R*_(s,i),
Z_L,(i,j) to Z*_R,(j,i), and Z_R,(i,j) to Z*_L,(j,i).
For coverage, original r covering (i,j) means p -> i, exactly the condition
that transformed c*=(j,p) covers (j,i). Original c covering (i,j) means
s -> j, exactly the condition that transformed r*=(s,i) covers (j,i).
So ALL three types of edges, and absence of Z--Z edges, are preserved.
In particular nu(Gamma*)=nu(Gamma) and |Z*|=|Z|.

Finally, an edge of B0* is

\[
 (s,i)\in R^*\quad--\quad(s,p)\in H^*
 \qquad\text{iff }p\to i.
\]

Under the displayed coordinate maps this is exactly an A0 edge from
(p,s) in H to (i,s) in C, with its bipartition reversed. Hence
nu(B0*)=nu(A0). Applying (11) to the starred input proves
nu(Gamma) <= |Z|+nu(A0), and taking the minimum gives (1).

For clarity at matrix level, after reindexing and formally setting a*=b,
b*=a, the maps satisfy

\[
 L^*=N^{\mathsf T},\quad N^*=L^{\mathsf T},\quad
 B^*=A^{\mathsf T},\quad A^*=B^{\mathsf T}.
\]

This is NOT reversal of the arrow relation. The application of (11) to the
starred input may use its own generic coefficient assignment. No assertion
that the earlier chosen assignment already satisfies the starred D-matrix
conditions is needed.

## 7. From matching to admissible pruning, and the exact objective

We first give the needed matching-cover argument, so the deduction is
self-contained rather than reliant on a black-box optimization theorem.
In a finite bipartite graph with a maximum matching M, start at all unmatched
left vertices. Traverse nonmatching edges left to right, and matching edges
right to left. Let W_L,W_R be the reached sets. No unmatched right vertex
is reached, as that would give an augmenting path. On each matching edge,
either both endpoints are reached or neither is: a reached right vertex
leads to its mate; a matched reached left vertex must have been entered
from its mate. Therefore

\[
 K=(V_L\setminus W_L)\cup W_R
\]

is a vertex cover: an edge from a reached left vertex to an unreached right
vertex is impossible, by either the traversal rule or the matching observation.
The cover includes exactly one endpoint of each matched edge, and no unmatched
vertices. Thus |K|=|M|. Conversely every cover has size at least every matching,
because distinct matching edges need distinct covering vertices. This proves
the finite bipartite matching-cover equality used here, classically due to
Kőnig [K31]. In particular this K is minimum and omits isolated vertices.

An initially conflict-free original left member is isolated in Gamma. To see
this, if (p,j) covered (i,j) in Z, a witness for that point provides an
original C member (i,s) with s -> j, which conflicts with (p,j).
For an initially conflict-free right member (i,s), coverage of (i,j) in Z
provides an original R witness (p,j) with p -> i, again producing a conflict.
Thus it has no auxiliary edge either. These arguments use original witnesses,
not assumptions about retained families.

Use the minimum cover K of Gamma just constructed and delete its original
vertices. Every original conflict is hit, and initially conflict-free members
are retained because they are isolated. If q points of the original Z are
uncovered, each of the |Z|-q covered points has a retained adjacent original
vertex, forcing its opposite tagged point-copy into K. These are distinct
vertices for distinct points. Hence

\[
 d\le |K|-(|Z|-q)=\nu(\Gamma)-|Z|+q\le\beta+q. \tag{13}
\]

This proves the requested pruning conclusion with the exact uncovered-point
counting and preservation condition.

There is also a converse charge, giving the exact minimum. For ANY
conflict-free retained R',C', a point z=(i,j) cannot be covered by both sides:
a retained (p,j) with p -> i and retained (i,s) with s -> j would conflict.
Form a canonical cover by taking the deleted original vertices and, for each
covered point, its Z_R copy if covered on the left or its Z_L copy if covered
on the right. Add neither copy for an uncovered point. This covers the original
conflicts and every auxiliary edge. Since no point is covered on both sides,
the cover size is EXACTLY

\[
 d+|Z|-q.
\]

Every matching is no larger than this cover, so every admissible pruning
satisfies d-q >= nu(Gamma)-|Z|. The pruning from (13) gives the reverse
inequality. The minimum exists (there are finitely many subfamilies), and
we obtain (2).

In particular, equality in Gamma's bound for a fixed input is equivalent to
the optimum deletion-minus-uncovered objective equaling beta. This equivalence
requires the converse-cover argument; it would not follow from the source's
one-directional cover charge alone. It concerns d-q, not minimum d by itself.

## 8. Infinite strict improvement and separate sharpness checks

For each integer n>=1, take distinct symbols

\[
 X_n=\{i,j,p_1,\ldots,p_n,s_1,\ldots,s_n\}.
\]

Let the ONLY arrows be p_a -> i and s_b -> j, for all a,b in {1,...,n}.
Set

\[
 R_n=\{r_a=(p_a,j):1\le a\le n\},\quad
 C_n=\{c_b=(i,s_b):1\le b\le n\}.
\]

These inputs are loopless, have no opposite pairs, and are even acyclic.
This is an example family, not a restriction in the theorem. Every r_a
conflicts with every c_b, so

\[
 Z_n=\{(i,j)\},\qquad H_n=\{(p_a,s_b):1\le a,b\le n\}.
\]

B0 consists of n disjoint stars with centres r_a and leaves (p_a,s_b).
The n edges r_a--(p_a,s_1) give a matching; all R_n vertices give a cover
of size n. Thus nu(B0)=n. For A0 the n edges (p_1,s_b)--c_b form a
matching, and all C_n vertices cover its edges, so nu(A0)=n. Consequently

\[
 |H_n|=n^2,\qquad \beta_n=n.
\]

For n>=2 the budget improves strictly; its additive improvement n^2-n and
its ratio |H_n|/beta_n=n are both unbounded.

**Sharpness of Gamma's bound.** Gamma has n+1 vertices in each part.
A matching of size n+1 is

\[
 \{r_1z_R,z_Lc_1\}\ \cup\ \{r_ac_a:2\le a\le n\}.
\]

All left vertices give a cover of the same size. Hence
nu(Gamma)=n+1=|Z|+beta, with matching and cover shown explicitly.

**Sharpness of the deletion objective, checked directly.** A conflict-free
pruning cannot retain a member of both original sides. If at least one member
survives, it covers the unique Z point, so q=0 and d>=n. If no member survives,
then d=2n,q=1, giving d-q=2n-1>=n. Retaining all of one side and deleting
the other gives d=n,q=0. Thus the actual minimum of d-q is n=beta.
This argument is independent of the objective identity and of the matching
calculation above.

For any real c<1, the proposed universal replacement d<=c beta+q fails on
these examples. More strongly, a universal bound d<=c beta+q+K with fixed
finite K fails for n sufficiently large, since it would require n<=cn+K.
Thus the coefficient 1 is optimal in the stated uniform sense.

The rectangular version with m left and n right originals has |H|=mn,
nu(B0)=m, nu(A0)=n, beta=min(m,n), and nu(Gamma)=1+min(m,n).
Certificates for (m,n)=(1,5),(5,1), and the explicit transpose are included
to test the nonsymmetric capacities rather than only the balanced example.

## 9. Why q must not be altered

A second family guards against replacing q with a clipped or multiplicity-based
quantity. Take distinct p,s,i_1,...,i_n,j_1,...,j_n, arrows p -> i_a and
s -> j_b only, R={(p,j_b)}, C={(i_a,s)}. Then H={(p,s)}, |Z|=n^2,
nu(B0)=nu(A0)=1, and nu(Gamma)=2n. For the latter, match every original R
vertex to its own distinct Z_R point and every original C vertex to its own
distinct Z_L point; all 2n original vertices form an equal-size cover.

Deleting everything yields d=2n and q=n^2. By (2), this attains the true
minimum 2n-n^2. The minimum is negative for n>=3. In particular, the objective
must not be silently replaced by max(0,d-q), and q must remain the number of
uncovered ORIGINAL Z points. The n=2,3,4 cases are in the regression files.

## 10. Dependencies, attribution, audit scope, and reproducibility

The general proof uses only finite matching arguments, determinant expansion,
nonvanishing of finite products of nonzero real polynomials, and finite-dimensional
rank-nullity. Lemmas 2 and 3, the generic block construction, the kernel lifts,
and the alternating-path cover construction are explicitly proved here. No
Seymour theorem, Lean theorem, numerical calculation, or finite enumeration is
a premise of Theorem 1.

[OAI] OpenAI, *A proof of Seymour's second-neighborhood conjecture*, dated
23 September 2026, openai/math commit
1581d4cbdd69a0faf34b2089614fe2a814316a6a,
`preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/02-pruning.tex`.
Precise source locators are `lem:pruning`, `lem:kernel-support`,
`eq:pruning-commute`, `eq:conflict-kernel`, `eq:pruning-lifts`,
`eq:pruning-rank-bound`, and `eq:cover-charge`.
The source proves the |H| budget. Its independent images Bu^r immediately
support (8), and (9) is the short refinement. The exact source is bundled
unchanged with its original Apache-2.0 license. Its Git blob SHA-1 and SHA-256
are verified in `provenance/SOURCE_HASHES.json`.

[E67] Jack Edmonds, *Systems of distinct representatives and linear algebra*,
Journal of Research of the National Bureau of Standards, Section B, 71B(4)
(1967), 241-245, DOI 10.6028/jres.071B.033. Section 5, Theorem 1, p. 242,
was checked in the original NIST-hosted article. Its distinct-indeterminate
hypothesis is respected blockwise, rather than assumed for a globally
shared-variable matrix.

[K31] Denes Konig, *Graphok es matrixok*, Matematikai es Fizikai Lapok 38
(1931), 116-119. The Hungarian Academy's volume record and the source's
bibliographic entry were consulted. The 95 MB full-volume scan was not read
in this bounded audit. Section 7 above supplies the entire needed proof,
so no unexamined historical proof step is a dependency.

The pinned source was independently retrieved on 14 October 2026 and exactly
matched the supplied snapshot. Its Git blob is
4fe3b01285d67d6fb5a5e7a8798a3c12f432ff76. This public edition makes no
claim about future upstream revisions or all derivative work. Related
primary-source locations and the preparation read scopes are retained in
provenance/PRIMARY_SOURCES.json. The bounded prior-art search establishes
neither novelty nor priority.

The accompanying standard-library Python constructor reconstructs all objects
from relation,R,C and constructs maximum matching/minimum cover certificates
for Gamma,B0,A0 and an objective-optimal pruning. The verifier does not import
the constructor or a matching library. It reconstructs the objects separately,
checks the exact finite certificates, and can independently enumerate retained
subfamilies against the original definitions. All tests are regression evidence,
not a proof for arbitrary X. See `STATUS.md`, `logs/`, `audit/REVIEW.md` and `README.md` for fresh
runs and commands. The initial handoff was self-reviewed; the public edition
also has separate agent proof review and an independent implementation audit.
These are AI-assisted reviews, not independent human referee review.

The investigation ends with this bounded refinement. The main Seymour claim,
its other manuscript sections, downstream applications, and Lean dependencies
have not been audited or extended here.
