# Finite-X matching/pruning theorem — Lean proof package v1.3.0

This additive edition formalizes the primary finite-X theorem in the attributed
matching-capacity pruning note. The36 proof/audit sources are unchanged from the
frozen reviewed proof archive. Preparation and review were AI-assisted.

For arbitrary finite X, arbitrary relation r, and finite original families R,C,
use the exact definitions in project/reference/PRIMARY_PRUNING_NOTE.v1.0.1.md.
Let Gamma be the tagged augmented graph, Z,H the fixed original corner sets,
and beta=min(nu(B0),nu(A0)). The named declarations prove:

    nu(Gamma) <= |Z| + beta
    min_admissible (d - q) = nu(Gamma) - |Z| <= beta

The minimum is an actual finite minimum of integer d-q values. An admissible
attaining pair also satisfies d<=beta+q. Admissibility has exactly the five
structural conditions and no budget premise. q counts DISTINCT uncovered points
of ORIGINAL Z. Loops, opposite arrows, coincident coordinate roles and empty
inputs are allowed. See project/PruningAcceptance.lean and STATEMENT_MAPPING.md.

The sharp family covers every positive size n=k+1 with |Z|=1,|H|=n*n,
beta=n and optimum=n. For EVERY real c<1 and EVERY fixed real K, one such input
violates d<=c*beta+q+K for EVERY admissible pruning, with admissible witnesses
available. See project/SharpAcceptance.lean and LocalSemanticAudit.lean.

## Attribution and scope

The source is OpenAI's openai/math at1581d4cbdd69a0faf34b2089614fe2a814316a6a:
preprints/A-proof-of-Seymours-second-neighborhood-conjecture-September-23-2026/build/source/02-pruning.tex.
The7 copied OAI modules retain their exact upstream bytes and Apache-2.0
licence. Original definitions and substantial matching/cover constructions are
inherited. The formal capacity argument uses a direct cover lift; it does not
claim to formalize the note's alternative matrix proof line by line.

This is a short structural corollary, not a novelty or priority claim. It does
not prove the full Seymour conjecture or formalize the full manuscript/note.
Excluded: arbitrary infinite ambient X, ancillary examples/alternative proofs,
Python/JSON equivalence, executable algorithm correctness and runtime bounds.
Existing Python finite tests remain supplementary software evidence.

## Reproduce

Requirements: Python3.10+, Git, and Lean4.34.1, compiler commit
5045d0056413266e57c625dcd7c365b10e377c52. Obtain that compiler from the official
leanprover/lean4 v4.34.1 distribution, or install the exact lean-toolchain with
an existing elan installation. No default-toolchain change is required.

From the repository root, first check the release manifest:

```sh
python3 -B verify_manifest.py
python3 -B lean-proof/reproduce.py --fetch --output /tmp/family173-lean-clean-1
```

Use a NEW output directory for each run. For a compiler not already on PATH,
add `--lean-bin /path/to/lean-4.34.1/bin`. Do not use Python -O. The script fetches
only the exact public Git source revisions from project/lake-manifest.json and
the pinned Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. It never
fetches binary caches and never installs or changes a global toolchain.
If exact clean pinned dependency Git trees already exist under project/.deps
and project/.lake/packages, omit --fetch for an offline run.

The source-only rebuild compiles the needed dependency closure and all36 local
modules at trust level0, with only a NEW central LEAN_PATH. It then compiles the
unchanged semantic audit and checks the exact120 Family173 axiom reports,
19 literal acceptance reports and4 semantic reports. Allowed axioms are only
propext, Classical.choice and Quot.sound. Proof-source admission/custom-axiom/
external-implementation scanning is additional evidence. A missing dependency,
wrong pin, build failure or unexpected/missing report stops the run.

Expected:1035 modules (999 external+36 local), followed by4 semantic reports
and final ACCEPTANCE.json status PASS. Per-module commands, output logs, source
hashes and object hashes are retained in the chosen output directory. A source
import graph and all9 package pins appear in BUILD_PLAN.json. A representative
macOS arm64 run took about5 minutes; allow more on other machines, disk space
for sources/objects, network for initial source fetch, and up to2 hours. The
runner reserves4GiB free disk and uses4 concurrent jobs with1 Lean thread each.
Sources need not include all Mathlib modules; only the required closure builds.

Dependency fetches modify only ignored project-local source directories.
Preserve those trees if anything differs; do not overwrite them to force a pass.
The root manifest verifies the pristine release BEFORE fetching; after local
fetches, use the recorded proof hashes/build source hashes for source identity,
or extract a fresh pristine release to repeat the root manifest check.

## Evidence and trust

review/INDEPENDENT_AI_REVIEW.json records a fresh separate-model statement
review: PASS, no unresolved objections. The reviewer did not run Lean. See
review/PROCESS.md for process and correlated-error limits. No human peer review
or OpenAI endorsement is implied. The bundled publication standard applies.

The sanitized evidence directory records complete successful build commands,
results/logs and the earlier deliberate negative controls. Build execution and
source-based statement review are separate. Kernel acceptance of a synthetic
axiom is possible; the axiom allowlist gate rejects its use in a verified claim.

Trusted base: the pinned Lean compiler/kernel and bundled Init/Lean/Std/Lake
modules, OS/hardware and file/process tooling. The compiler itself is not
bootstrapped. Mathlib/package proof dependencies in the needed closure build
from pinned sources. No external solver, native_decide or unreported target
axiom supports these named statements. Hashes establish byte identity, not
mathematical correctness or security against replacing a whole package.

The existing hosted workflow checks Python finite software regressions and
package integrity. It does not run Lean. Local clean Lean receipts and actual
hosted CI status must be reported separately.
