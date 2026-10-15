# Erebos Labs mathematical research publication standard

Version: 1.0 • 15 October 2026 • Asia/Singapore (UTC+08:00)

Status: Adopted publication standard and retrospective audit baseline. Published 15 October 2026 after owner approval.

This baseline is adopted under the user’s delegated authority to choose, save and apply a reasonable standard. Local audits and safe local remediation are authorized now. No additional approval gate applies to those local actions. This standard was adopted internally before publication and does not imply historical compliance. PASS, CONDITIONAL and BLOCKED are evidence dispositions, not authorization to publish. External effects require separate applicable authorization; high-impact public corrections and releases require approval of their exact content.

## Purpose and immediate priority

Erebos Labs is a hobby, AI-assisted research project. Its claims must be limited to what the released evidence supports. Publication is not a guarantee of correctness, novelty, peer review, or formal verification.

Before beginning new research, inventory every previous public release and its associated paper, code, release notes, website claims and announcement posts. Audit each against this standard. Resolve every material issue by a supported correction, an explicit reduction of the claim, or withdrawal. Publish a disposition for every release. A backlog entry or a promise to check later does not close the audit. Work needed to review or repair prior releases may continue during this pause.

## 1. Precise claims first

Give every principal claim a stable identifier. State its definitions, quantifiers, domain, hypotheses, boundary and degenerate cases, conclusion and exact scope. Distinguish:

- A general theorem from a bounded or finite result
- A new proof from a new theorem, implementation, example, reformulation or exposition
- A conditional implication from verification that its premises hold in the intended application
- A formalized lemma from a formalized complete argument
- A search that found no counterexample from proof that none exists

Record dependencies in a claim-to-evidence map. Every proof-critical dependency must have a proof, a precisely cited applicable theorem, or an explicit mathematical hypothesis. An unresolved conjecture used as a hypothesis must remain visible in the headline and statement. Do not present the resulting conditional theorem as an unconditional solution.

## 2. Evidence routes and their meanings

These routes can be combined. None automatically establishes novelty, relevance or the fidelity of the stated claim.

### A. Ordinary mathematical proof

A complete, readable argument covering every claimed case is a legitimate proof route. Lean is not universally required. Review must check each substantive inference, cited result and its hypotheses; reductions, existence and uniqueness claims; limiting operations; exceptional cases; and whether any step assumes the result. Numerical agreement is supplementary evidence, not a missing proof step.

A novel general proof requires substantive independent review before being released with the status “reviewed proof.” Until then, it may only be described as a proposed proof under review. A report must identify the claim and version reviewed, checks performed, unresolved objections and reviewer identity or disclosed review process. AI review must be labelled as AI review; it must not be advertised as human peer review or journal acceptance.

### B. Formal verification

“Formally verified” applies only to named statements that the released formal artifacts actually establish. For each such claim:

1. Map the prose statement and definitions to the exact formal declarations, including hypotheses and quantifiers. Independently review this mapping.
2. Check that the intended cases inhabit the domain and satisfy the hypotheses. Look for contradictory assumptions, empty domains, unintended restrictions and definitions that encode the desired conclusion. Use witnesses or a documented mathematical argument where applicable; do not claim to have mechanically established global consistency.
3. Rebuild the exact pinned source and dependencies from a clean environment. Record toolchain, library versions, commands and complete results. A cached binary or a green badge alone is insufficient.
4. Audit transitive axiom dependencies for every headline declaration. No `sorry`, `admit`, `sorryAx`, undisclosed custom axiom or other proof placeholder may support a “verified” claim. Declared mathematical premises are acceptable only when the public claim is explicitly conditional on them.
5. State the trusted computing base, including proof kernel, relevant tooling, native computation, external solver or checker assumptions. Distinguish kernel-checked proof terms from trusted computational evaluation. Document the actual pinned version rather than assuming all versions behave identically.
6. Explain every nonstandard axiom and why it is acceptable for the precise claim. Standard logical axioms are not automatically defects. A new axiom asserting an unproved target does not verify that target.

Lean documents axiom tracking and the hazards of inconsistent additional axioms in its [axiom reference](https://lean-lang.org/doc/reference/latest/Axioms/). Its [proof validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/) explains validation and trust considerations. These sources inform this checklist; the release must record its own toolchain-specific evidence.

### C. Exhaustive finite verification and certificates

A complete finite computation can establish a precisely bounded result, with its computational trust assumptions disclosed. It cannot alone prove a claim outside that finite scope.

- Define the exact finite domain, encoding, bounds, equivalence relation, expected case counts and exclusions
- Justify completeness of enumeration and every symmetry reduction or pruning rule; checking the output list does not by itself prove all required cases were generated
- Publish the proof-critical inputs, certificates, checker source and expected outputs with hashes. If generation is expensive, cheap certificate verification should be available where feasible
- Use an independently implemented checker against the mathematical specification, not a renamed copy of the generator's decision logic. Identify shared libraries and assumptions
- Reproduce the check in a clean environment. Record failures, timeouts, skipped cases and resource limits; none may silently count as success
- Include deliberately invalid, missing, duplicated, truncated and altered certificates/cases as applicable. Show that the checker rejects the relevant corruptions; mutation tests strengthen confidence but do not prove checker soundness
- Prefer exact arithmetic. Floating-point computations require a rigorous error enclosure and argument if they form part of the proof; otherwise label them numerical experiments

For a universal theorem reduced to finite verification, the reduction is itself proof-critical and requires the ordinary-proof or formal-proof checks above.

### D. Numerical experiments and heuristics

Publish these as experiments, observations or conjecture support. State algorithms, precision, tolerances, seeds, sampling, parameter ranges, stopping criteria and negative results. Separate exact and approximate arithmetic. Explain possible instability and selection effects. Successful trials or absent counterexamples are not proof, however many were run.

## 3. Independent means a separate check, not another success message

Independence has several dimensions and must be described rather than implied:

- **Review independence:** a reviewer who did not construct the argument examines it substantively and is free to reject it. They work from the frozen claim, source evidence and mathematical definitions, and supply their own objections and conclusions
- **Implementation independence:** a checker or derivation is separately constructed from the specification without copying the proof-critical implementation being checked. Shared dependencies and correlated failure risks remain disclosed
- **Execution independence:** another clean run checks reproducibility of the released artifacts. This is useful but does not establish either of the preceding forms of independence

The same agent replaying its own reasoning or rerunning its own code is self-checking. A fresh AI session can supply a separate critical review, but shared model training and similar reasoning can cause correlated errors; label it “independent AI review,” with the model/process and limitations stated. Multiple agreeing agents are not a proof. For unusually consequential or extraordinary mathematical claims, obtain relevant human expert review before promotional claims of a breakthrough or a settled open problem.

Independent review is mandatory for novel general proofs and for the prose-to-formal statement mapping supporting those proofs. The standard does not require paid peer review or Lean for every hobby note. If the required review is unavailable, retain the proposed-proof status.

## 4. Reproducibility, public artifacts and provenance

Every release must include:

- A fixed source revision, versioned paper and immutable artifact checksums
- A minimal README with precise reproduction commands, supported environment, dependencies, expected outputs, estimated resources and known limitations
- Clean-run logs covering the proof-critical path; optional demonstrations must be identified separately
- Public access to proof-critical material. A private certificate or inaccessible dependency cannot support the claim “publicly reproducible.” If lawful publication is impossible, narrow the public claim or withhold it
- Explicit rights and reuse terms for original code, text and data, with compatible third-party notices and provenance. Reserved rights are permitted when clearly disclosed; this standard does not require an open-source or permissive reuse license. Publication rights must still be held or lawfully obtained, and third-party limits must be respected. A public repository alone is not a license. Do not describe reserved-rights material as open source.
- Source attribution, AI-assistance disclosure and a record of which tasks were AI-assisted. Do not disclose private prompts, credentials or personal material merely to demonstrate transparency
- A privacy and secret scan appropriate to the artifact, plus review for accidental disclosure of private research, account details or third-party material

Keep a dated literature-search note: sources searched, relevant prior work, terminology variants, nearest results and actual differences. Verify cited sources and theorem hypotheses. An unsuccessful search supports “we have not found prior work as of this date,” not an absolute first-ever claim. Correctness and novelty are separate audit questions.

## 5. Public evidence and status labels

Use separate fields for evidence status, release-gate evidence disposition, and publication authorization. Do not use uncalibrated confidence percentages.

Evidence status, per claim:

- **Experiment:** empirical or heuristic evidence; no proof asserted
- **Conjecture:** a precise unproved statement
- **Proposed proof, under review:** an argument exists, but required review is incomplete
- **Reviewed ordinary proof:** complete argument and documented independent substantive review
- **Finite verified result:** exact stated finite scope, completeness justification and independent certificate/checker review completed
- **Formally verified statement:** named formal statements, fidelity review, clean build and disclosed axiom/trust audit completed
- **Corrected / superseded / withdrawn:** links to the replacement or explanation, preserving the previous record

A release can contain several statuses. A formalized background lemma does not upgrade a new unformalized theorem. “Verified” must always specify what was verified, by what method and under which assumptions.

## 6. Exact release gate

Evaluate the exact proposed public wording against each applicable requirement. Mark every check satisfied, not applicable with a reason, or unresolved. Do not average checks into a score.

### PASS

All mandatory checks for the stated scope and evidence category are satisfied; no unresolved material objection remains; the manifest, artifacts and public wording agree. PASS records that the exact wording and limitations meet the evidence requirements. It does not authorize publication, upload, push, external contact, or any other external effect. Publication authorization must be recorded separately and must apply to the exact content, destination and material state. It does not certify absolute correctness or novelty. A properly documented experiment may PASS as an experiment without being a theorem.

### CONDITIONAL

There is no known falsehood or unsafe disclosure in the proposed public wording, but some verification requirement for a stronger claim is unmet or a nonmaterial packaging issue remains. The manifest states the exact limitation, permitted wording, required corrective action and owner. Publication, if chosen, must use the limited status prominently, such as “proposed proof, independent review pending.” A conditional decision never authorizes asserting an unproved theorem, “formally verified” without the formal checks, or “exhaustive” with missing coverage.

If limitations are fully addressed by a narrower release and all requirements for that narrower category are satisfied, reevaluate it as PASS for that category. Do not leave the stronger claim in the title, abstract, README or promotional posts.

### BLOCKED

Any material claim is false or unsupported at the stated strength; a proof-critical gap, counterexample, statement mismatch, missing certificate, unexplained axiom/admission, incomplete coverage or unresolved substantive objection remains; or publication would violate privacy, permissions or artifact licensing. Do not publish or promote the affected claim at that strength. Repair, reduce the claim and re-audit, or withdraw it. A correction or withdrawal notice may be prepared after its factual wording is checked. Publication requires separate applicable authorization, including exact-content approval for a high-impact public correction.

The release decision is the most restrictive decision among its included headline claims and cross-cutting publication checks. Excluded or explicitly withdrawn claims must not remain implied by the rest of the release. Every decision names its assessor, date, standard version, source revision and evidence links.

## 7. Corrections and withdrawals

When a credible error appears, stop promoting the affected claim and assess its scope promptly. If unresolved and material, add a visible under-review notice. Do not wait for a complete replacement proof to warn readers about a known unsupported claim.

For a correction, state what was wrong, affected versions and claims, what changes, what remains supported, and the new evidence. Issue a new version; link old and new records in both directions where possible. Update the paper, repository, release notes, website and reachable announcements so the strongest visible claim matches the evidence.

Withdraw when the main claim is false, materially unsupported, or cannot responsibly be repaired. Preserve a dated withdrawal notice and the scholarly record where lawful and safe. Do not silently rewrite history, overwrite release assets or retag a different commit as though it were the old release. Remove secrets or unlawfully disclosed material when necessary, with a safe explanatory notice; archival fidelity does not justify keeping harmful disclosures public.

A withdrawn item with a clear public disposition can close the historical audit. It does not become a supported theorem. Novelty corrections should credit prior work even if the mathematics remains correct.

## 8. Historical-audit completion rule

Maintain an inventory of known public releases, version histories and associated claims, with the search scope and any inaccessible sources documented. For each release record its original wording, present evidence, missing checks, assessment, remedy and public correction links.

The pause on new research ends only when every inventoried release has a completed, documented disposition and all material public overclaims have been corrected, narrowed or withdrawn. A release still awaiting necessary verification must have an honest public under-review or proposed-proof status; this is a remediation outcome, not verification. Unresolved public overclaims keep the pause in effect. The owner explicitly acknowledges that the inventory and remediation pass are complete before new research resumes.

## 9. Per-release verification manifest template

- Release title, date and version:
- Standard version:
- Immutable source revision and artifact hashes:
- Paper / repository / release / announcement URLs:
- Claim identifiers, exact statements, scope and hypotheses:
- Novelty classification and dated prior-work search:
- Evidence status for each claim:
- Proof and dependency map:
- Independent reviewer, role, type of independence, method and report:
- AI assistance and review limitations:
- Formal declaration mapping, toolchain, axiom report and trusted base, if applicable:
- Finite-domain coverage, reduction arguments, checker independence and mutation tests, if applicable:
- Experimental design and numerical limitations, if applicable:
- Clean reproduction commands, logs and expected results:
- Public artifact availability, licenses, provenance and privacy checks:
- Known limitations, objections and excluded claims:
- Gate: PASS / CONDITIONAL / BLOCKED, with reasons:
- Exact assessed public wording and prohibited stronger interpretations:
- Separate publication authorization, approved content/destination/state, or explicitly not authorized:
- Assessor and assessment date:
- Required next actions and owner, if any:
- Corrections, superseded versions and withdrawal links:

## Adoption and publication

This version is adopted internally on 15 October 2026 in Asia/Singapore under the user’s delegated standard-selection and retrospective audit/remediation instruction. Apply it now to local audit and safe remediation, with a linked, claim-indexed manifest for every release. Apply it retrospectively without implying that old work had already met it.

This policy and the accompanying retrospective review are published on 15 October 2026 after owner approval. Public summaries must distinguish completed checks from pending ones. No internal evidence disposition itself grants publication authority. Keep the standard proportionate: complete proof and honest scope are mandatory, while formalization is required only when claimed or needed by the selected evidence route.
