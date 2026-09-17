# Reproducing the checks

## Current evidence

The final development archive records successful target builds, independent
statement checks, a semantic axiom audit, and a fresh kernel replay of 1,835
declarations for the homotopy development (including supporting declarations).
The path-only replay records 170 declarations. These are historical run results,
not claims that the publication package has already been rerun on your machine
or on GitHub. The publication preparation checked source hashes and local import
coverage but did not execute Lean.

## Recommended procedure

Extract or clone into a new directory, without copying an old `.lake/` build tree.
Install Elan using the official Lean setup instructions, then run:

```sh
bash scripts/verify.sh
```

Network access is required for the pinned Lean and dependency downloads and
Mathlib's compiled cache. No authentication token is required for the mathematical
checks. Resource or download failures are not mathematical disproofs.

The script first checks `SOURCE_SNAPSHOT.json`, verifies the expected Lean version,
fetches the Mathlib cache, checks dependency commit identities and cleanliness,
builds every bundled project module, and runs these audit programs:

```sh
lake env lean audit/StatementAudit.lean
lake env lean Audit.lean
lake env lean homotopy/audit/StatementAudit.lean
lake env lean homotopy/audit/SemanticsAudit.lean
lake env lean audit/KernelReplay.lean
lake env lean homotopy/audit/FinalKernelReplay.lean
```

The script checks that both public theorem axiom reports appear and contain only
`propext`, `Classical.choice`, and `Quot.sound`. The specifications are independently
written propositions, not types inferred from the theorem declarations.

The replay programs use Lean's kernel replay facility with a fresh Mathlib-only
starting environment. They reject new project axioms and unsafe/partial
declarations. This is replay through Lean's kernel, not a separately implemented
kernel, and Mathlib remains the trusted starting environment. Replay writes two
new dependency-graph JSON files under `audit/` and `homotopy/audit/`; these generated
files are ignored by Git.

The same scripts run in `.github/workflows/verify.yml`, on pushes and pull requests.
The workflow grants only read access to repository contents, does not publish,
does not update dependency pins, and does not enable automatic pull-request approval.
The workflow's public-runner build has not yet been exercised at package creation.

## Source fidelity is a different question

A successful run checks the formal declarations in this snapshot. It does not
certify that every sentence of a prose manuscript expresses the same argument.
See `MANUSCRIPT_CORRESPONDENCE.md` for the recorded differences and limitations.

Private historical baseline checkers are not bundled: they depend on draft source
files, old Git commits, and checkpoints deliberately excluded from this publication.
The publication source-hash checker has a new name and a precisely stated narrower
scope; it is not a rewritten historical audit.

## Future revisions

Do not casually regenerate `SOURCE_SNAPSHOT.json` to make a failed check pass.
A legitimate mathematical change needs a reviewed new snapshot and an explicit
new provenance record. Changes to publication metadata alone do not alter the
mathematical-source hash list.

## Official references

- https://lean-lang.org/doc/reference/latest/ValidatingProofs/
- https://lean-lang.org/install/
- https://github.com/leanprover/lean-action
