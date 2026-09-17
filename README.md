# Tutte's path and homotopy theorems in Lean

A Lean 4 formalization of Tutte's path theorem and the local [BJL] formulation
of Tutte's homotopy theorem, using Mathlib.

The mathematical source is **A modern perspective on Tutte's homotopy theorem**
by Matthew Baker, Tong Jin, and Oliver Lorscheid, with the homotopy-proof appendix
by Juš Kocutar. The code follows its path construction, Special Lemma, rank-four
counting and recognition argument, and final casework, with the explicit local
repairs described in [the correspondence note](docs/MANUSCRIPT_CORRESPONDENCE.md).

## Main results

| Declaration | Source file |
|---|---|
| `TutteFormalization.path_theorem` | [PathTheorem.lean](TutteFormalization/PathTheorem.lean) |
| `TutteFormalization.homotopy_theorem` | [Homotopy/Theorem.lean](TutteFormalization/Homotopy/Theorem.lean) |

Both declarations have complete proof bodies. The supplied development audit
reported successful compilation and fresh kernel replay, with transitive axioms
`propext`, `Classical.choice`, and `Quot.sound`, and no `sorryAx`.
**This publication snapshot has not yet had a fresh verification run.** Reproduce
the checks below; the original audit report is not a substitute for doing so.
The GitHub workflow is configured to run these checks, but has not run before
the repository is published. Manuscript reconciliation is a separate review task.

## Build and verify

Requirements: Git, Python 3, Bash, and [Elan / Lean](https://lean-lang.org/install/).
Run from the root of a fresh checkout:

```sh
bash scripts/verify.sh
```

The script downloads the pinned Mathlib cache, builds **both target theorems and
all bundled project modules**, runs the independent statement and axiom audits,
and replays the relevant declarations in a fresh Mathlib-only kernel environment.
It stops on a failed command and saves logs in a new `.verification-logs/` folder.
See [the verification guide](docs/VERIFICATION.md) for the individual commands
and the meaning and limits of these checks.

The exact environment is pinned:

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- Mathlib: `85e3a25e006c35636f0e53b0e9296caca2685bc0`.
- All nine dependency revisions: [lake-manifest.json](lake-manifest.json).

Do not update the toolchain or run `lake update` to reproduce this snapshot.
The historical umbrella import builds the path development only; use the explicit
homotopy import as well:

```lean
import TutteFormalization.PathTheorem
import TutteFormalization.Homotopy.Theorem
```

## What is included

All 195 project `.lean` files are preserved byte-for-byte from the final review
archive, including the independent specifications and the previously untracked
smoke test. Selected audit programs and the three version/configuration files
are also preserved exactly. [SOURCE_SNAPSHOT.json](SOURCE_SNAPSHOT.json) records
their hashes. New publication documentation and orchestration scripts are separate
from the mathematical sources.

[Proof guide](docs/PROOF_GUIDE.md) ·
[Mathematical conventions and manuscript correspondence](docs/MANUSCRIPT_CORRESPONDENCE.md) ·
[Verification](docs/VERIFICATION.md) ·
[Credits and development](docs/CREDITS.md)

Unpublished manuscript drafts, referee correspondence, private development logs,
checkpoints, conversation transcripts, and the original Git history are deliberately
not distributed here. Historical manuscript-path comments inside Lean files are
provenance notes, not build dependencies.

## Citation and release status

Citation metadata in `CITATION.cff` uses a collective project attribution.
The maintainers may refine the credited software-author list before a publication
release. The public repository is intended to be
[`mbaker386/tutte-homotopy-lean`](https://github.com/mbaker386/tutte-homotopy-lean). There is no invented DOI or release date.
When citing the work, cite the paper and the public repository, and identify the
exact public commit or release used. Do not substitute the private development
commit identifier for a public release commit.

## License

This repository's code and original accompanying documentation are licensed under
the [Apache License, Version 2.0](LICENSE). Existing source attributions are
preserved. Lean, Mathlib, and other external dependencies retain their respective
licenses; this repository does not relicense the source paper.

[Publication instructions](PUBLISHING.md) describe the one-time initial upload
from this clean snapshot, without importing private development history.
