# Navigating the development

The namespace is `TutteFormalization`; homotopy-specific declarations generally
use its `Homotopy` namespace. Module names are not separate theorem assumptions.

| Mathematical role | Principal source |
|---|---|
| Shared matroid, cut, and path definitions | `TutteFormalization/Definitions.lean` |
| Rank-based connectivity background | `SeparationRank.lean`, `ConnectedPartitions.lean`, `Separation.lean` |
| Structural flat results | `RelativeComplement.lean`, `IndecomposableStep.lean`, `Chain.lean`, `Diamond.lean`, `IndecomposableComplement.lean` |
| Path induction and public theorem | `PathInduction.lean`, `PathTheorem.lean` |
| Independent path statement | `PathStatement.lean` |
| Finite models and upper-sublattice embedding | `Homotopy/FiniteModels.lean`, `ModelGeometry.lean`, `GraphicModel.lean`, `Embedding.lean` |
| Allowed elementary loops and finite homotopy | `Homotopy/Elementary.lean`, `Deformation.lean` |
| Corrected preliminary separation argument | `Homotopy/B2Separation.lean` |
| Higher-corank special-path reduction | `Homotopy/LargeSpecial.lean` |
| Rank-four counting | `Homotopy/CountingFrame.lean`, `CountingPencils.lean`, `CountingPigeonhole.lean`, `PencilCounts.lean` |
| Fourth-kind lattice, cut, and path recognition | `Homotopy/FourthRecognition.lean`, `FourthSpecial.lean` |
| Completed Special Lemma | `Homotopy/Special.lean` |
| Lexicographic minimization and first offender | `Homotopy/MinimalLoop.lean`, `FirstOutsideIndex.lean` |
| Corank-three case, including residual branches | `Homotopy/CorankThreeReduction.lean` |
| Larger local corank | `Homotopy/LargeCorankStep.lean`, `LargeInsertion.lean`, `LargeReduction.lean` |
| Final induction | `Homotopy/CarrierInduction.lean` |
| Public homotopy theorem and independent statement | `Homotopy/Theorem.lean`, `Homotopy/Statement.lean` |

All filenames in the table after the first column are relative to
`TutteFormalization/` unless an initial `Homotopy/` is shown. The short source
comments retain historical manuscript labels; some refer to private development
paths not included in this public package. They are not required by the build.

Start with the public theorem, then follow its imports. The audit replays write
declaration-level dependency graphs for inspecting actual use, rather than merely
module imports.
