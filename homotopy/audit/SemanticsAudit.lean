import TutteFormalization.Homotopy.Statement
import TutteFormalization.Homotopy.Rotation
import TutteFormalization.Homotopy.GraphicModel
import Lean.Util.CollectAxioms

/-! This audit does not import the unfinished target. Every declaration belonging
 to a new semantic/support module is checked, including auxiliary proof constants. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`TutteFormalization.Homotopy).isPrefixOf mod do continue
    let axs ← collectAxioms n
    for ax in axs do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Unapproved transitive axiom {ax} in {n}"
    logInfo m!"{n}: {axs}"
    count := count + 1
  logInfo m!"Checked all {count} declarations from imported homotopy modules."
