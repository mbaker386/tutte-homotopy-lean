import TutteFormalization.Homotopy.Theorem
import TutteFormalization.Homotopy.ContractHomotopy
import TutteFormalization.Homotopy.SelectedThird
import TutteFormalization.Homotopy.OffJoinDecomposable
import TutteFormalization.Homotopy.OffJoinIndecomposable
import TutteFormalization.Homotopy.FirstOffenderReduction
import TutteFormalization.Homotopy.TriangleRankThree
import TutteFormalization.Homotopy.MinimalLoop
import TutteFormalization.Homotopy.LocalTriple
import TutteFormalization.Homotopy.Special
import TutteFormalization.Homotopy.RecognizedSixModel
import TutteFormalization.Homotopy.CubeDegreeCount
import TutteFormalization.Homotopy.LargeSpecial
import TutteFormalization.Homotopy.PencilCounts
import TutteFormalization.Homotopy.SecondIntersection
import TutteFormalization.Homotopy.TransversalJoin
import TutteFormalization.Homotopy.CorankOne
import TutteFormalization.Homotopy.FourthRecognition
import TutteFormalization.Homotopy.HyperplaneRecognition
import TutteFormalization.Homotopy.ContractHomotopy
import TutteFormalization.Homotopy.CorankThreeGeometry
import TutteFormalization.Homotopy.Statement
import TutteFormalization.Homotopy.Rotation
import TutteFormalization.Homotopy.GraphicModel
import Lean.Replay
import Lean.Util.FoldConsts

/-! Fresh kernel replay of the homotopy semantics and all preparation support, using a fresh
Mathlib-only environment. No proof is obtained by native evaluation. The replay
calls the kernel on the already elaborated declarations. This is a second
mechanical check, not an independent mathematical review of the source prose. -/

open Lean in
run_cmd do
  let env ← getEnv
  let base ← importModules #[{ module := `Mathlib }] {} 0
  let mut pending : Array Name := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`TutteFormalization.Homotopy).isPrefixOf mod then pending := pending.push n
  let mut found : Std.HashMap Name ConstantInfo := {}
  let mut edges : Array Json := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    if found.contains n || (base.find? n).isSome then
      continue
    let some ci := env.find? n | throwError "Missing dependency: {n}"
    found := found.insert n ci
    let mut deps := ci.getUsedConstantsAsSet
    if let .inductInfo info := ci then
      for nm in info.all ++ info.ctors do deps := deps.insert nm
    if let .recInfo info := ci then
      for nm in info.all do deps := deps.insert nm
    let mut ds : Array Json := #[]
    for dep in deps do
      pending := pending.push dep
      ds := ds.push (toJson dep.toString)
    edges := edges.push (Json.mkObj [("declaration", toJson n.toString), ("dependencies", toJson ds)])
  for (n, ci) in found.toList do
    if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial dependency: {n}"
    if let .axiomInfo _ := ci then throwError "New axiom in project dependency: {n}"
  let checked ← base.toKernelEnv.replay found
  unless (checked.find? `TutteFormalization.HomotopyTheoremStatement).isSome do
    throwError "Replay did not produce the target"
  unless (checked.find? `TutteFormalization.homotopy_theorem).isSome do
    throwError "Replay did not produce the public homotopy theorem"
  IO.FS.writeFile "homotopy/audit/final_dependency_graph.json" (Json.pretty (toJson edges) ++ "\n")
  logInfo m!"Fresh Mathlib-only kernel replay passed for {found.size} declarations, including the completed public homotopy theorem and independent statement."
