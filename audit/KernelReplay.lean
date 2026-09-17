import TutteFormalization.PathTheorem
import Lean.Replay
import Lean.Util.FoldConsts

/-! Fresh kernel replay of the target and project dependencies, using a fresh
Mathlib-only environment. No proof is obtained by native evaluation. The replay
calls the kernel on the already elaborated declarations. This is a second
mechanical check, not an independent mathematical review of the source prose. -/

open Lean in
run_cmd do
  let env ← getEnv
  let base ← importModules #[{ module := `Mathlib }] {} 0
  let mut pending := #[`TutteFormalization.path_theorem]
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
  unless (checked.find? `TutteFormalization.path_theorem).isSome do
    throwError "Replay did not produce the target"
  IO.FS.writeFile "audit/final_dependency_graph.json" (Json.pretty (toJson edges) ++ "\n")
  logInfo m!"Fresh Mathlib-only kernel replay passed for {found.size} declarations, including path_theorem."
