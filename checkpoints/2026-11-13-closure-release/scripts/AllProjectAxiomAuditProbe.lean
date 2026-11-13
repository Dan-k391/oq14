import Packet06ModalHotspotExistence
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
set_option maxRecDepth 100000

run_cmd do
  let env ← Lean.getEnv
  let modules : Std.HashSet Lean.Name := Std.HashSet.ofList [`Packet06ModalHotspotExistence]
  let names ← env.constants.foldM (init := (#[] : Array Lean.Name)) fun acc name ci => do
    match env.getModuleIdxFor? name with
    | some idx =>
      if modules.contains env.header.moduleNames[idx]! && !ci.isUnsafe then pure (acc.push name) else pure acc
    | none => pure acc
  let unsafeNames ← env.constants.foldM (init := (#[] : Array Lean.Name)) fun acc name ci => do
    match env.getModuleIdxFor? name with
    | some idx =>
      if modules.contains env.header.moduleNames[idx]! && ci.isUnsafe then pure (acc.push name) else pure acc
    | none => pure acc
  for name in unsafeNames do
    Lean.logInfo m!"EXCLUDED UNSAFE IMPLEMENTATION: {name}"
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  let allowed : Array Lean.Name := #[`propext, `Classical.choice, `Quot.sound]
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Unexpected project dependency axiom: {ax}"
  Lean.logInfo m!"AUDIT ALL KERNEL-SAFE PROJECT CONSTANTS: {names.size}; UNSAFE IMPLEMENTATIONS EXCLUDED: {unsafeNames.size}; AXIOMS: {state.axioms}"
