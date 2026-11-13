import Packet06ModalHotspotExistence
import Lean.Util.CollectAxioms

set_option maxHeartbeats 0
run_cmd do
  let env ← Lean.getEnv
  for n in [`Equiv.symm._elambda_2, `Equiv.symm] do
    match env.find? n with
    | none => Lean.logInfo m!"Not found: {n}"
    | some ci =>
      Lean.logInfo m!"Constant: {n}; unsafe: {ci.isUnsafe}; type: {ci.type}; module: {env.getModuleIdxFor? n}"
      match ci with
      | .axiomInfo _ => Lean.logInfo "KIND axiom"
      | .defnInfo _ => Lean.logInfo "KIND definition"
      | .opaqueInfo _ => Lean.logInfo "KIND opaque"
      | .thmInfo _ => Lean.logInfo "KIND theorem"
      | _ => Lean.logInfo "KIND other"
#print axioms Equiv.symm
