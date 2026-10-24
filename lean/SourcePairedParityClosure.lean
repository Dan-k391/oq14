import SourcePairedWallKernelAE
import HalfTurnParityEquivariance

/-! Closure of the finite-shell source reduction onto the parity device: for a half-turn symmetric
inclusion and half-turn-fixed data, the effective inclusion solutions of the actual paired shells
converge to the explicit parity material solution with gain parameter q^n. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
namespace OQ14.SourcePairedParityClosure
open Filter Topology OQ14.ShellInclusionReaction OQ14.SourcePairedInclusion OQ14.SourcePairedReduction
open OQ14.SourcePairedWallKernelAE OQ14.HalfTurnVectorAction OQ14.HalfTurnParityEquivariance
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

/-- The parity solution of half-turn-fixed data has almost-everywhere invariant source. -/
theorem source_invariantAE_of_fixed (ci : Coefficient) (hsym : Symmetric ci)
    (d : BoundedMaterialKernel.SupportData ci) (B : ℝ) (hu : IsUnit (ParityMaterialField.block d 1 B))
    (f : VectorL2) (hf : U f=f) :
    HalfTurnReactionBridgeAE.InvariantAE (sourceField ci (ParityMaterialField.solution d 1 B f)) := by
  intro j
  filter_upwards [solution_source_invariant_ae ci hsym d 1 B hu f hf j] with y hy
  simp only [sourceField]
  rw [← HalfTurnReactionKernel.rotation_eq]
  change DynamicVolume.source ci (ParityMaterialField.solution d 1 B f) j (rot y)=_
  rw [hy]
  simp only [o]
  push_cast
  ring

theorem parity_solution_equation (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (B : ℝ)
    (hu : IsUnit (ParityMaterialField.block d 1 B)) (f : VectorL2) :
    ParityMaterialField.block d 1 B (ParityMaterialField.solution d 1 B f)=f :=
  congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f) (Ring.mul_inverse_cancel _ hu)

section Closure
variable (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0<b) (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b) (hsym : Symmetric ci)
include hb hcar hsym

/-- Main closure statement of the source reduction: the effective inclusion solutions of the actual
paired shells converge to the explicit parity-device solution of half-turn-fixed data. -/
theorem paired_shell_solutions_tendsto_parity (hL : IsUnit (limitEffective q hq n ci d b hb))
    (hu : IsUnit (ParityMaterialField.block d 1 (q^n))) (f : VectorL2) (hf : U f=f) :
    Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X) f)
      atTop (𝓝 (ParityMaterialField.solution d 1 (q^n) f)) := by
  have h := effective_solution_tendsto q hq n ci d b hb hcar hL (fun _ => f) f tendsto_const_nhds
  rwa [limit_solution_eq_parity q hq n ci d b hb hcar hL (ParityMaterialField.solution d 1 (q^n) f) f
    (source_invariantAE_of_fixed ci hsym d (q^n) hu f hf) (parity_solution_equation ci d (q^n) hu f)] at h

/-- The same with both unit properties discharged by the explicit smallness hypotheses. -/
theorem paired_shell_solutions_tendsto_parity_of_small
    (hsmall : SourcePairedSmallness.dataSmallness q hq n ci d b<1)
    (hpar : ParityReactionVolume.perturbationBound d 1 (q^n)<1) (f : VectorL2) (hf : U f=f) :
    Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X) f)
      atTop (𝓝 (ParityMaterialField.solution d 1 (q^n) f)) :=
  paired_shell_solutions_tendsto_parity q hq n ci d b hb hcar hsym
    (SourcePairedSmallness.limitEffective_isUnit_of_data q hq n ci d b hb hsmall)
    (ParityReactionVolume.explicitBlock_isUnit d 1 (q^n) hpar) f hf

end Closure
end OQ14.SourcePairedParityClosure
#print axioms OQ14.SourcePairedParityClosure.source_invariantAE_of_fixed
#print axioms OQ14.SourcePairedParityClosure.parity_solution_equation
#print axioms OQ14.SourcePairedParityClosure.paired_shell_solutions_tendsto_parity
#print axioms OQ14.SourcePairedParityClosure.paired_shell_solutions_tendsto_parity_of_small
