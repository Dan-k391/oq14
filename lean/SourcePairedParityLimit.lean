import SourcePairedWallKernel

/-! The paired-shell inclusion solutions converge to the explicit parity-device solution of invariant
data: the finite-shell reduction meets the channel branch's parity device on the invariant sector. -/
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 10000
namespace OQ14.SourcePairedParityLimit
open Filter Topology OQ14.ShellInclusionReaction OQ14.SourcePairedInclusion OQ14.SourcePairedReduction
open OQ14.SourcePairedWallKernel OQ14.HalfTurnMaxwellParity
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

variable (q : ℝ) (hq : 1≤q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0<b) (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b)
include hb hcar

/-- If the limiting effective block is a unit and u is a parity-device solution of the datum f with
invariant source, then the effective inclusion solutions of the actual paired shells converge to u. -/
theorem effective_solution_tendsto_parity (hL : IsUnit (limitEffective q hq n ci d b hb))
    (u f : VectorL2) (hinv : Invariant (sourceField ci u)) (hu : ParityMaterialField.block d 1 (q^n) u=f) :
    Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X) f)
      atTop (𝓝 u) := by
  have h := effective_solution_tendsto q hq n ci d b hb hcar hL (fun _ => f) f tendsto_const_nhds
  rwa [limit_solution_eq_parity q hq n ci d b hb hcar hL u f hinv hu] at h

/-- The same with the unit property supplied by inclusion-data smallness. -/
theorem effective_solution_tendsto_parity_of_data (hsmall : SourcePairedSmallness.dataSmallness q hq n ci d b<1)
    (u f : VectorL2) (hinv : Invariant (sourceField ci u)) (hu : ParityMaterialField.block d 1 (q^n) u=f) :
    Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X) f)
      atTop (𝓝 u) :=
  effective_solution_tendsto_parity q hq n ci d b hb hcar
    (SourcePairedSmallness.limitEffective_isUnit_of_data q hq n ci d b hb hsmall) u f hinv hu

end OQ14.SourcePairedParityLimit
#print axioms OQ14.SourcePairedParityLimit.effective_solution_tendsto_parity
#print axioms OQ14.SourcePairedParityLimit.effective_solution_tendsto_parity_of_data
