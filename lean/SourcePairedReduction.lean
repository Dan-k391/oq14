import SourcePairedInclusion
import ShellReactionIdentification
import SourceCoreOperator
import SourcePairedInverse

/-! The finite paired-shell-plus-inclusion reduction: for large shell index the inclusion-weighted
reaction operator of the actual paired shell IS the clamped paired-core operator, so it converges in
operator norm to the central-inversion limit, and the effective inclusion blocks, their inverses and
their solutions converge whenever the limiting effective block is a unit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.SourcePairedReduction
open Filter Topology Metric MeasureTheory OQ14.Maxwell OQ14.DynamicConvolution
open OQ14.ShellInclusionVolume OQ14.ShellInclusionReaction OQ14.SourcePairedInclusion OQ14.SourcePairedGeometry
open OQ14.RadialPhaseLimit
open PhysicalReactionLimit (Region)
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Operator := VectorL2 →L[ℂ] VectorL2
abbrev Space := Maxwell.Space

variable (q : ℝ) (hq : 1≤q) (n : ℕ)

/-- The literal shell reaction kernel of the paired shell at the data radii is the paired shell tensor. -/
theorem reactionKernel_eq_pairedKernel (r : ℕ) (x y : Space) (hy : ‖y‖<(data q hq n r).R) (i j : Fin 3) :
    ShellReactionIdentification.reactionKernel (shell q hq n r) (data q hq n r).X (data q hq n r).R
        (data q hq n r).X x y i j=SourcePairedTensor.kernel q hq n r i j (x,y) := by
  simp only [ShellReactionIdentification.reactionKernel,ShellReactionIdentification.freeDatum,dif_pos hy,
    SourcePairedTensor.kernel,SourceTensorSeries.kernel,SourceTensorResponse.reaction,
    SourceTensorResponse.freeDatum,MaterialField.solution]

section Inclusion
variable (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : 0<b)
  (hcar : ∀ x ∈ d.carrier,‖x‖ ≤ b)
include hcar

theorem inclusion_vanish : ∀ x : Space, x ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap x)=0 := by
  intro x hx
  apply d.carrierZero
  intro hc
  exact hx (mem_closedBall_zero_iff.mpr (hcar x hc))

omit hcar in
theorem eventually_inner_radius : ∀ᶠ r : ℕ in atTop,b<(data q hq n r).R :=
  radius_tendsto.eventually (eventually_gt_atTop b)

/-- For large shell index, the inclusion-weighted reaction operator of the actual paired shell equals
the clamped paired-core operator. -/
theorem eventually_reaction_eq_core :
    ∀ᶠ r : ℕ in atTop,reaction (shell q hq n r) ci 1 (data q hq n r).X=
      SourcePairedCore.operator ci d q hq n b hb r := by
  have hall : ∀ᶠ r : ℕ in atTop,∀ i j : Fin 3,∀ p : Region b,
      (CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)).value p.val.1 p.val.2=
        SourcePairedTensor.kernel q hq n r i j p.val :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr
      (fun j => SourcePairedCore.eventually_entries_actual q hq n b hb i j))
  filter_upwards [hall,eventually_inner_radius q hq n b] with r hr hbR
  apply ContinuousLinearMap.ext
  intro u
  apply MaterialVolumeConverse.vector_ext
  intro i
  have hcs : ∀ y : Space, y ∉ closedBall (0 : Space) (data q hq n r).X \ ball (0 : Space) (data q hq n r).R →
      (shell q hq n r).value (VectorFourier.coordinateMap y)=0 := by
    intro y hy
    by_cases h1 : y ∈ closedBall (0 : Space) (data q hq n r).X
    · by_cases h2 : y ∈ ball (0 : Space) (data q hq n r).R
      · exact shell_inner q hq n r y (mem_ball_zero_iff.mp h2).le
      · exact absurd ⟨h1,h2⟩ hy
    · exact shell_support q hq n r y h1
  have h1 := ShellReactionIdentification.reaction_actual (shell q hq n r) ci b (data q hq n r).R
    (data q hq n r).X (data q hq n r).X hbR (radii_ordered q hq n r) le_rfl hcs
    (inclusion_vanish ci d b hcar) u i
  have h2 := BoundedMaterialKernel.component_operator_ae d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)) u i
  filter_upwards [h1,h2] with x e1 e2
  rw [e1]
  change component i (BoundedMaterialKernel.operator d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)) u) x=_ at e2
  change _=component i (BoundedMaterialKernel.operator d
    (fun i j => CompactCoreKernel.extension b hb (SourcePairedCore.actualMap q hq n b i j r)) u) x
  rw [e2]
  by_cases hxc : x ∈ d.carrier
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply integral_congr_ae
    filter_upwards [StaticNewton.material_source_ae ci u j] with y hy
    rw [component_apply,hy]
    by_cases hyc : y ∈ d.carrier
    · have hyb : ‖y‖<(data q hq n r).R := (hcar y hyc).trans_lt hbR
      rw [reactionKernel_eq_pairedKernel q hq n r x y hyb i j,
        hr i j ⟨(x,y),SourceCoreOperator.pair_mem_region b x y (hcar x hxc) (hcar y hyc)⟩]
      rfl
    · rw [d.carrierZero y hyc]
      simp [DynamicVolume.source,d.carrierZero y hyc]
  · simp [d.carrierZero x hxc]

/-- The paired-shell reaction operators converge in operator norm to the clamped central-inversion
limit operator. -/
theorem reaction_tendsto :
    Tendsto (fun r : ℕ => reaction (shell q hq n r) ci 1 (data q hq n r).X) atTop
      (𝓝 (SourcePairedCore.limitingOperator ci d q hq n b hb)) :=
  (SourcePairedCore.operator_limit ci d q hq n b hb).congr'
    ((eventually_reaction_eq_core q hq n ci d b hb hcar).mono (fun _ h => h.symm))

/-- The limiting effective inclusion block. -/
def limitEffective : Operator :=
  DynamicVolume.volumeBlock ci 1 b-SourcePairedCore.limitingOperator ci d q hq n b hb

theorem effective_tendsto :
    Tendsto (fun r : ℕ => DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X)
      atTop (𝓝 (limitEffective q hq n ci d b hb)) :=
  tendsto_const_nhds.sub (reaction_tendsto q hq n ci d b hb hcar)

theorem eventually_effective_isUnit (hL : IsUnit (limitEffective q hq n ci d b hb)) :
    ∀ᶠ r : ℕ in atTop,IsUnit (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X) :=
  SourcePairedInverse.eventually_isUnit _ _ _ (reaction_tendsto q hq n ci d b hb hcar) hL

/-- For large shell index the combined paired-shell-plus-inclusion block is a unit. -/
theorem eventually_combined_isUnit (hL : IsUnit (limitEffective q hq n ci d b hb)) :
    ∀ᶠ r : ℕ in atTop,IsUnit (DynamicVolume.volumeBlock (add (shell q hq n r) ci) 1 (data q hq n r).X) := by
  filter_upwards [eventually_effective_isUnit q hq n ci d b hb hcar hL,eventually_inner_radius q hq n b] with r hE hbR
  exact combined_isUnit_of_effective q hq n r ci b hbR.le (inclusion_vanish ci d b hcar) hE

theorem effective_inverse_tendsto (hL : IsUnit (limitEffective q hq n ci d b hb)) :
    Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X))
      atTop (𝓝 (Ring.inverse (limitEffective q hq n ci d b hb))) :=
  SourcePairedInverse.inverse_tendsto _ _ _ (reaction_tendsto q hq n ci d b hb hcar) hL

theorem effective_solution_tendsto (hL : IsUnit (limitEffective q hq n ci d b hb))
    (f : ℕ → VectorL2) (g : VectorL2) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun r : ℕ => Ring.inverse (DynamicVolume.volumeBlock ci 1 b-reaction (shell q hq n r) ci 1 (data q hq n r).X) (f r))
      atTop (𝓝 (Ring.inverse (limitEffective q hq n ci d b hb) g)) :=
  SourcePairedInverse.solution_tendsto _ _ _ (reaction_tendsto q hq n ci d b hb hcar) hL f g hf

omit hcar in
/-- Smallness of the inclusion relative to the limit kernel makes the limiting effective block a unit. -/
theorem limitEffective_isUnit_of_small
    (hsmall : DynamicVolume.errorBound ci 1 b+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖<1) :
    IsUnit (limitEffective q hq n ci d b hb) := by
  have he : limitEffective q hq n ci d b hb=
      StaticCoefficient.weightedBlock ci-
        (DynamicVolume.weightedRemainder ci 1 b+SourcePairedCore.limitingOperator ci d q hq n b hb) := by
    unfold limitEffective DynamicVolume.volumeBlock
    rw [StaticNewton.volumeBlock_eq]
    abel
  rw [he]
  apply StaticCoefficient.weightedBlock_perturbation_isUnit
  calc ‖DynamicVolume.weightedRemainder ci 1 b+SourcePairedCore.limitingOperator ci d q hq n b hb‖
      ≤ ‖DynamicVolume.weightedRemainder ci 1 b‖+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖ := norm_add_le _ _
    _ ≤ DynamicVolume.errorBound ci 1 b+‖SourcePairedCore.limitingOperator ci d q hq n b hb‖ :=
      add_le_add (DynamicVolume.weightedRemainder_norm_le ci 1 b hb.le) le_rfl
    _ < 1 := hsmall

end Inclusion
end OQ14.SourcePairedReduction
#print axioms OQ14.SourcePairedReduction.reactionKernel_eq_pairedKernel
#print axioms OQ14.SourcePairedReduction.inclusion_vanish
#print axioms OQ14.SourcePairedReduction.eventually_inner_radius
#print axioms OQ14.SourcePairedReduction.eventually_reaction_eq_core
#print axioms OQ14.SourcePairedReduction.reaction_tendsto
#print axioms OQ14.SourcePairedReduction.effective_tendsto
#print axioms OQ14.SourcePairedReduction.eventually_effective_isUnit
#print axioms OQ14.SourcePairedReduction.eventually_combined_isUnit
#print axioms OQ14.SourcePairedReduction.effective_inverse_tendsto
#print axioms OQ14.SourcePairedReduction.effective_solution_tendsto
#print axioms OQ14.SourcePairedReduction.limitEffective_isUnit_of_small
