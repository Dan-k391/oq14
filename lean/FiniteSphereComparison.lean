import FiniteSphereResidualBound
import StaticSphereScale

/-! # Actual forcing variation and inverse comparison for finite sphere trials -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.FiniteSphereComparison

open MeasureTheory Metric Set StaticBallNewton FiniteSphereStatic FiniteSphereResidual
  FiniteSphereResidualBound ParityReactionVolume
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem trial_norm_bound (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ) (E : ι → Vector) :
    ‖trial p r χ E‖ ≤ ∑ j : ι, (Real.sqrt χ*(∑ m : Fin 3, ‖E j m‖))*
      Real.sqrt (volume.real (ball (0 : Space) (r j))) := by
  apply (norm_sum_le Finset.univ (fun j => StaticSphereMaterial.trial (p j) (r j) χ (E j))).trans
  exact Finset.sum_le_sum (fun j _ => StaticSphereScale.trial_norm_bound (p j) (r j) χ hχ (E j))

theorem forcing_error_bound (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (R : ℝ) (hinside : ∀ j, ‖p j‖+r j ≤ R)
    (hsep : ∀ i j, i ≠ j → r i+r j ≤ dist (p i) (p j))
    (f : VectorL2) (incident : Maxwell.Field) (M : ℝ)
    (hincident : ∀ m : Fin 3, (fun x => f (VectorFourier.coordinateMap x) m) =ᵐ[volume]
      fun x => (Real.sqrt ((coefficient p r χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*incident x m)
    (hvariation : ∀ j, ∀ x ∈ ball (p j) (r j), ∀ m : Fin 3, ‖incident x m-E j m‖ ≤ M) :
    ‖f-forcing p r χ E‖ ≤
      (3*Real.sqrt χ*M)*Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) := by
  let f₀ := forcing p r χ E
  let d := FiniteSphereStatic.supportData p r χ hχ R hinside
  let w := DynamicSupportVolume.supportIndicator d.carrier d.measurable d.finite
  have hw : ‖w‖ = Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) :=
    DynamicSupportVolume.supportIndicator_norm d.carrier d.measurable d.finite
  have hi : ∀ m : Fin 3, ‖DynamicConvolution.component m (f-f₀)‖ ≤
      (Real.sqrt χ*M)*Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) := by
    intro m
    have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_sub f f₀)
    have hc : ∀ᵐ x : Space, ∀ j : ι, x ∈ ball (p j) (r j) →
        f₀ (VectorFourier.coordinateMap x) m = (Real.sqrt χ : ℂ)*E j m :=
      ae_all_iff.mpr (fun j => sumSource_on_ball p r (fun j => (Real.sqrt χ : ℂ) • E j) hsep j m)
    have hb : ∀ᵐ x : Space, ‖DynamicConvolution.component m (f-f₀) x‖ ≤
        (Real.sqrt χ*M)*‖w x‖ := by
      filter_upwards [hs, hc, NewtonL2.physicalCoordinate_ae (f-f₀) m, hincident m,
        sumSource_ae p r (fun j => (Real.sqrt χ : ℂ) • E j) m,
        indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := d.measurable)
          (hμs := d.finite) (c := (1 : ℂ))] with x hs hc hp hf hsum hw
      rw [DynamicConvolution.component_apply, hp, hs, Pi.sub_apply]
      change ‖f (VectorFourier.coordinateMap x) m-f₀ (VectorFourier.coordinateMap x) m‖ ≤ _
      rw [hf, coefficient_value]
      change w x = (⋃ j, ball (p j) (r j)).indicator (fun _ => (1 : ℂ)) x at hw
      by_cases hx : x ∈ ⋃ j, ball (p j) (r j)
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
        rw [if_pos hx, hc j hj, hw, indicator_of_mem hx, norm_one, mul_one, ← mul_sub,
          norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_mul_of_nonneg_left (hvariation j x hj m) (Real.sqrt_nonneg _)
      · have hn : ∀ j : ι, x ∉ ball (p j) (r j) := fun j hj => hx (mem_iUnion.mpr ⟨j,hj⟩)
        change f₀ (VectorFourier.coordinateMap x) m = _ at hsum
        rw [if_neg hx, hsum, hw, indicator_of_not_mem hx]
        simp [hn]
    simpa only [hw] using Lp.norm_le_mul_norm_of_ae_le_mul hb
  apply (DynamicSupportVolume.vector_norm_le_sum_components (f-f₀)).trans
  apply (Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin 3))) => hi m)).trans_eq
  simp only [Fin.sum_univ_three]
  ring

theorem parity_comparison (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (δ : ℝ) (hδ : 0 < δ) (hr : ∀ j, 0 < r j)
    (hrad : ∀ j, r j ≤ δ/4) (hsep : ∀ i j, i ≠ j → δ ≤ dist (p i) (p j))
    (R : ℝ) (hinside : ∀ j, ‖p j‖+r j ≤ R)
    (d : BoundedMaterialKernel.SupportData (coefficient p r χ hχ)) (k B : ℝ)
    (hsmall : perturbationBound d k B ≤ 1/2) (f : VectorL2) :
    ‖ParityMaterialField.solution d k B f-trial p r χ E‖ ≤
      2*(‖f-forcing p r χ E‖ +
        (3*Real.sqrt χ*interactionBound r (fun j => StaticSpherePolarization.polarization χ (E j)) δ)*
          Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) +
        perturbationBound d k B*‖trial p r χ E‖) := by
  apply (StaticSphereResidual.solution_residual d k B hsmall f (trial p r χ E)).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  have he : f-ParityMaterialField.block d k B (trial p r χ E) =
      (f-forcing p r χ E)-FiniteSphereResidual.residual p r χ hχ E+perturbation d k B (trial p r χ E) := by
    unfold FiniteSphereResidual.residual
    rw [StaticNewton.volumeBlock_eq]
    change f-(StaticCoefficient.weightedBlock _ _-perturbation d k B _) = _
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (norm_sub_le _ _).trans (add_le_add_left
      (residual_norm_bound p r χ hχ E δ hδ hr hrad hsep R hinside) _)
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (perturbation_norm d k B) (norm_nonneg _))

end OQ14.FiniteSphereComparison

#print axioms OQ14.FiniteSphereComparison.trial_norm_bound
#print axioms OQ14.FiniteSphereComparison.forcing_error_bound
#print axioms OQ14.FiniteSphereComparison.parity_comparison
