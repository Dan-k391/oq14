import FiniteSphereResidual

/-! # Derived norm bounds for actual finite-sphere cross-field residuals -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.FiniteSphereResidualBound

open MeasureTheory Metric Set StaticBallNewton FiniteSphereStatic FiniteSphereResidual
open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def interactionBound (r : ι → ℝ) (P : ι → Vector) (δ : ℝ) : ℝ :=
  ∑ j : ι, ((4/3 : ℝ)*((r j)^3/(δ/2)^3))*(∑ k : Fin 3, ‖P j k‖)

omit [DecidableEq ι] in
theorem interactionBound_nonnegative (r : ι → ℝ) (P : ι → Vector) (δ : ℝ)
    (hr : ∀ j, 0 ≤ r j) (hδ : 0 ≤ δ) : 0 ≤ interactionBound r P δ := by
  unfold interactionBound
  exact Finset.sum_nonneg (fun j _ => by have hj := hr j; positivity)

theorem residual_inside_bound (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (δ : ℝ) (hδ : 0 < δ) (hr : ∀ j, 0 < r j)
    (hsmall : ∀ j, r j ≤ δ/4) (hsep : ∀ i j, i ≠ j → δ ≤ dist (p i) (p j)) (m : Fin 3) :
    ∀ᵐ x : Space, x ∈ ⋃ j, ball (p j) (r j) →
      ‖residual p r χ hχ E (VectorFourier.coordinateMap x) m‖ ≤
        Real.sqrt χ*interactionBound r (fun j => StaticSpherePolarization.polarization χ (E j)) δ := by
  let P := fun j => StaticSpherePolarization.polarization χ (E j)
  have hdis : ∀ i j, i ≠ j → r i+r j ≤ dist (p i) (p j) := by
    intro i j hij
    linarith [hsmall i, hsmall j, hsep i j hij]
  have hc : ∀ᵐ x : Space, ∀ i : ι, x ∈ ball (p i) (r i) →
      residual p r χ hχ E (VectorFourier.coordinateMap x) m =
        -(Real.sqrt χ : ℂ)*NewtonL2.newtonOperator (StaticBallInteraction.crossSource p r P i)
          (VectorFourier.coordinateMap x) m :=
    ae_all_iff.mpr (fun i => residual_on_ball p r χ hχ E hr hdis i m)
  have hb : ∀ᵐ x : Space, ∀ i : ι, x ∈ ball (p i) (r i) →
      ‖NewtonL2.newtonOperator (StaticBallInteraction.crossSource p r P i)
        (VectorFourier.coordinateMap x) m‖ ≤
        ∑ j ∈ Finset.univ.erase i, ((4/3 : ℝ)*((r j)^3/(δ/2)^3))*(∑ k : Fin 3, ‖P j k‖) :=
    ae_all_iff.mpr (fun i => StaticBallInteraction.finite_cross_bound p r P i δ hδ hr hsmall
      (fun j hji => hsep i j hji.symm) m)
  filter_upwards [hc, hb] with x hc hb hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  rw [hc i hi, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left ((hb i hi).trans _) (Real.sqrt_nonneg _)
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
    (fun j _ _ => by have hj := hr j; positivity)

theorem residual_norm_bound (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (E : ι → Vector) (δ : ℝ) (hδ : 0 < δ) (hr : ∀ j, 0 < r j)
    (hsmall : ∀ j, r j ≤ δ/4) (hsep : ∀ i j, i ≠ j → δ ≤ dist (p i) (p j))
    (R : ℝ) (hinside : ∀ j, ‖p j‖+r j ≤ R) :
    ‖residual p r χ hχ E‖ ≤
      (3*Real.sqrt χ*interactionBound r (fun j => StaticSpherePolarization.polarization χ (E j)) δ)*
        Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) := by
  let P := fun j => StaticSpherePolarization.polarization χ (E j)
  let d := FiniteSphereStatic.supportData p r χ hχ R hinside
  let w := DynamicSupportVolume.supportIndicator d.carrier d.measurable d.finite
  have hw : ‖w‖ = Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) :=
    DynamicSupportVolume.supportIndicator_norm d.carrier d.measurable d.finite
  have hi : ∀ m : Fin 3, ‖DynamicConvolution.component m (residual p r χ hχ E)‖ ≤
      (Real.sqrt χ*interactionBound r P δ)*Real.sqrt (volume.real (⋃ j, ball (p j) (r j))) := by
    intro m
    have hb : ∀ᵐ x : Space, ‖DynamicConvolution.component m (residual p r χ hχ E) x‖ ≤
        (Real.sqrt χ*interactionBound r P δ)*‖w x‖ := by
      filter_upwards [NewtonL2.physicalCoordinate_ae (residual p r χ hχ E) m,
        residual_inside_bound p r χ hχ E δ hδ hr hsmall hsep m,
        residual_outside p r χ hχ E m,
        indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := d.measurable)
          (hμs := d.finite) (c := (1 : ℂ))] with x hc hi ho hw
      rw [DynamicConvolution.component_apply, hc]
      change w x = d.carrier.indicator (fun _ => (1 : ℂ)) x at hw
      change w x = (⋃ j, ball (p j) (r j)).indicator (fun _ => (1 : ℂ)) x at hw
      by_cases hx : x ∈ ⋃ j, ball (p j) (r j)
      · rw [hw, indicator_of_mem hx, norm_one, mul_one]
        exact hi hx
      · rw [ho hx, norm_zero, hw, indicator_of_not_mem hx, norm_zero, mul_zero]
    simpa only [hw] using Lp.norm_le_mul_norm_of_ae_le_mul hb
  apply (DynamicSupportVolume.vector_norm_le_sum_components (residual p r χ hχ E)).trans
  apply (Finset.sum_le_sum (fun m (_ : m ∈ (Finset.univ : Finset (Fin 3))) => hi m)).trans_eq
  simp only [Fin.sum_univ_three]
  ring

end OQ14.FiniteSphereResidualBound

#print axioms OQ14.FiniteSphereResidualBound.interactionBound_nonnegative
#print axioms OQ14.FiniteSphereResidualBound.residual_inside_bound
#print axioms OQ14.FiniteSphereResidualBound.residual_norm_bound
