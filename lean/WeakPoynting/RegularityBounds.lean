import WeakPoynting.LocalRegularity

/-! # Quantitative local magnetic H1 bounds from actual Maxwell equations -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.RegularityBounds

open MeasureTheory OQ14.Maxwell OQ14.CurlCutoff OQ14.LocalRegularity
  OQ14.DivCurlCompact OQ14.DivCurlRegularity
open scoped Topology

theorem cutoffDivergence_norm_le {Ω : Set Space} (χ : WeakCurl.Test)
    (E : DomainCurl.L2Vector Ω) {B : ℝ} (hB : 0 ≤ B)
    (hdχ : ∀ i x, ‖dcoord χ.function x i‖ ≤ B) :
    ‖cutoffDivergence Ω χ E‖ ≤ 3 * B * ‖E‖ := by
  have hd (i : Fin 3) : ‖derivativeMultiply Ω χ i (E i)‖ ≤ B * ‖E‖ :=
    (mulL2_norm_le Ω _ (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) (E i) (hdχ i)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm E i) hB)
  exact (norm_add_le _ _).trans
    ((add_le_add_right (norm_add_le _ _) _).trans (by linarith [hd 0, hd 1, hd 2]))

theorem maxwell_magnetic_curl_norm_le {Ω : Set Space}
    (ω : ℝ) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell ω (fun _ => 1) ε E H)
    {M : ℝ} (hM0 : 0 ≤ M) (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M) :
    ‖H.val.2‖ ≤ |ω| * M * ‖E.val.1‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hj : ‖H.val.2 j‖ ≤ (|ω| * M) * ‖E.val.1 j‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hM.2, hε] with x hx he
    rw [hx j]
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (abs_nonneg ω)) (norm_nonneg _)
  exact hj.trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm E.val.1 j) (by positivity))

theorem cutoff_derivative_energy_bound {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvχ : ∀ x, ‖χ.function x‖ ≤ A) (hdχ : ∀ i x, ‖dcoord χ.function x i‖ ≤ B)
    (E C : DomainCurl.L2Vector Ω) :
    (∑ j : Fin 3, ‖extendVector Ω hΩ.measurableSet (productCurl Ω χ.toTest E C) j‖ ^ 2) +
      ‖extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest E)‖ ^ 2 ≤
        3 * (A * ‖C‖ + 2 * B * ‖E‖)^2 + (3 * B * ‖E‖)^2 := by
  have hc (j : Fin 3) :
      ‖extendVector Ω hΩ.measurableSet (productCurl Ω χ.toTest E C) j‖ ≤
        A * ‖C‖ + 2 * B * ‖E‖ := by
    rw [extendVector, extendScalar_norm]
    exact (norm_le_pi_norm (productCurl Ω χ.toTest E C) j).trans
      (productCurl_norm_le Ω χ.toTest E C hA hB hvχ hdχ)
  have hd : ‖extendScalar Ω hΩ.measurableSet (cutoffDivergence Ω χ.toTest E)‖ ≤
      3 * B * ‖E‖ := by
    rw [extendScalar_norm]
    exact cutoffDivergence_norm_le χ.toTest E hB hdχ
  have hc2 (j : Fin 3) := pow_le_pow_left₀ (norm_nonneg _) (hc j) 2
  have hd2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  simp only [Fin.sum_univ_three]
  linarith [hc2 0, hc2 1, hc2 2]

/-- A bound for the constructed derivatives entirely in terms of regional
field L2 norms, frequency, the permittivity bound, and the actual cutoff. -/
theorem maxwell_cutoff_h1_bound {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    {A B M : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hM0 : 0 ≤ M)
    (hvχ : ∀ x, ‖χ.function x‖ ≤ A) (hdχ : ∀ i x, ‖dcoord χ.function x i‖ ≤ B)
    (ω : ℝ) (hω : ω ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell ω (fun _ => 1) ε E H)
    (hε : ∀ᵐ x ∂DomainCurl.regionMeasure Ω, |ε x| ≤ M) :
    ∃ G : DerivativeIndex → WeakCurl.L2Scalar,
      (∀ p, HasWeakPartial
        (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.1) p.2) (G p) p.1) ∧
      (∑ p, ‖G p‖ ^ 2) ≤
        3 * (A * (|ω| * M * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
          (3 * B * ‖H.val.1‖)^2 := by
  obtain ⟨G, hG, he⟩ := maxwell_cutoff_magnetic_regularity hΩ χ hχ ω hω ε E H hM
  refine ⟨G, hG, ?_⟩
  rw [he]
  apply (cutoff_derivative_energy_bound hΩ χ hA hB hvχ hdχ H.val.1 H.val.2).trans
  have hc := maxwell_magnetic_curl_norm_le ω ε E H hM hM0 hε
  have hb : A * ‖H.val.2‖ + 2 * B * ‖H.val.1‖ ≤
      A * (|ω| * M * ‖E.val.1‖) + 2 * B * ‖H.val.1‖ :=
    add_le_add_right (mul_le_mul_of_nonneg_left hc hA) _
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ A * ‖H.val.2‖ + 2 * B * ‖H.val.1‖) hb 2
  linarith

end OQ14.RegularityBounds

#print axioms OQ14.RegularityBounds.cutoffDivergence_norm_le
#print axioms OQ14.RegularityBounds.maxwell_magnetic_curl_norm_le
#print axioms OQ14.RegularityBounds.cutoff_derivative_energy_bound
#print axioms OQ14.RegularityBounds.maxwell_cutoff_h1_bound
