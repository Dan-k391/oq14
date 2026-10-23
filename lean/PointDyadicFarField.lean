import MaxwellFarField

/-! Genuine translated point-dyadic electric far amplitude from actual kernel estimates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PointDyadicFarField
open Filter Metric OQ14.Maxwell OQ14.DyadicRadiation
open scoped Topology RealInnerProductSpace

theorem error_limit (k : ℝ) (n y : Space) (hn : ‖n‖=1) (i j : Fin 3) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor k r*
      (DyadicKernel.dyadic k (r • n-y) i j-
        (k : ℂ)^2*GreenKernel.phi k (r • n-y)*transverse n i j)) atTop (𝓝 0) := by
  apply MaxwellFarField.scaled_error_limit k
    (4*(k^2*‖y‖+|k|+1)/Real.pi) (max (2*‖y‖) 2)
  intro r hr
  have hr0 : 0<r := lt_of_lt_of_le (by norm_num : (0 : ℝ)<2) ((le_max_right _ _).trans hr.le)
  have hnr : ‖r • n‖=r := by rw [norm_smul,hn,mul_one,Real.norm_eq_abs,abs_of_pos hr0]
  have h := dyadic_source_error k ‖y‖ (norm_nonneg y) (r • n) y
    (by rw [hnr];exact (le_max_left _ _).trans_lt hr)
    (by rw [hnr];exact (le_max_right _ _).trans hr.le)
    (by simp only [mem_closedBall_zero_iff,le_refl]) i j
  rw [MaxwellFarField.ray_transverse n hn r hr0,hnr] at h
  exact h.trans_eq (by ring)

theorem electric_limit (k : ℝ) (n y : Space) (hn : ‖n‖=1) (i j : Fin 3) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor k r*DyadicKernel.dyadic k (r • n-y) i j) atTop
      (𝓝 ((k : ℂ)^2*transverse n i j*
        (Complex.exp (-Complex.I*(k : ℂ)*(@inner ℝ Space _ n y : ℂ))/(4*Real.pi)))) := by
  have h0 := ScalarFarField.scaledKernel_limit k n y hn
  have h1 := h0.const_mul ((k : ℂ)^2*transverse n i j)
  have ht := (error_limit k n y hn i j).add h1
  simp only [zero_add] at ht
  apply ht.congr'
  apply Filter.Eventually.of_forall
  intro r
  simp only [MaxwellFarField.factor,ScalarFarField.scaledKernel]
  ring

end OQ14.PointDyadicFarField

#print axioms OQ14.PointDyadicFarField.error_limit
#print axioms OQ14.PointDyadicFarField.electric_limit
