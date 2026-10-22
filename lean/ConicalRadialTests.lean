import ConicalCapField
import PolarIntegration

/-! Genuine radial test derivatives and origin boundary cancellation for conical fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalRadialTests
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower
open scoped Topology

theorem rpow_test_ibp (β R : ℝ) (hβ : 0 < β) (hR : 0 < R)
    (v vD : ℝ → ℝ) (hv : ∀ r : ℝ, HasDerivAt v (vD r) r) (hD : Continuous vD)
    (hzero : v R = 0) :
    (∫ r in (0 : ℝ)..R, r^β*vD r) = -β*∫ r in (0 : ℝ)..R, r^(β-1)*v r := by
  have hc : Continuous v := continuous_iff_continuousAt.mpr (fun r => (hv r).continuousAt)
  have hi : IntervalIntegrable (fun r : ℝ => β*r^(β-1)) volume 0 R :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < β-1)).const_mul β
  have hr : ∀ r ∈ Ioo (min (0 : ℝ) R) (max 0 R), HasDerivAt (fun r : ℝ => r^β) (β*r^(β-1)) r := by
    intro r hr
    have hp : 0 < r := by simpa only [min_eq_left hR.le] using hr.1
    exact Real.hasDerivAt_rpow_const (Or.inl hp.ne')
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := R) (u := fun r : ℝ => r^β) (u' := fun r => β*r^(β-1))
    (v := v) (v' := vD) (Real.continuous_rpow_const hβ.le).continuousOn hc.continuousOn
    hr (fun r _ => hv r) hi (hD.intervalIntegrable _ _)
  rw [h]
  dsimp only
  rw [hzero,Real.zero_rpow hβ.ne',mul_zero,zero_mul,sub_self,zero_sub]
  simp only [mul_assoc,intervalIntegral.integral_const_mul]
  ring

theorem radial_test_hasDerivAt (ψ : Space → ℝ) (hψ : Differentiable ℝ ψ)
    (n : Sphere) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (s • (n : Space))) (fderiv ℝ ψ (r • (n : Space)) n) r := by
  have hn : HasDerivAt (fun s : ℝ => s • (n : Space)) (n : Space) r := by
    simpa using (hasDerivAt_id r).smul_const (n : Space)
  exact (hψ _).hasFDerivAt.comp_hasDerivAt r hn

theorem radial_test_derivative_continuous (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (n : Sphere) :
    Continuous (fun r : ℝ => fderiv ℝ ψ (r • (n : Space)) n) :=
  ((hψ.continuous_fderiv le_rfl).comp (f := fun r : ℝ => r • (n : Space))
    (continuous_id.smul continuous_const)).clm_apply continuous_const

theorem radial_test_ibp (β R : ℝ) (hβ : 0 < β) (hR : 0 < R)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (n : Sphere) (hzero : ψ (R • (n : Space)) = 0) :
    (∫ r in (0 : ℝ)..R, r^β*fderiv ℝ ψ (r • (n : Space)) n) =
      -β*∫ r in (0 : ℝ)..R, r^(β-1)*ψ (r • (n : Space)) :=
  rpow_test_ibp β R hβ hR _ _ (radial_test_hasDerivAt ψ (hψ.differentiable le_rfl) n)
    (radial_test_derivative_continuous ψ hψ n) hzero

end OQ14.ConicalRadialTests

#print axioms OQ14.ConicalRadialTests.rpow_test_ibp
#print axioms OQ14.ConicalRadialTests.radial_test_hasDerivAt
#print axioms OQ14.ConicalRadialTests.radial_test_derivative_continuous
#print axioms OQ14.ConicalRadialTests.radial_test_ibp
