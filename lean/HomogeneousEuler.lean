import ConicalSpatialWeak

/-! Actual weak Euler identity for a locally integrable homogeneous scalar field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.HomogeneousEuler
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalSpatialTests
  OQ14.ConicalSpatialWeak
open scoped Topology

theorem euler_test_compact (ψ : Space → ℝ) (hc : HasCompactSupport ψ) :
    HasCompactSupport (fun x : Space => fderiv ℝ ψ x x) := by
  apply HasCompactSupport.intro hc
  intro x hx
  rw [fderiv_of_not_mem_tsupport ℝ hx,ContinuousLinearMap.zero_apply]

theorem weak_euler (ν : ℝ) (hν : 0 < ν) (V : Space → ℝ) (hV : LocallyIntegrable V)
    (H : Sphere → ℝ) (hH : Integrable H angularMeasure)
    (hpolar : ∀ r, 0 < r → ∀ n : Sphere, V (r • (n : Space))=r^(ν-1)*H n)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, V x*fderiv ℝ ψ x x) = -(ν+2)*(∫ x : Space, V x*ψ x) := by
  have hiL : Integrable (fun x : Space => V x*fderiv ℝ ψ x x) := by
    simpa only [smul_eq_mul] using hV.integrable_smul_right_of_hasCompactSupport
      ((hψ.continuous_fderiv le_rfl).clm_apply continuous_id) (euler_test_compact ψ hc)
  have hiR : Integrable (fun x : Space => V x*ψ x) := by
    simpa only [smul_eq_mul] using hV.integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  obtain ⟨R,hR,hcut⟩ := compact_test_radius ψ hc
  rw [PolarIntegration.integral_polar _ hiL,PolarIntegration.integral_polar _ hiR]
  have hLcut : (∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere,
      V (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (r • (n : Space)) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
        V (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (r • (n : Space)) ∂angularMeasure) := by
    apply integral_Ioi_truncate
    intro r hr
    have hz : (∫ n : Sphere, V (r • (n : Space))*fderiv ℝ ψ (r • (n : Space))
        (r • (n : Space)) ∂angularMeasure)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with n
      simp only [(hcut r hr n).2,ContinuousLinearMap.zero_apply,mul_zero,Pi.zero_apply]
    rw [hz,mul_zero]
  have hRcut : (∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere, V (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere, V (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure) := by
    apply integral_Ioi_truncate
    intro r hr
    have hz : (∫ n : Sphere, V (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure)=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with n
      simp only [(hcut r hr n).1,mul_zero,Pi.zero_apply]
    rw [hz,mul_zero]
  rw [hLcut,hRcut]
  have hLp : (∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
      V (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (r • (n : Space)) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^(ν+2)*H n*fderiv ℝ ψ (r • (n : Space)) n ∂angularMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [hpolar r hr.1 n,map_smul]
    simp only [smul_eq_mul]
    have he : r^2*r^(ν-1)*r=r^(ν+2) := by
      calc
        _ = r^(2+(ν-1))*r := by rw [Real.rpow_add hr.1,Real.rpow_two]
        _ = r^(2+(ν-1))*r^(1 : ℝ) := by rw [Real.rpow_one]
        _ = r^(ν+2) := by rw [← Real.rpow_add hr.1]; congr 1; ring
    linear_combination H n*fderiv ℝ ψ (r • (n : Space)) n*he
  have hRp : (∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere, V (r • (n : Space))*ψ (r • (n : Space)) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^(ν+1)*H n*ψ (r • (n : Space)) ∂angularMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [hpolar r hr.1 n]
    have he : r^2*r^(ν-1)=r^(ν+1) := by
      rw [← Real.rpow_two,← Real.rpow_add hr.1]
      congr 1
      ring
    linear_combination H n*ψ (r • (n : Space))*he
  rw [hLp,hRp]
  simpa only [show ν+2-1=ν+1 by ring] using
    radial_moment_ibp (ν+2) R (by linarith) hR H hH ψ hψ hc (fun n => (hcut R le_rfl n).1)

end OQ14.HomogeneousEuler

#print axioms OQ14.HomogeneousEuler.euler_test_compact
#print axioms OQ14.HomogeneousEuler.weak_euler
