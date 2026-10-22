import ConicalSpatialWeak

/-! The literal conical electric field is the actual global weak gradient of its potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalWeakGradient
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.ConicalSpatialTests OQ14.ConicalSpatialWeak OQ14.ConicalPolarTests
open scoped Topology ENNReal

theorem finite_electric_gradient (ν a t R : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) (i : Fin 3) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ)
    (hzero : ∀ n : Sphere, ψ (R • (n : Space)) = 0) :
    (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
      r^(ν+2)*field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure) =
      -(∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
        r^(ν+1)*(ν*field a t n*(n : Space) i+(gradient a t n) i)*ψ (r • (n : Space)) ∂angularMeasure) := by
  have hiH : Integrable (fun n : Sphere => field a t n*(n : Space) i) angularMeasure :=
    ConicalAngularTrial.continuous_integrable _
      ((SphereCapWeak.profile_continuous a t ha ht ht1).mul (ConicalAngularTrial.coordinate_continuous i))
  have hiG : Integrable (fun n : Sphere => (gradient a t n) i) angularMeasure := by
    have hc : Continuous (fun n : Sphere => (basis 2-(n : Space) 2 • (n : Space)) i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp
        (continuous_const.sub ((ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val))
    simpa only [SphereCapH1.gradient,PiLp.smul_apply,smul_eq_mul] using SphereCapWeak.slope_mul_integrable a t ha ht ht1 _ hc
  have hiC := power_test_integrable (ν+1) R (by linarith) hR _ hiH ψ hψ.continuous hcompact
  have hiD := power_test_integrable (ν+1) R (by linarith) hR _ hiG ψ hψ.continuous hcompact
  have hs : (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
      r^(ν+1)*(ν*field a t n*(n : Space) i+(gradient a t n) i)*ψ (r • (n : Space)) ∂angularMeasure) =
      ν*(∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^(ν+1)*(field a t n*(n : Space) i)*ψ (r • (n : Space)) ∂angularMeasure)+
        ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^(ν+1)*(gradient a t n) i*ψ (r • (n : Space)) ∂angularMeasure := by
    calc
      _ = ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
          ν*(r^(ν+1)*(field a t n*(n : Space) i)*ψ (r • (n : Space)))+
            r^(ν+1)*(gradient a t n) i*ψ (r • (n : Space)) ∂angularMeasure := by
        apply integral_congr_ae
        filter_upwards with r
        apply integral_congr_ae
        filter_upwards with n
        ring
      _ = _ := by
        rw [integral_integral_add (hiC.const_mul ν) hiD]
        simp only [integral_const_mul]
  rw [hs]
  have h := finite_gradient_moment ν a t R hν ha ht ht1 hR i ψ hψ hcompact hzero
  linarith

theorem weak_partial (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ) :
    (∫ x : Space, potential ν a t x*fderiv ℝ ψ x (basis i)) =
      -(∫ x : Space, electric ν a t x i*ψ x) := by
  have hd : Continuous (fun x : Space => fderiv ℝ ψ x (basis i)) :=
    (hψ.continuous_fderiv le_rfl).clm_apply continuous_const
  have hiL : Integrable (fun x : Space => potential ν a t x*fderiv ℝ ψ x (basis i)) := by
    simpa only [smul_eq_mul] using
      (potential_locallyIntegrable ν a t hν.le ha ht ht1).integrable_smul_right_of_hasCompactSupport hd
        (hcompact.fderiv_apply ℝ (basis i))
  have hiR : Integrable (fun x : Space => electric ν a t x i*ψ x) := by
    simpa only [smul_eq_mul] using
      (electric_component_locallyIntegrable ν a t hν.le ha ht ht1 i).integrable_smul_right_of_hasCompactSupport
        hψ.continuous hcompact
  obtain ⟨R,hR,hcut⟩ := compact_test_radius ψ hcompact
  rw [PolarIntegration.integral_polar _ hiL,PolarIntegration.integral_polar _ hiR]
  have hLcut : (∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere,
      potential ν a t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
        potential ν a t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure) := by
    apply integral_Ioi_truncate
    intro r hr
    have hz : (∫ n : Sphere, potential ν a t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with n
      simp only [(hcut r hr n).2,ContinuousLinearMap.zero_apply,mul_zero,Pi.zero_apply]
    rw [hz,mul_zero]
  have hRcut : (∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere,
      electric ν a t (r • (n : Space)) i*ψ (r • (n : Space)) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
        electric ν a t (r • (n : Space)) i*ψ (r • (n : Space)) ∂angularMeasure) := by
    apply integral_Ioi_truncate
    intro r hr
    have hz : (∫ n : Sphere, electric ν a t (r • (n : Space)) i*ψ (r • (n : Space)) ∂angularMeasure) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with n
      simp only [(hcut r hr n).1,mul_zero,Pi.zero_apply]
    rw [hz,mul_zero]
  rw [hLcut,hRcut]
  have hLp : (∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
      potential ν a t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
        r^(ν+2)*field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [potential_polar ν a t r hr.1 n]
    have he : r^2*r^ν = r^(ν+2) := by rw [Real.rpow_add hr.1,Real.rpow_two]; ring
    linear_combination field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i)*he
  have hRp : (∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
      electric ν a t (r • (n : Space)) i*ψ (r • (n : Space)) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
        r^(ν+1)*(ν*field a t n*(n : Space) i+(gradient a t n) i)*ψ (r • (n : Space)) ∂angularMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [electric_polar ν a t r hr.1 n]
    simp only [angularElectric,PiLp.smul_apply,PiLp.add_apply,smul_eq_mul]
    have he : r^2*r^(ν-1) = r^(ν+1) := by
      rw [show ν+1=(ν-1)+2 by ring,Real.rpow_add hr.1,Real.rpow_two]
      ring
    linear_combination (ν*field a t n*(n : Space) i+(gradient a t n) i)*ψ (r • (n : Space))*he
  rw [hLp,hRp]
  exact finite_electric_gradient ν a t R hν ha ht ht1 hR i ψ hψ hcompact (fun n => (hcut R le_rfl n).1)

end OQ14.ConicalWeakGradient

#print axioms OQ14.ConicalWeakGradient.finite_electric_gradient
#print axioms OQ14.ConicalWeakGradient.weak_partial
