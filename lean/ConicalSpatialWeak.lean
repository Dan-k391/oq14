import ConicalSpatialTests

/-! Genuine radial/angular identities for the spatial weak conical gradient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalSpatialWeak
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.ConicalRadialTests OQ14.ConicalPolarTests
  OQ14.ConicalAngularTests OQ14.ConicalSpatialTests
open scoped Topology ENNReal

theorem spherical_derivative_continuous (r : ℝ) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (V : Sphere → Space) (hV : Continuous V) :
    Continuous (fun n : Sphere => fderiv ℝ ψ (r • (n : Space)) (V n)) :=
  ((hψ.continuous_fderiv le_rfl).comp (f := fun n : Sphere => r • (n : Space))
    (continuous_const.smul continuous_subtype_val)).clm_apply hV

theorem angular_gradient_trace (a t r : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    r*(∫ n : Sphere, field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure) =
      r*(∫ n : Sphere, field a t n*(n : Space) i*fderiv ℝ ψ (r • (n : Space)) n ∂angularMeasure)+
      2*(∫ n : Sphere, field a t n*(n : Space) i*ψ (r • (n : Space)) ∂angularMeasure)-
      ∫ n : Sphere, (gradient a t n) i*ψ (r • (n : Space)) ∂angularMeasure := by
  have hc := SphereCapWeak.profile_continuous a t ha ht ht1
  have hcoord : Continuous (fun n : Sphere => (n : Space) i) := ConicalAngularTrial.coordinate_continuous i
  have hiA : Integrable (fun n : Sphere => field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i)) angularMeasure :=
    ConicalAngularTrial.continuous_integrable _
    (hc.mul (spherical_derivative_continuous r ψ hψ (fun _ => basis i) continuous_const))
  have hiB : Integrable (fun n : Sphere => field a t n*(n : Space) i*fderiv ℝ ψ (r • (n : Space)) n) angularMeasure :=
    ConicalAngularTrial.continuous_integrable _
    ((hc.mul hcoord).mul (spherical_derivative_continuous r ψ hψ (fun n => (n : Space)) continuous_subtype_val))
  have hiC : Integrable (fun n : Sphere => field a t n*(n : Space) i*ψ (r • (n : Space))) angularMeasure :=
    ConicalAngularTrial.continuous_integrable _
    ((hc.mul hcoord).mul (hψ.continuous.comp (f := fun n : Sphere => r • (n : Space))
      (continuous_const.smul continuous_subtype_val)))
  have he : (fun n : Sphere => field a t n*(r*fderiv ℝ ψ (r • (n : Space))
      (basis i-(n : Space) i • (n : Space))-2*(n : Space) i*ψ (r • (n : Space)))) =
      fun n : Sphere => r*(field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i))-
        r*(field a t n*(n : Space) i*fderiv ℝ ψ (r • (n : Space)) n)-
        2*(field a t n*(n : Space) i*ψ (r • (n : Space))) := by
    funext n
    rw [map_sub,map_smul]
    simp only [smul_eq_mul]
    ring
  have h := scaled_surface_ibp a t r ha ht ht1 i ψ hψ
  have hI := integral_sub ((hiA.const_mul r).sub (hiB.const_mul r)) (hiC.const_mul 2)
  simp only [Pi.sub_apply] at hI
  rw [he,hI,integral_sub (hiA.const_mul r) (hiB.const_mul r),
    integral_const_mul,integral_const_mul,integral_const_mul] at h
  linarith

theorem radial_moment_ibp (β R : ℝ) (hβ : 0 < β) (hR : 0 < R)
    (H : Sphere → ℝ) (hH : Integrable H angularMeasure) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ)
    (hzero : ∀ n : Sphere, ψ (R • (n : Space)) = 0) :
    (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^β*H n*fderiv ℝ ψ (r • (n : Space)) n ∂angularMeasure) =
      -β*(∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere, r^(β-1)*H n*ψ (r • (n : Space)) ∂angularMeasure) := by
  rw [power_derivative_swap β R (by linarith) hR H hH (fun n => (n : Space)) continuous_subtype_val ψ hψ hcompact,
    power_test_swap (β-1) R (by linarith) hR H hH ψ hψ.continuous hcompact,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with n
  have h := radial_test_ibp β R hβ hR ψ hψ n (hzero n)
  simp only [intervalIntegral.integral_of_le hR.le,integral_Ioc_eq_integral_Ioo] at h
  have hL : (∫ r in Ioo (0 : ℝ) R, r^β*H n*fderiv ℝ ψ (r • (n : Space)) n) =
      H n*(∫ r in Ioo (0 : ℝ) R, r^β*fderiv ℝ ψ (r • (n : Space)) n) := by
    rw [← integral_const_mul]
    congr 1
    funext r
    ring
  have hR' : (∫ r in Ioo (0 : ℝ) R, r^(β-1)*H n*ψ (r • (n : Space))) =
      H n*(∫ r in Ioo (0 : ℝ) R, r^(β-1)*ψ (r • (n : Space))) := by
    rw [← integral_const_mul]
    congr 1
    funext r
    ring
  rw [hL,hR',h]
  ring

theorem finite_gradient_moment (ν a t R : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) (i : Fin 3) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ)
    (hzero : ∀ n : Sphere, ψ (R • (n : Space)) = 0) :
    (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
      r^(ν+2)*field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure) =
    -ν*(∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
      r^(ν+1)*(field a t n*(n : Space) i)*ψ (r • (n : Space)) ∂angularMeasure)-
    ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
      r^(ν+1)*(gradient a t n) i*ψ (r • (n : Space)) ∂angularMeasure := by
  let A : ℝ → ℝ := fun r => ∫ n : Sphere, r^(ν+2)*field a t n*fderiv ℝ ψ (r • (n : Space)) (basis i) ∂angularMeasure
  let B : ℝ → ℝ := fun r => ∫ n : Sphere, r^(ν+2)*(field a t n*(n : Space) i)*fderiv ℝ ψ (r • (n : Space)) n ∂angularMeasure
  let C : ℝ → ℝ := fun r => ∫ n : Sphere, r^(ν+1)*(field a t n*(n : Space) i)*ψ (r • (n : Space)) ∂angularMeasure
  let D : ℝ → ℝ := fun r => ∫ n : Sphere, r^(ν+1)*(gradient a t n) i*ψ (r • (n : Space)) ∂angularMeasure
  have hiH : Integrable (fun n : Sphere => field a t n*(n : Space) i) angularMeasure :=
    ConicalAngularTrial.continuous_integrable _
      ((SphereCapWeak.profile_continuous a t ha ht ht1).mul (ConicalAngularTrial.coordinate_continuous i))
  have hiG : Integrable (fun n : Sphere => (gradient a t n) i) angularMeasure := by
    have hc : Continuous (fun n : Sphere => (basis 2-(n : Space) 2 • (n : Space)) i) :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).continuous.comp
        (continuous_const.sub ((ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val))
    simpa only [SphereCapH1.gradient,PiLp.smul_apply,smul_eq_mul] using SphereCapWeak.slope_mul_integrable a t ha ht ht1 _ hc
  have hiPow : IntegrableOn (fun r : ℝ => r^(ν+2)) (Ioo (0 : ℝ) R) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < ν+2))
  have hiB : IntegrableOn B (Ioo (0 : ℝ) R) :=
    (derivative_product_integrable R _ hiPow _ hiH (fun n : Sphere => (n : Space)) continuous_subtype_val ψ hψ hcompact).integral_prod_left
  have hiC : IntegrableOn C (Ioo (0 : ℝ) R) :=
    (power_test_integrable (ν+1) R (by linarith) hR _ hiH ψ hψ.continuous hcompact).integral_prod_left
  have hiD : IntegrableOn D (Ioo (0 : ℝ) R) :=
    (power_test_integrable (ν+1) R (by linarith) hR _ hiG ψ hψ.continuous hcompact).integral_prod_left
  have htrace (r : ℝ) (hr : 0 < r) : A r = B r+2*C r-D r := by
    have he : r^(ν+2) = r^(ν+1)*r := by
      calc
        r^(ν+2) = r^((ν+1)+1) := by congr 1; ring
        _ = r^(ν+1)*r := by rw [Real.rpow_add hr,Real.rpow_one]
    have h := congrArg (fun x : ℝ => r^(ν+1)*x) (angular_gradient_trace a t r ha ht ht1 i ψ hψ)
    dsimp only [A,B,C,D]
    simp_rw [mul_assoc,integral_const_mul] at h ⊢
    rw [he]
    linear_combination h
  have hAB : (∫ r in Ioo (0 : ℝ) R, A r) = ∫ r in Ioo (0 : ℝ) R, (B+(2 : ℝ) • C-D) r := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    simpa only [Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul] using htrace r hr.1
  rw [integral_sub' (hiB.add (hiC.smul (2 : ℝ))) hiD,
    integral_add' hiB (hiC.smul (2 : ℝ))] at hAB
  simp only [Pi.smul_apply,integral_smul] at hAB
  have hBC : (∫ r in Ioo (0 : ℝ) R, B r) = -(ν+2)*(∫ r in Ioo (0 : ℝ) R, C r) := by
    have h := radial_moment_ibp (ν+2) R (by linarith) hR _ hiH ψ hψ hcompact hzero
    simpa only [B,C,show ν+2-1=ν+1 by ring] using h
  change (∫ r in Ioo (0 : ℝ) R, A r) = -ν*(∫ r in Ioo (0 : ℝ) R, C r)-∫ r in Ioo (0 : ℝ) R, D r
  simp only [smul_eq_mul] at hAB
  linear_combination hAB+hBC

end OQ14.ConicalSpatialWeak

#print axioms OQ14.ConicalSpatialWeak.spherical_derivative_continuous
#print axioms OQ14.ConicalSpatialWeak.angular_gradient_trace
#print axioms OQ14.ConicalSpatialWeak.radial_moment_ibp
#print axioms OQ14.ConicalSpatialWeak.finite_gradient_moment
