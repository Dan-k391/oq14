import ConicalWeakGradient

/-! Actual angular and radial transmission cancellation for conical electric fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalDivergenceTests
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.ConicalSpatialTests OQ14.ConicalSpatialWeak
  OQ14.ConicalPolarTests OQ14.ConicalAngularTests
open scoped Topology ENNReal

theorem angular_electric_trace (ν a d t r : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    r*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ (r • (n : Space)) (angularElectric ν a t n) ∂angularMeasure) =
    ν*r*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      field a t n*fderiv ℝ ψ (r • (n : Space)) n ∂angularMeasure)+
    a*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      field a t n*ψ (r • (n : Space)) ∂angularMeasure) := by
  have hiA := SphereCapWeak.coefficient_integrable _
    (ConicalAngularTrial.continuous_integrable _ ((SphereCapWeak.profile_continuous a t ha ht ht1).mul
      (spherical_derivative_continuous r ψ hψ (fun n => (n : Space)) continuous_subtype_val))) d t
  have hc : Continuous (fun n : Sphere => fderiv ℝ ψ (r • (n : Space))
      (basis 2-(n : Space) 2 • (n : Space))) :=
    spherical_derivative_continuous r ψ hψ _
      (continuous_const.sub ((ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val))
  have hiG : Integrable (fun n : Sphere => CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ (r • (n : Space)) (SphereCapH1.gradient a t n)) angularMeasure := by
    simpa only [SphereCapH1.gradient,map_smul,smul_eq_mul] using
      SphereCapWeak.coefficient_integrable _ (SphereCapWeak.slope_mul_integrable a t ha ht ht1 _ hc) d t
  have he : (fun n : Sphere => CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ (r • (n : Space)) (angularElectric ν a t n)) =
      fun n : Sphere => ν*(CapSturmLiouville.coefficient d t ((n : Space) 2)*field a t n*
        fderiv ℝ ψ (r • (n : Space)) n)+CapSturmLiouville.coefficient d t ((n : Space) 2)*
        fderiv ℝ ψ (r • (n : Space)) (SphereCapH1.gradient a t n) := by
    funext n
    simp only [angularElectric,map_add,map_smul,smul_eq_mul]
    ring
  have hiA' : Integrable (fun n : Sphere => CapSturmLiouville.coefficient d t ((n : Space) 2)*
      field a t n*fderiv ℝ ψ (r • (n : Space)) n) angularMeasure := by
    simpa only [field,mul_assoc] using hiA
  rw [he,integral_add (hiA'.const_mul ν) hiG,integral_const_mul]
  have h := scaled_weighted_weak a d t r ha ht ht1 hroot ψ hψ
  simp only [mul_assoc] at h ⊢
  linear_combination h

theorem finite_divergence_moment (ν a d t R : ℝ) (hν : 0 < ν)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    (hroot : CapAngularShooting.determinant d t a = 0) (heq : ν*(ν+1) = a)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ)
    (hzero : ∀ n : Sphere, ψ (R • (n : Space)) = 0) :
    (∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
      r^(ν+1)*CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ (r • (n : Space)) (angularElectric ν a t n) ∂angularMeasure) = 0 := by
  let H : Sphere → ℝ := fun n => CapSturmLiouville.coefficient d t ((n : Space) 2)*field a t n
  have hH : Integrable H angularMeasure := SphereCapWeak.coefficient_integrable _
    (ConicalAngularTrial.continuous_integrable _ (SphereCapWeak.profile_continuous a t ha ht ht1)) d t
  let B : ℝ → ℝ := fun r => ∫ n : Sphere, r^(ν+1)*H n*fderiv ℝ ψ (r • (n : Space)) n ∂angularMeasure
  let C : ℝ → ℝ := fun r => ∫ n : Sphere, r^ν*H n*ψ (r • (n : Space)) ∂angularMeasure
  have hiPow : IntegrableOn (fun r : ℝ => r^(ν+1)) (Ioo (0 : ℝ) R) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hR.le).mp
      (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < ν+1))
  have hiB : IntegrableOn B (Ioo (0 : ℝ) R) :=
    (derivative_product_integrable R _ hiPow H hH (fun n : Sphere => (n : Space)) continuous_subtype_val ψ hψ hcompact).integral_prod_left
  have hiC : IntegrableOn C (Ioo (0 : ℝ) R) :=
    (power_test_integrable ν R (by linarith) hR H hH ψ hψ.continuous hcompact).integral_prod_left
  have htrace (r : ℝ) (hr : 0 < r) :
      (∫ n : Sphere, r^(ν+1)*CapSturmLiouville.coefficient d t ((n : Space) 2)*
        fderiv ℝ ψ (r • (n : Space)) (angularElectric ν a t n) ∂angularMeasure) = ν*B r+a*C r := by
    have he : r^(ν+1)=r^ν*r := by rw [Real.rpow_add hr,Real.rpow_one]
    have h := congrArg (fun x : ℝ => r^ν*x) (angular_electric_trace ν a d t r ha ht ht1 hroot ψ hψ)
    dsimp only [B,C,H]
    simp_rw [mul_assoc,integral_const_mul] at h ⊢
    rw [he]
    linear_combination h
  have hm := radial_moment_ibp (ν+1) R (by linarith) hR H hH ψ hψ hcompact hzero
  have hBC : (∫ r in Ioo (0 : ℝ) R, B r) = -(ν+1)*(∫ r in Ioo (0 : ℝ) R, C r) := by
    simpa only [B,C,show ν+1-1=ν by ring] using hm
  calc
    _ = ∫ r in Ioo (0 : ℝ) R, (ν • B+a • C) r := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] using htrace r hr.1
    _ = ν*(∫ r in Ioo (0 : ℝ) R, B r)+a*(∫ r in Ioo (0 : ℝ) R, C r) := by
      rw [integral_add' (hiB.smul ν) (hiC.smul a)]
      simp only [Pi.smul_apply,smul_eq_mul,integral_const_mul]
    _ = 0 := by rw [hBC,← heq]; ring

end OQ14.ConicalDivergenceTests

#print axioms OQ14.ConicalDivergenceTests.angular_electric_trace
#print axioms OQ14.ConicalDivergenceTests.finite_divergence_moment
