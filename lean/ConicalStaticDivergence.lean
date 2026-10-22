import ConicalDivergenceTests

/-! Actual global static transmission divergence for the literal conical field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalStaticDivergence
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.ConicalSpatialTests OQ14.ConicalDivergenceTests
open scoped Topology ENNReal

theorem permittivity_integrable (d t : ℝ) (f : Space → ℝ) (hf : Integrable f) :
    Integrable (fun x => permittivity d t x*f x) := by
  let S : Set Space := {x | t < |(unit x : Space) 2|}
  have hm : Measurable (fun x : Space => (unit x : Space) 2) :=
    (ConicalAngularTrial.coordinate_continuous 2).measurable.comp unit_measurable
  have hS : MeasurableSet S := measurableSet_lt measurable_const (continuous_abs.measurable.comp hm)
  have he : (fun x : Space => permittivity d t x*f x) = f+d • S.indicator f := by
    funext x
    by_cases hx : x ∈ S
    · have hx' : t < |(unit x : Space) 2| := hx
      simp only [permittivity,CapSturmLiouville.coefficient,if_neg (not_le.mpr hx'),
        Pi.add_apply,Pi.smul_apply,indicator_of_mem hx,smul_eq_mul]
      ring
    · have hx' : |(unit x : Space) 2| ≤ t := le_of_not_gt hx
      simp only [permittivity,CapSturmLiouville.coefficient,if_pos hx',
        Pi.add_apply,Pi.smul_apply,indicator_of_not_mem hx,smul_eq_mul,mul_zero,add_zero,one_mul]
  rw [he]
  exact hf.add ((hf.indicator hS).smul d)

theorem electric_test_integrable (ν a d t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hcompact : HasCompactSupport ψ) :
    Integrable (fun x => permittivity d t x*fderiv ℝ ψ x (electric ν a t x)) := by
  have he (x : Space) : fderiv ℝ ψ x (electric ν a t x) =
      ∑ i : Fin 3, electric ν a t x i*fderiv ℝ ψ x (basis i) := by
    have hv : (∑ i : Fin 3, electric ν a t x i • basis i) = electric ν a t x := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr (electric ν a t x)
    conv_lhs => rw [← hv,map_sum]
    simp only [map_smul,smul_eq_mul]
  apply permittivity_integrable
  have hi (i : Fin 3) : Integrable (fun x => electric ν a t x i*fderiv ℝ ψ x (basis i)) := by
    simpa only [smul_eq_mul] using
      (electric_component_locallyIntegrable ν a t hν ha ht ht1 i).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hcompact.fderiv_apply ℝ (basis i))
  simpa only [he] using integrable_finset_sum Finset.univ (fun i _ => hi i)

theorem weak_divergence (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1) = a) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hcompact : HasCompactSupport ψ) :
    (∫ x : Space, permittivity d t x*fderiv ℝ ψ x (electric ν a t x)) = 0 := by
  have hi := electric_test_integrable ν a d t hν.le ha ht ht1 ψ hψ hcompact
  obtain ⟨R,hR,hcut⟩ := compact_test_radius ψ hcompact
  rw [PolarIntegration.integral_polar _ hi]
  have hcutI : (∫ r in Ioi (0 : ℝ), r^2*(∫ n : Sphere,
      permittivity d t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space))
        (electric ν a t (r • (n : Space))) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
        permittivity d t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space))
          (electric ν a t (r • (n : Space))) ∂angularMeasure) := by
    apply integral_Ioi_truncate
    intro r hr
    have hz : (∫ n : Sphere, permittivity d t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space))
        (electric ν a t (r • (n : Space))) ∂angularMeasure) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards with n
      simp only [(hcut r hr n).2,ContinuousLinearMap.zero_apply,mul_zero,Pi.zero_apply]
    rw [hz,mul_zero]
  rw [hcutI]
  have hp : (∫ r in Ioo (0 : ℝ) R, r^2*(∫ n : Sphere,
      permittivity d t (r • (n : Space))*fderiv ℝ ψ (r • (n : Space))
        (electric ν a t (r • (n : Space))) ∂angularMeasure)) =
      ∫ r in Ioo (0 : ℝ) R, ∫ n : Sphere,
        r^(ν+1)*CapSturmLiouville.coefficient d t ((n : Space) 2)*
          fderiv ℝ ψ (r • (n : Space)) (angularElectric ν a t n) ∂angularMeasure := by
    apply setIntegral_congr_fun measurableSet_Ioo
    intro r hr
    dsimp only
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with n
    rw [permittivity_polar d t r hr.1 n,electric_polar ν a t r hr.1 n,map_smul]
    simp only [smul_eq_mul]
    have he : r^2*r^(ν-1)=r^(ν+1) := by
      rw [show ν+1=(ν-1)+2 by ring,Real.rpow_add hr.1,Real.rpow_two]
      ring
    linear_combination CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ (r • (n : Space)) (angularElectric ν a t n)*he
  rw [hp]
  exact finite_divergence_moment ν a d t R hν ha ht ht1 hR hroot heq ψ hψ hcompact
    (fun n => (hcut R le_rfl n).1)

theorem shooting_weak_divergence (a d t : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hcompact : HasCompactSupport ψ) :
    (∫ x : Space, permittivity d t x*fderiv ℝ ψ x (electric (CapAngularShooting.exponent a) a t x)) = 0 :=
  weak_divergence _ a d t (CapAngularShooting.exponent_range a ha).1 ⟨ha.1.le,ha.2.le⟩ ht ht1 hroot
    (CapAngularShooting.exponent_equation a ha.1.le) ψ hψ hcompact

end OQ14.ConicalStaticDivergence

#print axioms OQ14.ConicalStaticDivergence.permittivity_integrable
#print axioms OQ14.ConicalStaticDivergence.electric_test_integrable
#print axioms OQ14.ConicalStaticDivergence.weak_divergence
#print axioms OQ14.ConicalStaticDivergence.shooting_weak_divergence
