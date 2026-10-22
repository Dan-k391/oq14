import ConicalRadialTests

/-! Actual rescaled ambient tests in the geometric sphere distribution identities. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalAngularTests
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
open scoped Topology

theorem scaled_test_contDiff (r : ℝ) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    ContDiff ℝ 1 (fun x : Space => ψ (r • x)) :=
  hψ.comp (contDiff_const.smul contDiff_id)

theorem scaled_test_fderiv (r : ℝ) (ψ : Space → ℝ) (hψ : Differentiable ℝ ψ) (x v : Space) :
    fderiv ℝ (fun y : Space => ψ (r • y)) x v = r*fderiv ℝ ψ (r • x) v := by
  have hc : HasFDerivAt (fun y : Space => r • y) (r • ContinuousLinearMap.id ℝ Space) x := by
    simpa using (r • ContinuousLinearMap.id ℝ Space).hasFDerivAt (x := x)
  have h := (hψ (r • x)).hasFDerivAt.comp x hc
  change HasFDerivAt (fun y : Space => ψ (r • y)) _ x at h
  rw [h.fderiv,ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]

theorem scaled_surface_ibp (a t r : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ n : Sphere, (gradient a t n) i*ψ (r • (n : Space)) ∂angularMeasure) =
    -(∫ n : Sphere, field a t n*(r*fderiv ℝ ψ (r • (n : Space))
      (basis i-(n : Space) i • (n : Space))-2*(n : Space) i*ψ (r • (n : Space))) ∂angularMeasure) := by
  have h := (field_hasWeakTangentialGradient a t ha ht ht1).2 i
    (fun x : Space => ψ (r • x)) (scaled_test_contDiff r ψ hψ)
  simpa only [scaled_test_fderiv r ψ (hψ.differentiable le_rfl)] using h

theorem scaled_weighted_weak (a d t r : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hr : CapAngularShooting.determinant d t a = 0)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    r*(∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ (r • (n : Space)) (gradient a t n) ∂angularMeasure) =
    a*∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      (field a t n*ψ (r • (n : Space))) ∂angularMeasure := by
  have h := field_weighted_weak a d t ha ht ht1 hr (fun x : Space => ψ (r • x))
    (scaled_test_contDiff r ψ hψ)
  simp only [scaled_test_fderiv r ψ (hψ.differentiable le_rfl)] at h
  rw [← integral_const_mul]
  convert h using 1
  congr 1
  funext n
  ring

end OQ14.ConicalAngularTests

#print axioms OQ14.ConicalAngularTests.scaled_test_contDiff
#print axioms OQ14.ConicalAngularTests.scaled_test_fderiv
#print axioms OQ14.ConicalAngularTests.scaled_surface_ibp
#print axioms OQ14.ConicalAngularTests.scaled_weighted_weak
