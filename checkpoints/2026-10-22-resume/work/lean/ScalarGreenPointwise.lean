import ScalarGreenAngularBound
import ScalarGreenExpansion

/-! Pointwise free Green identification from actual coefficients and genuine angular convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarGreenPointwise
open MeasureTheory Set Metric Complex OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.SphereHarmonicBasis OQ14.SphereHarmonicHilbert OQ14.ScalarGreenAngularBound
  OQ14.ScalarGreenRadialBound OQ14.ScalarGreenMoment

def modeSlice (k r s : ℝ) (m : Sphere) (a : TotalIndex) : C(Sphere,ℂ) :=
  (modeMap a k r s).comp ⟨fun n => (n,m),continuous_id.prodMk continuous_const⟩

theorem modeSlice_bound (k r s : ℝ) (m : Sphere) (a : TotalIndex) :
    ‖modeSlice k r s m a‖ ≤ ‖modeMap a k r s‖ := by
  rw [(modeSlice k r s m a).norm_le (norm_nonneg _)]
  intro n
  exact (modeMap a k r s).norm_coe_le_norm (n,m)

theorem modeSlice_summable (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s) (m : Sphere) :
    Summable (modeSlice k r s m) := by
  have hs := hr.trans hrs
  apply Summable.of_norm_bounded (f := modeSlice k r s m)
    (indexMajorant (Real.exp ((k*r)^2/2+k*s)/(s*angularMeasure.real Set.univ)) (r/s) 3)
    (indexMajorant_summable _ _ 3 (by positivity) (div_pos hr hs) ((div_lt_one hs).mpr hrs))
  intro a
  exact (modeSlice_bound k r s m a).trans (modeMap_bound a k r s hk hr hs)

theorem source_ray_norm (s : ℝ) (hs : 0 < s) (m : Sphere) : ‖s • (m : Space)‖=s := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs,AngularPower.sphere_norm,mul_one]

theorem source_ray_coefficient (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s)
    (m : Sphere) (a : TotalIndex) :
    ScalarGreenExpansion.modeCoefficient k (s • (m : Space)) r a=
      radialFactor a.1 k r s*(angular a.1 a.2 m : ℂ) := by
  have hs := hr.trans hrs
  have hk0 : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  simp only [ScalarGreenExpansion.modeCoefficient,source_ray_norm s hs m,min_eq_left hrs.le,max_eq_right hrs.le]
  rw [FischerDecomposition.complexEvaluate_smul (representative a.1 a.2) a.1
    (representative_homogeneous a.1 a.2) s (m : Space)]
  simp only [
    ScalarGreenJump.innerProfile,ScalarGreenJump.outerProfile,RadialQuotient.profile,
    RadialOriginSelection.regular,RadialRellich.outgoing,pow_one,radialFactor,ofReal_mul,
    angular,SpherePolynomial.polynomialMap_apply,complexEvaluate,evaluate]
  field_simp [hk0,hr0,hs0]
  ring

theorem modeSlice_toLp (k r s : ℝ) (m : Sphere) (a : TotalIndex) :
    ContinuousMap.toLp 2 angularMeasure ℂ (modeSlice k r s m a)=
      (radialFactor a.1 k r s*(angular a.1 a.2 m : ℂ)) • ComplexHarmonicBasis.vector a := by
  have he : modeSlice k r s m a=
      (radialFactor a.1 k r s*(angular a.1 a.2 m : ℂ)) • ComplexHarmonicBasis.complexAngular a := by
    ext n
    simp only [modeSlice,ContinuousMap.comp_apply,modeMap,ContinuousMap.coe_mk,
      ContinuousMap.smul_apply,ComplexHarmonicBasis.complexAngular,smul_eq_mul]
    ring
  rw [he,map_smul,← ComplexHarmonicBasis.vector_toLp]

theorem actual_kernel_hasSum (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s) (m : Sphere) :
    HasSum (modeSlice k r s m)
      (ScalarGreenExpansion.angularKernel k (s • (m : Space)) r hr
        (by rw [source_ray_norm s (hr.trans hrs) m];exact hrs.ne)) := by
  have hs := hr.trans hrs
  have hy : s • (m : Space) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [source_ray_norm s hs m]
    exact hs
  apply ContinuousMap.hasSum_of_hasSum_Lp (p := 2) (μ := angularMeasure) (𝕜 := ℂ)
    (modeSlice_summable k r s hk hr hrs m)
  simpa only [Function.comp_def,modeSlice_toLp,← source_ray_coefficient k r s hk hr hrs m] using
    ScalarGreenExpansion.actual_kernel_expansion k hk (s • (m : Space)) hy r hr
      (by rw [source_ray_norm s hs m];exact hrs.ne)

theorem actual_pointwise_expansion (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s)
    (n m : Sphere) :
    HasSum (fun a : TotalIndex => radialFactor a.1 k r s*
      ((angular a.1 a.2 n : ℂ)*(angular a.1 a.2 m : ℂ)))
      (GreenKernel.phi k (r • (n : Space)-s • (m : Space))) := by
  have h := (ContinuousMap.evalCLM ℂ n).hasSum (actual_kernel_hasSum k r s hk hr hrs m)
  simpa only [ContinuousMap.evalCLM_apply,modeSlice,ContinuousMap.comp_apply,modeMap,
    ContinuousMap.coe_mk,ScalarGreenExpansion.angularKernel,kernel] using h


theorem joint_sum_value (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s) (n m : Sphere) :
    (∑' a : TotalIndex,modeMap a k r s) (n,m)=
      GreenKernel.phi k (r • (n : Space)-s • (m : Space)) := by
  have he := (ContinuousMap.evalCLM ℂ (n,m)).map_tsum (actual_modes_summable k r s hk hr hrs)
  calc
    _ = ∑' a : TotalIndex,radialFactor a.1 k r s*
        ((angular a.1 a.2 n : ℂ)*(angular a.1 a.2 m : ℂ)) := by
      simpa only [ContinuousMap.evalCLM_apply,modeMap,ContinuousMap.coe_mk] using he
    _ = _ := (actual_pointwise_expansion k r s hk hr hrs n m).tsum_eq

def actualKernel (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s) : C(Sphere × Sphere,ℂ) where
  toFun p := GreenKernel.phi k (r • (p.1 : Space)-s • (p.2 : Space))
  continuous_toFun := by
    have he : (fun p : Sphere × Sphere => GreenKernel.phi k (r • (p.1 : Space)-s • (p.2 : Space)))=
        fun p => (∑' a : TotalIndex,modeMap a k r s) p :=
      funext (fun p => (joint_sum_value k r s hk hr hrs p.1 p.2).symm)
    rw [he]
    exact (∑' a : TotalIndex,modeMap a k r s).continuous

theorem actual_joint_kernel_hasSum (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s) :
    HasSum (fun a : TotalIndex => modeMap a k r s) (actualKernel k r s hk hr hrs) := by
  have he : (∑' a : TotalIndex,modeMap a k r s)=actualKernel k r s hk hr hrs := by
    ext p
    exact joint_sum_value k r s hk hr hrs p.1 p.2
  rw [← he]
  exact (actual_modes_summable k r s hk hr hrs).hasSum

end OQ14.ScalarGreenPointwise

#print axioms OQ14.ScalarGreenPointwise.modeSlice_bound

#print axioms OQ14.ScalarGreenPointwise.modeSlice_summable

#print axioms OQ14.ScalarGreenPointwise.source_ray_norm

#print axioms OQ14.ScalarGreenPointwise.source_ray_coefficient

#print axioms OQ14.ScalarGreenPointwise.modeSlice_toLp

#print axioms OQ14.ScalarGreenPointwise.actual_kernel_hasSum

#print axioms OQ14.ScalarGreenPointwise.actual_pointwise_expansion

#print axioms OQ14.ScalarGreenPointwise.joint_sum_value

#print axioms OQ14.ScalarGreenPointwise.actual_joint_kernel_hasSum
