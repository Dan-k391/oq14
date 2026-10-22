import ScalarGreenNormalization
import ComplexHarmonicBasis

/-! Genuine angular L2 expansion of the physical scalar Green kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarGreenExpansion
open MeasureTheory Set OQ14.Maxwell OQ14.HarmonicPolynomial
  OQ14.ScalarGreenMoment OQ14.ScalarGreenNormalization OQ14.ScalarGreenJump
  OQ14.SphereHarmonicBasis OQ14.SphereHarmonicOrthogonality OQ14.SphereHarmonicHilbert

theorem sphere_source_avoided (y : Space) (r : ℝ) (hr : 0 < r) (hry : r ≠ ‖y‖)
    (n : Sphere) : r • (n : Space) ≠ y := by
  intro he
  have hn := congrArg norm he
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,OQ14.AngularPower.sphere_norm,mul_one] at hn
  exact hry hn

def angularKernel (k : ℝ) (y : Space) (r : ℝ) (hr : 0 < r) (hry : r ≠ ‖y‖) : C(Sphere,ℂ) where
  toFun n := kernel k y (r • (n : Space))
  continuous_toFun := by
    apply continuous_iff_continuousAt.mpr
    intro n
    exact (kernel_contDiffAt k y _ (sphere_source_avoided y r hr hry n)).continuousAt.comp
      (f := fun n : Sphere => r • (n : Space))
      (continuous_const.smul continuous_subtype_val).continuousAt

def modeCoefficient (k : ℝ) (y : Space) (r : ℝ) (a : TotalIndex) : ℂ :=
  Complex.I*complexEvaluate (representative a.1 a.2) y/((k : ℂ)*(‖y‖ : ℂ)^a.1)*
    innerProfile a.1 (k : ℂ) (min r ‖y‖)*outerProfile a.1 (k : ℂ) (max r ‖y‖)

theorem actual_coefficient (k : ℝ) (hk : 0 < k) (y : Space) (hy : y ≠ 0)
    (r : ℝ) (hr : 0 < r) (hry : r ≠ ‖y‖) (a : TotalIndex) :
    (∫ n : Sphere,(angular a.1 a.2 n : ℂ)*angularKernel k y r hr hry n ∂angularMeasure)=
      modeCoefficient k y r a := by
  unfold modeCoefficient
  rw [← coefficient_formula k hk y hy (representative a.1 a.2) a.1
    (representative_homogeneous _ _) (representative_harmonic _ _) r hr hry]
  apply integral_congr_ae
  filter_upwards [] with n
  simp only [coefficient,RadialMoment.moment,SphericalMomentEquation.angularPolynomial,
    angularKernel,ContinuousMap.coe_mk,angular,HarmonicPolynomial.complexEvaluate,
    HarmonicPolynomial.evaluate,SpherePolynomial.polynomialMap_apply,mul_comm]

theorem actual_kernel_expansion (k : ℝ) (hk : 0 < k) (y : Space) (hy : y ≠ 0)
    (r : ℝ) (hr : 0 < r) (hry : r ≠ ‖y‖) :
    HasSum (fun a : TotalIndex => modeCoefficient k y r a • ComplexHarmonicBasis.vector a)
      (ContinuousMap.toLp 2 angularMeasure ℂ (angularKernel k y r hr hry)) := by
  simpa only [actual_coefficient k hk y hy r hr hry] using
    ComplexHarmonicBasis.continuous_expansion (angularKernel k y r hr hry)

end OQ14.ScalarGreenExpansion

#print axioms OQ14.ScalarGreenExpansion.sphere_source_avoided

#print axioms OQ14.ScalarGreenExpansion.actual_coefficient

#print axioms OQ14.ScalarGreenExpansion.actual_kernel_expansion
