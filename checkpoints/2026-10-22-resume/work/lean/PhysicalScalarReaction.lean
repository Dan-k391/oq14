import ScalarGreenReduced
import SpatialReactionTerms

/-! The actual physical scalar reaction sign and globally regular solid-wave realization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.PhysicalScalarReaction
open Complex Set OQ14.Maxwell OQ14.HarmonicPolynomial

theorem reducedFree_formula (l : ℕ) (r s : ℝ) :
    ScalarGreenReduced.reducedFree l r s=
      (HankelRealBasis.regular l (min r s) : ℂ)*HankelRealBasis.irregular l (max r s)-
        I*(HankelRealBasis.regular l r : ℂ)*HankelRealBasis.regular l s := by
  rcases le_total r s with h | h
  · simp only [ScalarGreenReduced.reducedFree,min_eq_left h,max_eq_right h];ring
  · simp only [ScalarGreenReduced.reducedFree,min_eq_right h,max_eq_left h];ring

theorem physical_radial_difference (l : ℕ) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) (r s : ℝ) :
    -(RadialSource.scalarGreen l gs R X hR r s-ScalarGreenReduced.reducedFree l r s)/
        ((r : ℂ)*(s : ℂ))=
      -(RadialSource.gamma l gs R X hR+I)*(HankelRealBasis.regular l r : ℂ)*
        HankelRealBasis.regular l s/((r : ℂ)*(s : ℂ)) := by
  rw [RadialSource.scalarGreen_formula,reducedFree_formula]
  ring

theorem solid_wave_on_ray (l : ℕ) (p : Poly) (hp : p.IsHomogeneous l)
    (r : ℝ) (hr : 0 < r) (n : SphereHarmonicBasis.Sphere) :
    SolidScalarHelmholtz.wave l 1 p (r • (n : Space))=
      ScalarGreenJump.innerProfile l 1 r*SphericalMomentEquation.angularPolynomial p n := by
  have hn : ‖r • (n : Space)‖=r := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,AngularPower.sphere_norm,mul_one]
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  simp only [SolidScalarHelmholtz.wave,SolidScalarHelmholtz.radial,hn,one_pow,one_mul,
    FischerDecomposition.complexEvaluate_smul p l hp,ScalarGreenJump.innerProfile,
    RadialQuotient.profile,RadialOriginSelection.regular,pow_one,one_mul,
    SphericalMomentEquation.angularPolynomial,SolidRadialSeries.origin_factor,ofReal_pow]
  field_simp [hrc]
  ring

def term (a : SphereHarmonicHilbert.TotalIndex) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) : Space × Space → ℂ :=
  -(RadialSource.gamma a.1 gs R X hR+I) • SpatialReactionTerms.basisProduct a 1 1

theorem term_smooth (a : SphereHarmonicHilbert.TotalIndex) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) : ContDiff ℝ (⊤ : ℕ∞) (term a gs R X hR) := by
  simpa only [term,Pi.smul_apply] using (SpatialReactionTerms.basisProduct_smooth a 1 1).const_smul
    (-(RadialSource.gamma a.1 gs R X hR+I))

theorem term_on_rays (a : SphereHarmonicHilbert.TotalIndex) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (n m : SphereHarmonicBasis.Sphere) :
    term a gs R X hR (r • (n : Space),s • (m : Space))=
      -(RadialSource.gamma a.1 gs R X hR+I)*
        ScalarGreenJump.innerProfile a.1 1 r*ScalarGreenJump.innerProfile a.1 1 s*
        (SphereHarmonicBasis.angular a.1 a.2 n : ℂ)*(SphereHarmonicBasis.angular a.1 a.2 m : ℂ) := by
  simp only [term,Pi.smul_apply,smul_eq_mul,SpatialReactionTerms.basisProduct,
    solid_wave_on_ray _ _ (SphereHarmonicBasis.representative_homogeneous _ _) r hr,
    solid_wave_on_ray _ _ (SphereHarmonicBasis.representative_homogeneous _ _) s hs]
  simp only [SphereHarmonicBasis.angular,SpherePolynomial.polynomialMap_apply,
    SphericalMomentEquation.angularPolynomial,complexEvaluate,evaluate]
  ring

end OQ14.PhysicalScalarReaction

#print axioms OQ14.PhysicalScalarReaction.reducedFree_formula

#print axioms OQ14.PhysicalScalarReaction.physical_radial_difference

#print axioms OQ14.PhysicalScalarReaction.solid_wave_on_ray

#print axioms OQ14.PhysicalScalarReaction.term_smooth

#print axioms OQ14.PhysicalScalarReaction.term_on_rays
