import EvenHarmonicProjection
import HarmonicMomentSeparation
import SphereReactionKernel

/-! Symmetric continuous angular tests are separated by projected harmonic moments. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HarmonicProjectedMoments
open MeasureTheory Maxwell HarmonicPolynomial SphereReactionKernel
abbrev Space := FourierL2.Space

theorem integral_twist (L : Space ≃ₗᵢ[ℝ] Space) (v f : Sphere → ℂ)
    (hv : ∀ θ, v (SphereAngularSymmetry.sphereMap L θ)=v θ) :
    (∫ θ, v θ*f (SphereAngularSymmetry.sphereMap L θ) ∂surface)=∫ θ, v θ*f θ ∂surface := by
  have h := (SphereAngularSymmetry.measurePreserving_sphereMap L).integral_comp
    (SphereAngularSymmetry.sphereMap L).measurableEmbedding (fun θ => v θ*f θ)
  simpa only [hv] using h

theorem half_turn_moment (v : Sphere → ℂ) (hv : Continuous v)
    (hs : ∀ θ, v (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)=v θ)
    (p : Poly) :
    (∫ θ, v θ*(SpherePolynomial.polynomialMap (HarmonicHalfTurn.project p) θ : ℂ) ∂surface)=
      ∫ θ, v θ*(SpherePolynomial.polynomialMap p θ : ℂ) ∂surface := by
  have hi (q : Poly) : Integrable (fun θ : Sphere => v θ*(SpherePolynomial.polynomialMap q θ : ℂ)) surface :=
    (hv.mul (Complex.continuous_ofReal.comp (SpherePolynomial.polynomialMap q).continuous)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he (θ : Sphere) : (SpherePolynomial.polynomialMap (HarmonicHalfTurn.project p) θ : ℂ)=
      (1/2 : ℂ)*((SpherePolynomial.polynomialMap p θ : ℂ)+
        (SpherePolynomial.polynomialMap p (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ) : ℂ)) := by
    have hr := HarmonicRotation.rotate_evaluate HarmonicHalfTurn.rotation p θ.val
    simp only [SpherePolynomial.polynomialMap_apply]
    change ((evaluate (HarmonicHalfTurn.project p) θ.val : ℝ) : ℂ)=
      (1/2 : ℂ)*((evaluate p θ.val : ℂ)+(evaluate p (HarmonicHalfTurn.rotation θ.val) : ℂ))
    simp [HarmonicHalfTurn.project,evaluate,Algebra.smul_def,← hr]
    exact hr
  have ht : Integrable (fun θ : Sphere => v θ*(SpherePolynomial.polynomialMap p
      (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ) : ℂ)) surface := by
    exact (hv.mul (Complex.continuous_ofReal.comp ((SpherePolynomial.polynomialMap p).continuous.comp
      (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation).continuous))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  calc
    _ = (1/2 : ℂ)*(∫ θ, v θ*(SpherePolynomial.polynomialMap p θ : ℂ)+
        v θ*(SpherePolynomial.polynomialMap p (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ) : ℂ) ∂surface) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with θ
      rw [he]
      ring
    _ = _ := by
      rw [integral_add (hi p) ht,integral_twist HarmonicHalfTurn.rotation v
        (fun θ => (SpherePolynomial.polynomialMap p θ : ℂ)) hs]
      ring

theorem odd_moment_zero (v : Sphere → ℂ)
    (hs : ∀ θ, v (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ)=v θ)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hl : Odd l) :
    (∫ θ, v θ*(SpherePolynomial.polynomialMap p θ : ℂ) ∂surface)=0 := by
  have he (θ : Sphere) : (SpherePolynomial.polynomialMap p
      (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ) : ℂ)=
      -(SpherePolynomial.polynomialMap p θ : ℂ) := by
    have h := FischerDecomposition.evaluate_smul p l hp (-1) θ.val
    simpa only [neg_one_smul,hl.neg_one_pow,neg_one_mul,Complex.ofReal_neg,
      SpherePolynomial.polynomialMap_apply] using congrArg Complex.ofReal h
  have h := integral_twist (LinearIsometryEquiv.neg ℝ) v
    (fun θ => (SpherePolynomial.polynomialMap p θ : ℂ)) hs
  simp_rw [he,mul_neg,integral_neg] at h
  linear_combination (-1/2 : ℂ)*h

theorem projected_moment (v : Sphere → ℂ) (hv : Continuous v)
    (hs : ∀ θ, v (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)=v θ)
    (hc : ∀ θ, v (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ)=v θ)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    (∫ θ, v θ*(SpherePolynomial.polynomialMap (EvenHarmonicProjection.project l p) θ : ℂ) ∂surface)=
      ∫ θ, v θ*(SpherePolynomial.polynomialMap p θ : ℂ) ∂surface := by
  by_cases he : Even l
  · simpa only [EvenHarmonicProjection.project,if_pos he] using half_turn_moment v hv hs p
  · rw [EvenHarmonicProjection.project,if_neg he,odd_moment_zero v hc p l hp (Nat.not_even_iff_odd.mp he)]
    simp [SpherePolynomial.polynomialMap_apply,evaluate]

theorem zero_of_projected_moments (v : Sphere → ℂ) (hv : Continuous v)
    (hs : ∀ θ, v (SphereAngularSymmetry.sphereMap HarmonicHalfTurn.rotation θ)=v θ)
    (hc : ∀ θ, v (SphereAngularSymmetry.sphereMap (LinearIsometryEquiv.neg ℝ) θ)=v θ)
    (hm : ∀ (l : ℕ) (p : Poly), p.IsHomogeneous l → formalLaplacian p=0 →
      (∫ θ, v θ*(SpherePolynomial.polynomialMap (EvenHarmonicProjection.project l p) θ : ℂ) ∂surface)=0) :
    ∀ θ, v θ=0 := by
  apply HarmonicMomentSeparation.zero_of_harmonic_moments v hv
  intro l p hp hh
  change (∫ θ, v θ*(SpherePolynomial.polynomialMap p θ : ℂ) ∂surface)=0
  rw [← projected_moment v hv hs hc p l hp]
  exact hm l p hp hh

end OQ14.HarmonicProjectedMoments
#print axioms OQ14.HarmonicProjectedMoments.integral_twist
#print axioms OQ14.HarmonicProjectedMoments.half_turn_moment
#print axioms OQ14.HarmonicProjectedMoments.odd_moment_zero
#print axioms OQ14.HarmonicProjectedMoments.projected_moment
#print axioms OQ14.HarmonicProjectedMoments.zero_of_projected_moments
