import NormalizedHarmonicJets
import Mathlib.Algebra.MvPolynomial.Funext

/-! Injectivity and actual representative expansion for homogeneous polynomials. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.HarmonicPolynomialRestriction
open OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis

theorem homogeneous_eq_zero (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (hz : SpherePolynomial.polynomialMap p=0) : p=0 := by
  apply MvPolynomial.funext
  intro a
  let x : Space := (WithLp.equiv 2 (Fin 3 → ℝ)).symm a
  obtain ⟨r,n,hr,he,hx⟩ := NormalizedHarmonicJets.radius_unit_representation x
  have hn : evaluate p (n : Space)=0 := by
    have h := congrArg (fun f : C(Sphere,ℝ) => f n) hz
    simpa only [SpherePolynomial.polynomialMap_apply,ContinuousMap.zero_apply,evaluate] using h
  have hzero : evaluate p x=0 := by
    rw [hx,FischerDecomposition.evaluate_smul p l hp,hn,mul_zero]
  simpa only [evaluate,x,map_zero] using hzero

theorem restrictionL2_injective (l : ℕ) : Function.Injective (restrictionL2 l) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  have hz : SpherePolynomial.polynomialMap (p : Poly)=0 := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) angularMeasure
    simpa only [map_zero] using (show restrictionL2 l p=0 from hp)
  have he := homogeneous_eq_zero (p : Poly) l p.property.1 hz
  exact Subtype.ext he

theorem representative_expansion (l : ℕ) (p : harmonicPolynomials l) :
    (p : Poly)=∑ i : Index l,(SphereHarmonicBasis.basis l).repr (polynomialVector l p) i • (representative l i : Poly) := by
  have h := restriction_expansion l p
  apply sub_eq_zero.mp
  apply homogeneous_eq_zero _ l
  · exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ l).sub_mem p.property.1
      ((MvPolynomial.homogeneousSubmodule (Fin 3) ℝ l).sum_mem (fun i _ =>
        (MvPolynomial.homogeneousSubmodule (Fin 3) ℝ l).smul_mem _ (representative_homogeneous l i)))
  · simpa only [map_sub,map_sum,map_smul,angular] using sub_eq_zero.mpr h

end OQ14.HarmonicPolynomialRestriction

#print axioms OQ14.HarmonicPolynomialRestriction.homogeneous_eq_zero
#print axioms OQ14.HarmonicPolynomialRestriction.restrictionL2_injective
#print axioms OQ14.HarmonicPolynomialRestriction.representative_expansion
