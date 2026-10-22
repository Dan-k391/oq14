import ScalarGreenNormalization
import HankelRealBasis

/-! The sign relating the physical scalar kernel to the reduced radial Green function. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarGreenReduced
open Complex Set OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.ScalarGreenJump
  OQ14.ScalarGreenMoment OQ14.ScalarGreenNormalization

def reducedFree (l : ℕ) (x y : ℝ) : ℂ :=
  (HankelRealBasis.regular l (min x y) : ℂ)*
    ((HankelRealBasis.irregular l (max x y) : ℂ)-I*HankelRealBasis.regular l (max x y))

theorem irregular_minus_I_regular (l : ℕ) (x : ℝ) :
    (HankelRealBasis.irregular l x : ℂ)-I*HankelRealBasis.regular l x=
      -I*ModalAlgebra.xi l (x : ℂ) := by
  apply Complex.ext <;> simp [HankelRealBasis.irregular,HankelRealBasis.regular]

theorem reducedFree_actual (l : ℕ) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    reducedFree l x y= -I*RiccatiOriginSeries.origin l (min x y : ℝ)*
      ModalAlgebra.xi l (max x y : ℝ) := by
  rw [reducedFree,irregular_minus_I_regular,HankelRealBasis.regular_eq_psi,
    ← RiccatiOriginSeries.origin_eq_psi l _ (ofReal_ne_zero.mpr (lt_min hx hy).ne')]
  ring

theorem coefficient_reduced (k : ℝ) (hk : 0 < k) (y : Space) (hy : y ≠ 0)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (hh : formalLaplacian p=0)
    (r : ℝ) (hr : 0 < r) (hry : r ≠ ‖y‖) :
    coefficient k y p r= -complexEvaluate p y*
      reducedFree l (k*r) (k*‖y‖)/((k : ℂ)*(‖y‖ : ℂ)^l*(r : ℂ)*(‖y‖ : ℂ)) := by
  rw [coefficient_formula k hk y hy p l hp hh r hr hry,
    reducedFree_actual l (k*r) (k*‖y‖) (mul_pos hk hr) (mul_pos hk (norm_pos_iff.mpr hy))]
  have hkc : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk.ne'
  have hrc : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hsc : (‖y‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy)
  rcases le_total r ‖y‖ with h | h
  · rw [min_eq_left h,max_eq_right h,min_eq_left (mul_le_mul_of_nonneg_left h hk.le),
      max_eq_right (mul_le_mul_of_nonneg_left h hk.le)]
    simp only [innerProfile,outerProfile,RadialQuotient.profile,RadialOriginSelection.regular,
      RadialRellich.outgoing,pow_one,ofReal_mul]
    field_simp [hkc,hrc,hsc]
    ring
  · rw [min_eq_right h,max_eq_left h,min_eq_right (mul_le_mul_of_nonneg_left h hk.le),
      max_eq_left (mul_le_mul_of_nonneg_left h hk.le)]
    simp only [innerProfile,outerProfile,RadialQuotient.profile,RadialOriginSelection.regular,
      RadialRellich.outgoing,pow_one,ofReal_mul]
    field_simp [hkc,hrc,hsc]
    ring

end OQ14.ScalarGreenReduced

#print axioms OQ14.ScalarGreenReduced.irregular_minus_I_regular

#print axioms OQ14.ScalarGreenReduced.reducedFree_actual

#print axioms OQ14.ScalarGreenReduced.coefficient_reduced
