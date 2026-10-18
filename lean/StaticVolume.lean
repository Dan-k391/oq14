import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Positive static volume block and stable perturbation

The weighted block is the actual bounded operator `1 + S† P S` on a
complex Hilbert space. Its inverse estimate is derived from positivity.
Identification of P with the Maxwell longitudinal Fourier projection is
a separate analytic obligation; no such identification is postulated here.
-/

noncomputable section
set_option autoImplicit false

namespace OQ14.StaticVolume

open ContinuousLinearMap
open scoped InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

def block (P S : H →L[ℂ] H) : H →L[ℂ] H := 1 + S.adjoint ∘L P ∘L S

theorem block_coercive (P S : H →L[ℂ] H) (hP : P.IsPositive) (x : H) :
    ‖x‖ ^ 2 ≤ (⟪block P S x, x⟫_ℂ).re := by
  have hp := (hP.adjoint_conj S).inner_nonneg_left x
  have hs : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  simp only [block, add_apply, one_apply, inner_add_left, Complex.add_re,
    hs]
  exact le_add_of_nonneg_right hp

theorem block_norm_lower (P S : H →L[ℂ] H) (hP : P.IsPositive) (x : H) :
    ‖x‖ ≤ ‖block P S x‖ := by
  have h1 := block_coercive P S hP x
  have h2 := RCLike.re_le_norm (⟪block P S x, x⟫_ℂ)
  simp only [RCLike.re_eq_complex_re] at h2
  have h3 := norm_inner_le_norm (𝕜 := ℂ) (block P S x) x
  by_cases hx : ‖x‖ = 0
  · simp [hx]
  · have hx' : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    nlinarith

theorem block_isUnit (P S : H →L[ℂ] H) (hP : P.IsPositive) :
    IsUnit (block P S) := by
  apply isUnit_of_forall_le_norm_inner_map (block P S) (c := 1) (by norm_num)
  intro x
  simpa using (block_coercive P S hP x).trans
    (RCLike.re_le_norm (⟪block P S x, x⟫_ℂ))

theorem block_inverse_norm_le (P S : H →L[ℂ] H) (hP : P.IsPositive) :
    ‖Ring.inverse (block P S)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have hi := congrArg (fun f : H →L[ℂ] H => f x)
    (Ring.mul_inverse_cancel (block P S) (block_isUnit P S hP))
  have hb := block_norm_lower P S hP ((Ring.inverse (block P S)) x)
  simp only [mul_apply, one_apply] at hi
  simpa only [one_mul, hi] using hb

theorem block_perturbation_isUnit (P S Q : H →L[ℂ] H)
    (hP : P.IsPositive) (hQ : ‖Q‖ < 1) : IsUnit (block P S - Q) := by
  let A := block P S
  have hA : IsUnit A := block_isUnit P S hP
  have hi : ‖Ring.inverse A‖ ≤ 1 := block_inverse_norm_le P S hP
  have hs : ‖Ring.inverse A * Q‖ < 1 := by
    calc
      ‖Ring.inverse A * Q‖ ≤ ‖Ring.inverse A‖ * ‖Q‖ := norm_mul_le _ _
      _ ≤ 1 * ‖Q‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
      _ < 1 := by simpa using hQ
  have hu := hA.mul (isUnit_one_sub_of_norm_lt_one hs)
  have he : A * (1 - Ring.inverse A * Q) = A - Q := by
    rw [mul_sub, mul_one, ← mul_assoc, Ring.mul_inverse_cancel A hA, one_mul]
  simpa only [he] using hu

theorem block_perturbation_lower (P S Q : H →L[ℂ] H)
    (hP : P.IsPositive) (x : H) :
    (1 - ‖Q‖) * ‖x‖ ≤ ‖(block P S - Q) x‖ := by
  have h0 := block_norm_lower P S hP x
  have h1 := norm_add_le (block P S x - Q x) (Q x)
  rw [sub_add_cancel] at h1
  have h2 := Q.le_opNorm x
  simp only [sub_apply]
  nlinarith

theorem block_perturbation_inverse_bound (P S Q : H →L[ℂ] H)
    (hP : P.IsPositive) (hQ : ‖Q‖ < 1) :
    ‖Ring.inverse (block P S - Q)‖ ≤ (1 - ‖Q‖)⁻¹ := by
  have hd : 0 < 1 - ‖Q‖ := sub_pos.mpr hQ
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hd.le)
  intro x
  have hi := congrArg (fun f : H →L[ℂ] H => f x)
    (Ring.mul_inverse_cancel (block P S - Q) (block_perturbation_isUnit P S Q hP hQ))
  have hl := block_perturbation_lower P S Q hP
    ((Ring.inverse (block P S - Q)) x)
  simp only [mul_apply, one_apply] at hi
  rw [hi] at hl
  exact (le_inv_mul_iff₀ hd).mpr hl

/-- An actual orthogonal projection is positive, without a positivity premise. -/
theorem projection_positive (U : Submodule ℂ H) [CompleteSpace U] :
    (U.subtypeL ∘L U.orthogonalProjection).IsPositive := by
  have h := (isPositive_one (𝕜 := ℂ) (E := U)).conj_adjoint U.subtypeL
  simpa only [Submodule.adjoint_subtypeL, one_def, id_comp] using h

/-- The inverse estimate for the actual weighted orthogonal-projection block. -/
theorem weighted_projection_inverse (U : Submodule ℂ H) [CompleteSpace U]
    (S : H →L[ℂ] H) :
    IsUnit (block (U.subtypeL ∘L U.orthogonalProjection) S) ∧
    ‖Ring.inverse (block (U.subtypeL ∘L U.orthogonalProjection) S)‖ ≤ 1 :=
  ⟨block_isUnit _ _ (projection_positive U),
    block_inverse_norm_le _ _ (projection_positive U)⟩

/-- The error of a proposed polarization is controlled by its actual residual. -/
theorem polarization_residual_bound (P S Q : H →L[ℂ] H)
    (hP : P.IsPositive) (hQ : ‖Q‖ < 1) (u v f : H)
    (hsol : (block P S - Q) u = f) :
    ‖u - v‖ ≤ (1 - ‖Q‖)⁻¹ * ‖f - (block P S - Q) v‖ := by
  have hl := block_perturbation_lower P S Q hP (u - v)
  rw [map_sub, hsol] at hl
  exact (le_inv_mul_iff₀ (sub_pos.mpr hQ)).mpr hl

end OQ14.StaticVolume

#print axioms OQ14.StaticVolume.block_coercive
#print axioms OQ14.StaticVolume.block_norm_lower
#print axioms OQ14.StaticVolume.block_isUnit
#print axioms OQ14.StaticVolume.block_inverse_norm_le
#print axioms OQ14.StaticVolume.block_perturbation_isUnit
#print axioms OQ14.StaticVolume.block_perturbation_lower
#print axioms OQ14.StaticVolume.block_perturbation_inverse_bound
#print axioms OQ14.StaticVolume.projection_positive
#print axioms OQ14.StaticVolume.weighted_projection_inverse
#print axioms OQ14.StaticVolume.polarization_residual_bound
