import ComplexMagneticReflection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02VanishingAlgebra
open Complex OQ14.Maxwell OQ14.ModalAxialRotation OQ14.ModalMeridionalReflection OQ14.WeakDebyeScalar

theorem radial_rotation (θ : ℝ) (x : Space) (v : Fin 3 → ℂ) :
    radialDot (fun j _ => vector θ v j) (spatial θ x) = radialDot (fun j _ => v j) x := by
  have h : (Real.cos θ : ℂ)^2 + (Real.sin θ : ℂ)^2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq θ
  simp only [radialDot, Fin.sum_univ_three, spatial, vector, WithLp.equiv_symm_pi_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    ofReal_sub, ofReal_add, ofReal_mul]
  norm_num [Matrix.vecHead, Matrix.vecTail, Function.comp_def]
  simp only [ofReal_cos, ofReal_sin] at h
  linear_combination ((x 0 : ℂ)*v 0 + (x 1 : ℂ)*v 1) * h

theorem rotate_to_plane (x : Space) : ∃ θ : ℝ, spatial θ x 1 = 0 := by
  by_cases hx : x 0 = 0
  · refine ⟨Real.pi / 2, ?_⟩
    simp [spatial, WithLp.equiv_symm_pi_apply, hx]
  · refine ⟨Real.arctan (-(x 1 / x 0)), ?_⟩
    simp only [spatial, WithLp.equiv_symm_pi_apply, Matrix.cons_val_one, Matrix.head_cons,
      Real.sin_arctan, Real.cos_arctan]
    field_simp
    ring

theorem plane_radial_zero (v : Space → Fin 3 → ℂ) (x : Space) (hx : x 1 = 0)
    (href : ∀ i, v (reflection x) i = -(sign i : ℂ) * v x i) :
    radialDot (fun j y => v y j) x = 0 := by
  have hr : reflection x = x := by
    ext i
    fin_cases i <;> simp [reflection_coordinate, sign, hx]
  have h0 := href 0
  have h2 := href 2
  rw [hr] at h0 h2
  simp [sign] at h0 h2
  simp only [radialDot, Fin.sum_univ_three, hx, ofReal_zero, zero_mul]
  linear_combination (x 0 : ℂ)/2 * h0 + (x 2 : ℂ)/2 * h2

theorem radial_zero (Good : Space → Prop) (v : Space → Fin 3 → ℂ)
    (hgood : ∀ θ x, Good x → Good (spatial θ x))
    (hrot : ∀ θ x, Good x → v (spatial θ x) = vector θ (v x))
    (href : ∀ x, Good x → ∀ i, v (reflection x) i = -(sign i : ℂ) * v x i)
    (x : Space) (hx : Good x) : radialDot (fun j y => v y j) x = 0 := by
  obtain ⟨θ, hplane⟩ := rotate_to_plane x
  have h := plane_radial_zero v (spatial θ x) hplane (href _ (hgood θ x hx))
  have he : radialDot (fun j y => v y j) (spatial θ x) =
      radialDot (fun j _ => vector θ (v x) j) (spatial θ x) := by
    simp only [radialDot, hrot θ x hx]
  rw [he, radial_rotation] at h
  exact h

#print axioms OQ14.Packet02VanishingAlgebra.radial_rotation
#print axioms OQ14.Packet02VanishingAlgebra.rotate_to_plane
#print axioms OQ14.Packet02VanishingAlgebra.plane_radial_zero
#print axioms OQ14.Packet02VanishingAlgebra.radial_zero
end OQ14.Packet02VanishingAlgebra
