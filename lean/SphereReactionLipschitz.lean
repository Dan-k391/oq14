import SphereReactionKernel
import Mathlib.Analysis.Calculus.MeanValue

/-! # Derived global source Lipschitz bounds for the actual sphere-integral kernels -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.SphereReactionLipschitz

open MeasureTheory Metric Set SphereReactionKernel
open scoped Topology InnerProductSpace

def bound (k : ℝ) : ℝ := entryBound k*|k|

theorem bound_nonnegative (k : ℝ) : 0 ≤ bound k :=
  mul_nonneg (entryBound_nonnegative k) (abs_nonneg k)

theorem phase_difference (s t : ℝ) :
    ‖Complex.exp ((t : ℂ)*Complex.I)-Complex.exp ((s : ℂ)*Complex.I)‖ ≤ |t-s| := by
  let f := fun r : ℝ => Complex.exp ((r : ℂ)*Complex.I)
  let f' := fun r : ℝ => Complex.exp ((r : ℂ)*Complex.I)*Complex.I
  have hd : ∀ r : ℝ, HasDerivAt f (f' r) r := by
    intro r
    have he := ((GreenKernel.complex_radius_hasDerivAt r).mul_const Complex.I).cexp
    convert he using 1
    dsimp only [f, f']
    ring
  have hb : ∀ r ∈ (Set.univ : Set ℝ), ‖f' r‖ ≤ 1 := by
    intro r _
    simp only [f', norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one, le_refl]
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r (_ : r ∈ (Set.univ : Set ℝ)) => (hd r).hasDerivWithinAt) hb
    convex_univ (mem_univ s) (mem_univ t)
  simpa only [f, one_mul, Real.norm_eq_abs] using he

theorem wave_difference (k : ℝ) (x y : Space) (θ : Sphere) :
    ‖wave k x θ-wave k y θ‖ ≤ |k| * ‖x-y‖ := by
  have he := phase_difference (k*⟪θ.val,y⟫_ℝ) (k*⟪θ.val,x⟫_ℝ)
  change ‖wave k x θ-wave k y θ‖ ≤ _ at he
  have hh : k*⟪θ.val,x⟫_ℝ-k*⟪θ.val,y⟫_ℝ = k*⟪θ.val,x-y⟫_ℝ := by
    rw [inner_sub_right]
    ring
  rw [hh, abs_mul] at he
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg k)
  simpa only [sphere_norm, one_mul] using abs_real_inner_le_norm θ.val (x-y)

theorem J_difference (k : ℝ) (x y : Space) (i j : Fin 3) :
    ‖J k x i j-J k y i j‖ ≤ bound k*‖x-y‖ := by
  have he : J k x i j-J k y i j = ((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
      ∫ θ : Sphere, amplitude θ i j*(wave k x θ-wave k y θ) ∂surface := by
    simp only [J]
    rw [← mul_sub, ← integral_sub (integrand_integrable k x i j) (integrand_integrable k y i j)]
    congr 1
    apply integral_congr_ae
    filter_upwards with θ
    ring
  have hb : ∀ θ : Sphere, ‖amplitude θ i j*(wave k x θ-wave k y θ)‖ ≤ 2*|k| * ‖x-y‖ := by
    intro θ
    rw [norm_mul]
    exact (mul_le_mul (amplitude_bound θ i j) (wave_difference k x y θ)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have hi := norm_integral_le_of_norm_le_const (μ := surface) (Filter.Eventually.of_forall hb)
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left hi (abs_nonneg _)).trans_eq
  unfold bound entryBound surfaceMass
  ring

theorem reaction_source_difference (electric : Bool) (k : ℝ) (x y z : Space) (i j : Fin 3) :
    ‖reaction electric k x y i j-reaction electric k x z i j‖ ≤ bound k*‖y-z‖ := by
  have hfirst := J_difference k (x-y) (x-z) i j
  have hsecond := J_difference k (reflect x-y) (reflect x-z) i j
  have hn (u : Space) : ‖(u-y)-(u-z)‖ = ‖y-z‖ := by
    rw [show (u-y)-(u-z)=-(y-z) by abel, norm_neg]
  rw [hn] at hfirst hsecond
  have he : reaction electric k x y i j-reaction electric k x z i j = (Complex.I/2)*
      ((J k (x-y) i j-J k (x-z) i j) +
        (if electric then -1 else 1 : ℂ)*(sign i : ℂ)*
          (J k (reflect x-y) i j-J k (reflect x-z) i j)) := by
    unfold reaction
    ring
  have hs : ‖(sign i : ℂ)‖ = 1 := by unfold sign; split_ifs <;> norm_num
  have hb : ‖(if electric then -1 else 1 : ℂ)‖ = 1 := by cases electric <;> norm_num
  have hc : ‖Complex.I/2‖ = 1/2 := by norm_num [norm_div]
  rw [he, norm_mul, hc]
  apply (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num : (0 : ℝ) ≤ 1/2)).trans
  simp only [norm_mul, hs, hb, one_mul]
  linarith

end OQ14.SphereReactionLipschitz

#print axioms OQ14.SphereReactionLipschitz.bound_nonnegative
#print axioms OQ14.SphereReactionLipschitz.phase_difference
#print axioms OQ14.SphereReactionLipschitz.wave_difference
#print axioms OQ14.SphereReactionLipschitz.J_difference
#print axioms OQ14.SphereReactionLipschitz.reaction_source_difference
