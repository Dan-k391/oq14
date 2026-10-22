import RiccatiCompactDerivatives
import RadialReactionKernel

/-! The actual analytic origin extension of the scalar reaction, at every derivative order. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialEntireReaction

open Filter OQ14.RiccatiOriginSeries OQ14.RiccatiCompactDerivatives OQ14.HankelRealBasis
open OQ14.RiccatiBarrier
open scoped Topology

def reaction (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R)
    (z w : ℂ) : ℂ := RadialSource.gamma l gs R X hR*origin l z*origin l w

def component (l m n : ℕ) (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R)
    (z w : ℂ) : ℂ :=
  RadialSource.gamma l gs R X hR*iteratedDeriv m (origin l) z*iteratedDeriv n (origin l) w

theorem reaction_eq_actual (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    reaction l gs R X hR (x : ℂ) (y : ℂ) = RadialReactionKernel.reaction l gs R X hR x y := by
  rw [reaction,RadialReactionKernel.reaction_eq,
    origin_eq_psi l (x : ℂ) (Complex.ofReal_ne_zero.mpr hx.ne'),
    origin_eq_psi l (y : ℂ) (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← regular_eq_psi,← regular_eq_psi]

theorem reaction_zero_left (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (w : ℂ) : reaction l gs R X hR 0 w = 0 := by
  simp only [reaction,origin_zero,mul_zero,zero_mul]

theorem reaction_zero_right (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (z : ℂ) : reaction l gs R X hR z 0 = 0 := by
  simp only [reaction,origin_zero,mul_zero]

theorem component_eq_mixed_derivative (l m n : ℕ) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) (z w : ℂ) :
    iteratedDeriv n (fun v : ℂ => iteratedDeriv m (fun u : ℂ => reaction l gs R X hR u v) z) w =
      component l m n gs R X hR z w := by
  have hleft : ∀ v : ℂ, iteratedDeriv m (fun u : ℂ => reaction l gs R X hR u v) z =
      RadialSource.gamma l gs R X hR*iteratedDeriv m (origin l) z*origin l v := by
    intro v
    have he : (fun u : ℂ => reaction l gs R X hR u v) =
        fun u : ℂ => (RadialSource.gamma l gs R X hR*origin l v)*origin l u := by
      funext u
      dsimp [reaction]
      ring
    rw [he,iteratedDeriv_const_mul (origin_analyticAt l z).contDiffAt]
    ring
  simp_rw [hleft]
  rw [iteratedDeriv_const_mul (origin_analyticAt l w).contDiffAt]
  rfl

theorem component_norm_bound (l m n : ℕ) (gs : List RadialStack.Layer) (R X b : ℝ)
    (hR : 0 < R) (hb : 0 < b) (hbarrier : b^2 < ν l) (z w : ℂ)
    (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    ‖component l m n gs R X hR z w‖ ≤
      Real.exp (2*b^2)*(‖RadialSource.gamma l gs R X hR‖*(regular l b)^2) := by
  have h1 := origin_derivative_regular_bound l m b hb hbarrier z hz
  have h2 := origin_derivative_regular_bound l n b hb hbarrier w hw
  have hpos : 0 < regular l b := (barrier_positive l b hb hbarrier b ⟨hb,le_rfl⟩).1
  have hp := mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le hpos.le)
  have hm := mul_le_mul_of_nonneg_left hp (norm_nonneg (RadialSource.gamma l gs R X hR))
  simp only [component,norm_mul]
  convert hm using 1
  · ring
  · rw [show 2*b^2=b^2+b^2 by ring,Real.exp_add]
    ring

theorem real_iteratedDeriv_const_mul (f : ℝ → ℂ) (n : ℕ) (x : ℝ)
    (hf : ContDiffAt ℝ n f x) (c : ℂ) :
    iteratedDeriv n (fun t : ℝ => c*f t) x = c*iteratedDeriv n f x := by
  simpa only [iteratedDerivWithin_univ,Pi.smul_apply,smul_eq_mul] using
    iteratedDerivWithin_const_smul (Set.mem_univ x) uniqueDiffOn_univ c
      (contDiffWithinAt_univ.mpr hf)

theorem actual_real_mixed_derivative (l m n : ℕ) (gs : List RadialStack.Layer)
    (R X : ℝ) (hR : 0 < R) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    iteratedDeriv n (fun v : ℝ => iteratedDeriv m
      (fun u : ℝ => RadialReactionKernel.reaction l gs R X hR u v) x) y =
        component l m n gs R X hR (x : ℂ) (y : ℂ) := by
  have hleft : ∀ v : ℝ, iteratedDeriv m
      (fun u : ℝ => RadialReactionKernel.reaction l gs R X hR u v) x =
        RadialSource.gamma l gs R X hR*iteratedDeriv m (origin l) (x : ℂ)*(regular l v : ℂ) := by
    intro v
    have he : (fun u : ℝ => RadialReactionKernel.reaction l gs R X hR u v) =
        fun u : ℝ => (RadialSource.gamma l gs R X hR*(regular l v : ℂ))*(regular l u : ℂ) := by
      funext u
      rw [RadialReactionKernel.reaction_eq]
      ring
    have hreg : ContDiffAt ℝ m (fun u : ℝ => (regular l u : ℂ)) x := by
      have hh : (fun u : ℝ => (regular l u : ℂ)) =ᶠ[nhds x] fun u : ℝ => origin l (u : ℂ) := by
        filter_upwards [eventually_ne_nhds hx.ne'] with u hu
        exact (regular_eq_psi l u).trans (origin_eq_psi l (u : ℂ) (Complex.ofReal_ne_zero.mpr hu)).symm
      have hc := ((entire_origin l).restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
      exact (hc.contDiffAt.of_le (by exact_mod_cast (show (m : ℕ∞) ≤ ⊤ from le_top))).congr_of_eventuallyEq hh
    rw [he,real_iteratedDeriv_const_mul _ m x hreg,positive_real_derivative_identification l m x hx]
    ring
  simp_rw [hleft]
  have hreg : ContDiffAt ℝ n (fun v : ℝ => (regular l v : ℂ)) y := by
    have hh : (fun v : ℝ => (regular l v : ℂ)) =ᶠ[nhds y] fun v : ℝ => origin l (v : ℂ) := by
      filter_upwards [eventually_ne_nhds hy.ne'] with v hv
      exact (regular_eq_psi l v).trans (origin_eq_psi l (v : ℂ) (Complex.ofReal_ne_zero.mpr hv)).symm
    have hc := ((entire_origin l).restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
    exact (hc.contDiffAt.of_le (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))).congr_of_eventuallyEq hh
  rw [real_iteratedDeriv_const_mul _ n y hreg,positive_real_derivative_identification l n y hy]
  rfl

end OQ14.RadialEntireReaction

#print axioms OQ14.RadialEntireReaction.reaction_eq_actual
#print axioms OQ14.RadialEntireReaction.reaction_zero_left
#print axioms OQ14.RadialEntireReaction.reaction_zero_right
#print axioms OQ14.RadialEntireReaction.component_eq_mixed_derivative
#print axioms OQ14.RadialEntireReaction.component_norm_bound
#print axioms OQ14.RadialEntireReaction.real_iteratedDeriv_const_mul
#print axioms OQ14.RadialEntireReaction.actual_real_mixed_derivative
