import RiccatiGaussianBound
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Entire origin-series Cauchy bounds, with derivative order paid by a fixed larger disk. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RiccatiCompactDerivatives

open Complex Filter Set Metric OQ14.RiccatiOriginSeries OQ14.RiccatiSeriesCoefficients
open OQ14.HankelRealBasis OQ14.RiccatiBarrier
open scoped Topology

theorem entire_origin (l : ℕ) : ContDiff ℂ (⊤ : ℕ∞) (origin l) := by
  exact AnalyticOnNhd.contDiff (fun z _ => origin_analyticAt l z)

theorem origin_norm_bound (l : ℕ) (b : ℝ) (hb : 0 ≤ b) (z : ℂ) (hz : ‖z‖ ≤ b) :
    ‖origin l z‖ ≤ amplitude l 0*b^(l+1)*Real.exp (b^2/2) := by
  have hs : HasSum (fun m : ℕ => (b^2/2)^m/(Nat.factorial m : ℝ)) (Real.exp (b^2/2)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp ℝ (b^2/2)
  apply tsum_of_norm_bounded (hs.mul_left (amplitude l 0*b^(l+1)))
  intro m
  rw [term_norm]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz _) (amplitude_pos l m).le).trans
    (power_majorant l m b hb)

theorem iterated_derivative_disk_bound (f : ℂ → ℂ) (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    (b M : ℝ) (hM : ∀ z : ℂ, ‖z‖ ≤ b → ‖f z‖ ≤ M) (n : ℕ) :
    ∀ z : ℂ, ‖z‖+(n : ℝ) ≤ b → ‖iteratedDeriv n f z‖ ≤ M := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero,Nat.cast_zero,add_zero] using hM
  | succ n ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hd := hf.differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z) (R := 1)
      (by norm_num) hd.diffContOnCl (fun w hw => ih w (by
        have hdist : ‖w-z‖ = 1 := by simpa only [mem_sphere,dist_eq_norm] using hw
        have hn : ‖w‖ ≤ ‖w-z‖+‖z‖ := by
          convert norm_add_le (w-z) z using 1
          simp
        push_cast at hz
        linarith))
    simpa only [div_one] using h

theorem origin_iteratedDeriv_bound (l n : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (z : ℂ) (hz : ‖z‖+(n : ℝ) ≤ b) :
    ‖iteratedDeriv n (origin l) z‖ ≤ amplitude l 0*b^(l+1)*Real.exp (b^2/2) :=
  iterated_derivative_disk_bound (origin l) (entire_origin l) b _ (origin_norm_bound l b hb) n z hz

theorem origin_iteratedDeriv_eq_psi (l n : ℕ) (z : ℂ) (hz : z ≠ 0) :
    iteratedDeriv n (origin l) z = iteratedDeriv n (OQ14.ModalAlgebra.psi l) z := by
  apply Filter.EventuallyEq.iteratedDeriv_eq n
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact origin_eq_psi l w hw

theorem real_origin_iteratedDeriv (l n : ℕ) :
    iteratedDeriv n (fun x : ℝ => origin l (x : ℂ)) =
      fun x : ℝ => iteratedDeriv n (origin l) (x : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ,ih]
    funext x
    have hd := (entire_origin l).differentiable_iteratedDeriv n (by exact_mod_cast ENat.coe_lt_top n)
    rw [iteratedDeriv_succ]
    exact (hd (x : ℂ)).hasDerivAt.comp_ofReal |>.deriv

theorem positive_real_derivative_identification (l n : ℕ) (x : ℝ) (hx : 0 < x) :
    iteratedDeriv n (fun t : ℝ => (regular l t : ℂ)) x =
      iteratedDeriv n (origin l) (x : ℂ) := by
  calc
    _ = iteratedDeriv n (fun t : ℝ => origin l (t : ℂ)) x := by
      apply Filter.EventuallyEq.iteratedDeriv_eq n
      filter_upwards [eventually_ne_nhds hx.ne'] with t ht
      exact (regular_eq_psi l t).trans (origin_eq_psi l t (Complex.ofReal_ne_zero.mpr ht)).symm
    _ = _ := congrFun (real_origin_iteratedDeriv l n) x

theorem amplitude_regular_comparison (l : ℕ) (b : ℝ) (hb : 0 < b) (hbarrier : b^2 < ν l) :
    amplitude l 0*b^(l+1) ≤ Real.exp (b^2/2)*regular l b := by
  let E : ℝ := b^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l b+2))
  have hg := RiccatiLogDerivative.gamma_ge_one l b hbarrier
  have hden : 1 ≤ (l : ℝ)+RiccatiLogDerivative.gamma l b+2 := by
    have hn : 0 ≤ (l : ℝ) := Nat.cast_nonneg l
    linarith
  have hE : E ≤ b^2/2 := by
    dsimp [E]
    apply (div_le_iff₀ (by positivity : 0 < 2*((l : ℝ)+RiccatiLogDerivative.gamma l b+2))).mpr
    nlinarith [mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hden)]
  have hlo : amplitude l 0*b^(l+1)*Real.exp (-E) ≤ regular l b := by
    simpa only [E,neg_div] using RiccatiGaussianBound.regular_gaussian_lower l b hb hbarrier b ⟨hb,le_rfl⟩
  have hlow : amplitude l 0*b^(l+1)*Real.exp (-(b^2/2)) ≤ regular l b :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hE))
      (mul_nonneg (amplitude_pos l 0).le (pow_nonneg hb.le _))).trans hlo
  have h := mul_le_mul_of_nonneg_left hlow (Real.exp_pos (b^2/2)).le
  have he : Real.exp (b^2/2)*Real.exp (-(b^2/2)) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  calc
    _ = Real.exp (b^2/2)*(amplitude l 0*b^(l+1)*Real.exp (-(b^2/2))) := by
      rw [← mul_assoc,mul_comm (Real.exp (b^2/2)),mul_assoc,he,mul_one]
    _ ≤ _ := h

theorem origin_derivative_regular_bound (l n : ℕ) (b : ℝ) (hb : 0 < b)
    (hbarrier : b^2 < ν l) (z : ℂ) (hz : ‖z‖+(n : ℝ) ≤ b) :
    ‖iteratedDeriv n (origin l) z‖ ≤ Real.exp (b^2)*regular l b := by
  apply (origin_iteratedDeriv_bound l n b hb.le z hz).trans
  have h := mul_le_mul_of_nonneg_right (amplitude_regular_comparison l b hb hbarrier)
    (Real.exp_pos (b^2/2)).le
  convert h using 1
  rw [mul_assoc,mul_comm (regular l b),← mul_assoc,← Real.exp_add]
  congr 2
  ring

end OQ14.RiccatiCompactDerivatives

#print axioms OQ14.RiccatiCompactDerivatives.entire_origin
#print axioms OQ14.RiccatiCompactDerivatives.origin_norm_bound
#print axioms OQ14.RiccatiCompactDerivatives.iterated_derivative_disk_bound
#print axioms OQ14.RiccatiCompactDerivatives.origin_iteratedDeriv_bound
#print axioms OQ14.RiccatiCompactDerivatives.origin_iteratedDeriv_eq_psi
#print axioms OQ14.RiccatiCompactDerivatives.real_origin_iteratedDeriv
#print axioms OQ14.RiccatiCompactDerivatives.positive_real_derivative_identification
#print axioms OQ14.RiccatiCompactDerivatives.amplitude_regular_comparison
#print axioms OQ14.RiccatiCompactDerivatives.origin_derivative_regular_bound
