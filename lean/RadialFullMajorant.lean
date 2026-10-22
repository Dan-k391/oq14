import RadialLowTail
import RadialEntireTail

/-! Genuine summable full-degree bounds for the actual scalar reaction derivatives. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialFullMajorant

open OQ14.RadialStack OQ14.RadialEntireReaction OQ14.RiccatiSeriesCoefficients

def majorant (q M d b : ℝ) (k l : ℕ) : ℝ :=
  RadialLowTail.prefactor M d b*RadialLowTail.majorant b k l +
    RadialMiddleTail.prefactor q M d b*RadialMiddleTail.majorant q b k l +
    (4*b^2*Real.exp (2*b^2))*((l+1 : ℝ)^k*(1/2 : ℝ)^l)

theorem majorant_nonnegative (q M d b : ℝ) (k l : ℕ) : 0 ≤ majorant q M d b k l := by
  dsimp [majorant,RadialLowTail.prefactor,RadialLowTail.bound,RadialLowTail.majorant,
    RadialMiddleTail.prefactor,RadialMiddleTail.majorant]
  positivity

theorem majorant_summable (q M d b : ℝ) (k : ℕ) (hb : 0 ≤ b) :
    Summable (majorant q M d b k) :=
  (((RadialLowTail.majorant_summable b k hb).mul_left _).add
    ((RadialMiddleTail.majorant_summable q b k hb).mul_left _)).add
    ((RadialHighOrderTail.polynomial_geometric_summable k).mul_left _)

theorem component_weighted_bound (l k m n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hb : 0 < b) (ht : Real.exp 1*b ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (hqp : ∀ g ∈ gs, g.q ≤ q) (z w : ℂ)
    (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    (l+1 : ℝ)^k*‖component l m n gs R X (by linarith) z w‖ ≤ majorant q M d b k l := by
  have hRp : 0 < R := by linarith
  have hlow0 : 0 ≤ RadialLowTail.prefactor M d b*RadialLowTail.majorant b k l := by
    dsimp [RadialLowTail.prefactor,RadialLowTail.bound,RadialLowTail.majorant]
    positivity
  have hmid0 : 0 ≤ RadialMiddleTail.prefactor q M d b*RadialMiddleTail.majorant q b k l := by
    dsimp [RadialMiddleTail.prefactor,RadialMiddleTail.majorant]
    positivity
  have hhigh0 : 0 ≤ (4*b^2*Real.exp (2*b^2))*((l+1 : ℝ)^k*(1/2 : ℝ)^l) := by positivity
  by_cases hl : 2*((l : ℝ)+1) ≤ R
  · have h := RadialLowTail.weighted_term_bound (fun _ => gs) (fun _ => X)
      M d R b k m n z w hM hRp hb.le hz hw hc hd hp l
    simp only [RadialLowTail.term,dif_pos hRp,if_pos hl] at h
    dsimp [majorant]
    linarith
  · by_cases hm : (l : ℝ) ≤ 2*q*R
    · have hlower := RadialMiddleTail.outside_low_degree l R hR hl
      have hcut : (¬ 2*((l : ℝ)+1) ≤ R) ∧ (l : ℝ) ≤ 2*q*R := ⟨hl,hm⟩
      have h := RadialMiddleTail.term_degree_bound (fun _ => gs) (fun _ => X)
        q M d R b m n z w hq hM hR hb.le hz hw hc hX hd hp l
      simp only [RadialMiddleTail.term,dif_pos hRp,if_pos hcut,if_pos hlower] at h
      have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (l+1 : ℝ)^k)
      have h' : (l+1 : ℝ)^k*‖component l m n gs R X hRp z w‖ ≤
          RadialMiddleTail.prefactor q M d b*RadialMiddleTail.majorant q b k l := by
        convert hh using 1
        dsimp [RadialMiddleTail.majorant]
        ring
      dsimp [majorant]
      linarith
    · have hm' : 2*q*R ≤ l := le_of_lt (lt_of_not_ge hm)
      have hhigh := RadialStackHighTail.cutoff_covers_high_range q R hq hRp.le l hm'
      have hbR : b ≤ R := by
        have he : (2 : ℝ) ≤ Real.exp 1 := by have he := Real.add_one_le_exp (1 : ℝ); linarith
        nlinarith
      have hbν : b^2 < RiccatiBarrier.ν l :=
        ((sq_le_sq₀ hb.le hRp.le).mpr hbR).trans_lt (RadialHighOrderBound.high_order_barrier l R hRp hhigh)
      have hcomp := RadialEntireReaction.component_norm_bound l m n gs R X b hRp hb hbν z w hz hw
      have hreact := RadialHighOrderBound.actual_reaction_high_order l gs R X b hRp
        (hRp.trans_le (chain_ordered hc)) hb hbR hhigh
        (RadialStackHighTail.common_stack_barrier l hc q hq hRp hX hqp hm')
      have hgeo := RadialHighOrderTail.majorant_geometric_envelope l b R hb.le (by linarith) ht hhigh
      have hnorm : ‖component l m n gs R X hRp z w‖ ≤
          (4*b^2*Real.exp (2*b^2))*(1/2 : ℝ)^l := by
        have hh := hcomp.trans (mul_le_mul_of_nonneg_left (hreact.trans hgeo) (Real.exp_pos _).le)
        have he : Real.exp (-R/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have h' := mul_le_mul_of_nonneg_left he
          (by positivity : 0 ≤ 4*b^2*Real.exp (2*b^2)*(1/2 : ℝ)^l)
        apply hh.trans
        convert h' using 1 <;> ring
      have hh := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ (l+1 : ℝ)^k)
      have h' : (l+1 : ℝ)^k*‖component l m n gs R X hRp z w‖ ≤
          (4*b^2*Real.exp (2*b^2))*((l+1 : ℝ)^k*(1/2 : ℝ)^l) := by
        convert hh using 1
        ring
      dsimp [majorant]
      linarith

theorem actual_norm_series_summable (k m n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hb : 0 < b) (ht : Real.exp 1*b ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (hqp : ∀ g ∈ gs, g.q ≤ q) (z w : ℂ)
    (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*‖component l m n gs R X (by linarith) z w‖) :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (by positivity) (norm_nonneg _))
    (fun l => component_weighted_bound l k m n hc q M d b hq hM hR hb ht hX hd hp hqp z w hz hw)
    (majorant_summable q M d b k hb.le)

theorem actual_complex_series_summable (k m n : ℕ) {gs : List Layer} {R X : ℝ}
    (hc : Chain gs X R) (q M d b : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M)
    (hR : 4 ≤ R) (hb : 0 < b) (ht : Real.exp 1*b ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hp : ∀ g ∈ gs, 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (hqp : ∀ g ∈ gs, g.q ≤ q) (z w : ℂ)
    (hz : ‖z‖+(m : ℝ) ≤ b) (hw : ‖w‖+(n : ℝ) ≤ b) :
    Summable (fun l : ℕ => ((l+1 : ℝ)^k) • component l m n gs R X (by linarith) z w) := by
  apply Summable.of_norm_bounded _ (majorant_summable q M d b k hb.le)
  intro l
  simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (l+1 : ℝ)^k)] using
    component_weighted_bound l k m n hc q M d b hq hM hR hb ht hX hd hp hqp z w hz hw

end OQ14.RadialFullMajorant

#print axioms OQ14.RadialFullMajorant.majorant_nonnegative
#print axioms OQ14.RadialFullMajorant.majorant_summable
#print axioms OQ14.RadialFullMajorant.component_weighted_bound
#print axioms OQ14.RadialFullMajorant.actual_norm_series_summable
#print axioms OQ14.RadialFullMajorant.actual_complex_series_summable
