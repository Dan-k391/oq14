import RadialLoadBounds
import RiccatiGaussianBound

/-! # Actual high-order reaction bounds for finite radial stacks -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialHighOrderBound

open Complex Set OQ14.HankelRealBasis OQ14.HankelCoefficientBounds
open OQ14.RiccatiBarrier OQ14.RiccatiSeriesCoefficients OQ14.RiccatiGaussianBound

theorem leading_amplitude_product (l : ℕ) : coefficient l l*amplitude l 0 = 1/(2*l+1 : ℝ) := by
  unfold coefficient amplitude
  simp only [Nat.sub_self,Nat.add_zero,Nat.factorial_zero,Nat.cast_one,mul_one,one_mul]
  rw [show l+l=2*l by omega,Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem high_order_barrier (l : ℕ) (R : ℝ) (hR : 0 < R) (hl : 2*R ≤ l) : R^2 < ν l := by
  have hs : (2*R)^2 ≤ (l : ℝ)^2 := (sq_le_sq₀ (by positivity) (Nat.cast_nonneg l)).mpr hl
  unfold ν
  nlinarith [sq_nonneg R,Nat.cast_nonneg (α := ℝ) l]

theorem gamma_ge_half_degree (l : ℕ) (R : ℝ) (hR : 0 < R) (hl : 2*R ≤ l) :
    (l : ℝ)/2 ≤ RiccatiLogDerivative.gamma l R := by
  have hb := high_order_barrier l R hR hl
  have hg := RiccatiLogDerivative.gamma_ge_one l R hb
  have he := RiccatiLogDerivative.gamma_equation l R hb
  have hRsq : R^2 ≤ ((l : ℝ)/2)^2 :=
    (sq_le_sq₀ hR.le (by positivity)).mpr (by linarith)
  by_contra hnot
  have hgsq : (RiccatiLogDerivative.gamma l R)^2 ≤ ((l : ℝ)/2)^2 :=
    pow_le_pow_left₀ (by linarith) (le_of_lt (lt_of_not_ge hnot)) 2
  unfold ν at he
  nlinarith [sq_nonneg (l : ℝ),Nat.cast_nonneg (α := ℝ) l]

theorem gaussian_exponent_le (l : ℕ) (R : ℝ) (hR : 0 < R) (hl : 2*R ≤ l) :
    R^2/(2*((l : ℝ)+RiccatiLogDerivative.gamma l R+2)) ≤ R/2 := by
  have hg := RiccatiLogDerivative.gamma_ge_one l R (high_order_barrier l R hR hl)
  apply (div_le_iff₀ (by positivity : 0 < 2*((l : ℝ)+RiccatiLogDerivative.gamma l R+2))).mpr
  nlinarith [mul_nonneg hR.le (by linarith : 0 ≤ (l : ℝ)+RiccatiLogDerivative.gamma l R+2-R)]

theorem irregular_bound (l : ℕ) (R : ℝ) (hR : 0 < R) :
    |irregular l R| ≤ coefficient l l/R^l*Real.exp R :=
  (Complex.abs_im_le_norm _).trans (xi_exponential_bound l R hR)

theorem irregularD_bound (l : ℕ) (R : ℝ) (hR : 0 < R) :
    |irregularD l R| ≤ (1+l/R)*(coefficient l l/R^l*Real.exp R) :=
  (Complex.abs_im_le_norm _).trans (xiD_exponential_bound l R hR)

theorem load_quotient_bound (U D C Dχ Cχ L R β : ℝ)
    (hU : 0 < U) (hD : 0 < D) (hC : 0 ≤ C) (hR : 0 < R)
    (hload : β*U ≤ R*D) (hfactor : R+L ≤ 3*β)
    (hχ : Cχ ≤ C) (hχD : Dχ ≤ (1+L/R)*C) :
    Dχ/D+Cχ/U ≤ 4*C/U := by
  have hterm : (1+L/R)*U ≤ 3*D := by
    have he : (1+L/R)*U = (R+L)*U/R := by field_simp [hR.ne']
    rw [he]
    apply (div_le_iff₀ hR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hfactor hU.le]
  have hfirst : Dχ/D ≤ 3*C/U := by
    apply (div_le_div_iff₀ hD hU).mpr
    nlinarith [mul_le_mul_of_nonneg_right hχD hU.le,mul_le_mul_of_nonneg_left hterm hC]
  have hsecond : Cχ/U ≤ C/U := div_le_div_of_nonneg_right hχ hU.le
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

theorem reaction_majorant_simplify (l : ℕ) (a b s R E : ℝ) (hR : R ≠ 0) (hb : b ≠ 0) :
    (4*(a/R^l*Real.exp R)/(b*R^(l+1)*Real.exp (-E)))*(b*s^(l+1))^2 =
      4*(a*b)*Real.exp (R+E)*s^(2*l+2)/R^(2*l+1) := by
  rw [Real.exp_neg,Real.exp_add,show 2*l+2=2*(l+1) by omega,
    show 2*l+1=l+(l+1) by omega,pow_mul,pow_add]
  field_simp [hR,hb,Real.exp_ne_zero]
  ring

theorem actual_reaction_high_order (l : ℕ) (gs : List RadialStack.Layer) (R X s : ℝ)
    (hR : 0 < R) (hX : 0 < X) (hs : 0 < s) (hsR : s ≤ R) (hl : 2*R ≤ l)
    (hstack : ∀ g ∈ gs, g.q^2*g.b^2 ≤ HankelEnergy.angular l) :
    ‖RadialSource.gamma l gs R X hR‖*(regular l s)^2 ≤
      4*Real.exp (3*R/2)*s^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1)) := by
  let β := RiccatiLogDerivative.gamma l R
  let A := coefficient l l/R^l*Real.exp R
  let B := amplitude l 0
  let E := R^2/(2*((l : ℝ)+β+2))
  have hb := high_order_barrier l R hR hl
  obtain ⟨hU,hD⟩ := barrier_positive l R hR hb R ⟨hR,le_rfl⟩
  have hβ : β*regular l R ≤ R*regularD l R :=
    (le_div_iff₀ hU).mp (RiccatiLogDerivative.barrier_logDerivative_bounds l R hR hb R ⟨hR,le_rfl⟩).1
  have hfactor : R+(l : ℝ) ≤ 3*β := by
    have hh := gamma_ge_half_degree l R hR hl
    dsimp [β]
    linarith
  have hA : 0 < A := mul_pos (div_pos (coefficient_pos l l) (pow_pos hR _)) (Real.exp_pos R)
  have hΓ : ‖RadialSource.gamma l gs R X hR‖ ≤ 4*A/regular l R :=
    (RadialLoadBounds.actual_gamma_barrier_bound l gs R X hR hX hb hstack).trans
      (load_quotient_bound _ _ A _ _ l R β hU hD hA.le hR hβ hfactor
        (irregular_bound l R hR) (irregularD_bound l R hR))
  have hB : 0 < B := amplitude_pos l 0
  have hlow : B*R^(l+1)*Real.exp (-E) ≤ regular l R := by
    simpa only [B,E,β,neg_div] using regular_gaussian_lower l R hR hb R ⟨hR,le_rfl⟩
  have hlowpos : 0 < B*R^(l+1)*Real.exp (-E) := by positivity
  have hspos := (barrier_positive l R hR hb s ⟨hs,hsR⟩).1
  have hsupper : regular l s ≤ B*s^(l+1) := regular_upper l R hR hb s ⟨hs,hsR⟩
  have hssq : (regular l s)^2 ≤ (B*s^(l+1))^2 :=
    pow_le_pow_left₀ hspos.le hsupper 2
  have hbase : ‖RadialSource.gamma l gs R X hR‖*(regular l s)^2 ≤
      (4*A/(B*R^(l+1)*Real.exp (-E)))*(B*s^(l+1))^2 := by
    exact mul_le_mul (hΓ.trans (div_le_div_of_nonneg_left (by positivity) hlowpos hlow))
      hssq (sq_nonneg _) (by positivity)
  have hprod : coefficient l l*B = 1/(2*l+1 : ℝ) := leading_amplitude_product l
  have hE : E ≤ R/2 := gaussian_exponent_le l R hR hl
  calc
    _ ≤ _ := hbase
    _ = 4*(coefficient l l*B)*Real.exp (R+E)*s^(2*l+2)/R^(2*l+1) :=
      reaction_majorant_simplify l _ B s R E hR.ne' hB.ne'
    _ = 4*Real.exp (R+E)*s^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1)) := by
      rw [hprod]
      field_simp [hR.ne']
    _ ≤ _ := by
      have he : Real.exp (R+E) ≤ Real.exp (3*R/2) := Real.exp_le_exp.mpr (by linarith)
      have hm := mul_le_mul_of_nonneg_left he
        (by positivity : 0 ≤ 4*s^(2*l+2)/((2*l+1 : ℝ)*R^(2*l+1)))
      convert hm using 1 <;> ring

end OQ14.RadialHighOrderBound
#print axioms OQ14.RadialHighOrderBound.leading_amplitude_product
#print axioms OQ14.RadialHighOrderBound.high_order_barrier
#print axioms OQ14.RadialHighOrderBound.gamma_ge_half_degree
#print axioms OQ14.RadialHighOrderBound.gaussian_exponent_le
#print axioms OQ14.RadialHighOrderBound.irregular_bound
#print axioms OQ14.RadialHighOrderBound.irregularD_bound
#print axioms OQ14.RadialHighOrderBound.load_quotient_bound
#print axioms OQ14.RadialHighOrderBound.reaction_majorant_simplify
#print axioms OQ14.RadialHighOrderBound.actual_reaction_high_order
