import ModalAlgebra
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.MeanValue

/-!
# General finite-Hankel coefficient and differential identities

This module derives the differential equation and the exact Wronskian in
every degree from the actual factorial series in ModalAlgebra. The finite
inverse-coordinate polynomial supplies the Wronskian normalization; neither
the equation nor the normalization is assumed. The resulting nonvanishing
of matching coefficients discharges the coefficient hypotheses in the
general multiple-pole rational condition. Transcendence and resonance
existence are separate, unformalized steps.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalWronskian

open Complex OQ14.ModalAlgebra

theorem factorial_cast_ne_zero (n : ℕ) : (Nat.factorial n : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

theorem hankelCoeff_recurrence (l s : ℕ) (phase : ℂ) (hs : s < l) :
    2 * (s + 1 : ℕ) * hankelCoeff l (s + 1) phase =
      phase * (l + s + 1 : ℕ) * (l - s : ℕ) * hankelCoeff l s phase := by
  have hsub : l - s = l - (s + 1) + 1 := by omega
  have hfact : (Nat.factorial (l - s) : ℂ) =
      (l - s : ℕ) * (Nat.factorial (l - (s + 1)) : ℂ) := by
    have h : Nat.factorial (l - s) = (l - s) * Nat.factorial (l - (s + 1)) := by
      conv_lhs => rw [hsub, Nat.factorial_succ]
      rw [← hsub]
    exact_mod_cast h
  have hsp : (s : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero s
  have hls : ((l - s : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.sub_ne_zero_of_lt hs
  have htwo : (2 : ℂ) ≠ 0 := by norm_num
  unfold hankelCoeff
  rw [show l + (s + 1) = l + s + 1 by omega]
  rw [Nat.factorial_succ, Nat.factorial_succ, pow_succ, pow_succ]
  push_cast
  rw [hfact]
  field_simp [factorial_cast_ne_zero, hsp, hls, htwo, mul_ne_zero, pow_ne_zero]
  ring

theorem hankelCoeff_ode_relation (l s : ℕ) (phase : ℂ)
    (hp : phase ^ 2 = -1) (hs : s < l) :
    2 * phase * (s + 1 : ℕ) * hankelCoeff l (s + 1) phase =
      ((s : ℂ) * (s + 1) - (l : ℂ) * (l + 1)) * hankelCoeff l s phase := by
  have hr := hankelCoeff_recurrence l s phase hs
  have hle : s ≤ l := Nat.le_of_lt hs
  push_cast at hr ⊢
  rw [Nat.cast_sub hle] at hr
  linear_combination phase * hr +
    ((l : ℂ) + s + 1) * ((l : ℂ) - s) * hankelCoeff l s phase * hp

theorem square_mul_zpow (z : ℂ) (hz : z ≠ 0) (m : ℤ) :
    z ^ 2 * z ^ m = z ^ (m + 2) := by
  calc
    z ^ 2 * z ^ m = z ^ (2 : ℤ) * z ^ m := by norm_num; exact Or.inl rfl
    _ = z ^ ((2 : ℤ) + m) := (zpow_add₀ hz _ _).symm
    _ = z ^ (m + 2) := by congr 1; omega

theorem scaled_poly_second_derivative (l : ℕ) (phase z : ℂ) (hz : z ≠ 0) :
    z ^ 2 * hankelPolyDD l phase z =
      ∑ s ∈ Finset.range (l + 1),
        hankelCoeff l s phase * ((s : ℂ) * (s + 1)) * z ^ (-(s : ℤ)) := by
  unfold hankelPolyDD
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have he : -(s : ℤ) - 1 - 1 + 2 = -(s : ℤ) := by omega
  calc
    z ^ 2 * (hankelCoeff l s phase *
        ((-(s : ℤ) : ℂ) * ((-(s : ℤ) - 1 : ℤ) * z ^ (-(s : ℤ) - 1 - 1)))) =
        hankelCoeff l s phase * ((s : ℂ) * (s + 1)) *
          (z ^ 2 * z ^ (-(s : ℤ) - 1 - 1)) := by push_cast; ring
    _ = _ := by rw [square_mul_zpow z hz, he]

theorem scaled_poly_first_derivative (l : ℕ) (phase z : ℂ) (hz : z ≠ 0) :
    z ^ 2 * hankelPolyD l phase z =
      ∑ s ∈ Finset.range l,
        -((s + 1 : ℕ) : ℂ) * hankelCoeff l (s + 1) phase * z ^ (-(s : ℤ)) := by
  unfold hankelPolyD
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Int.cast_zero, neg_zero, zero_mul, mul_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  have he : -((s + 1 : ℕ) : ℤ) - 1 + 2 = -(s : ℤ) := by omega
  calc
    z ^ 2 * (hankelCoeff l (s + 1) phase *
        ((-((s + 1 : ℕ) : ℤ) : ℂ) * z ^ (-((s + 1 : ℕ) : ℤ) - 1))) =
        -((s + 1 : ℕ) : ℂ) * hankelCoeff l (s + 1) phase *
          (z ^ 2 * z ^ (-((s + 1 : ℕ) : ℤ) - 1)) := by push_cast; ring
    _ = _ := by rw [square_mul_zpow z hz, he]

/-- The general radial polynomial equation is obtained by cancellation
of adjacent terms in the actual finite factorial series. -/
theorem hankelPoly_scaled_ode (l : ℕ) (phase z : ℂ)
    (hp : phase ^ 2 = -1) (hz : z ≠ 0) :
    z ^ 2 * hankelPolyDD l phase z +
      2 * phase * z ^ 2 * hankelPolyD l phase z -
      (l : ℂ) * (l + 1) * hankelPoly l phase z = 0 := by
  let ν : ℂ := (l : ℂ) * (l + 1)
  have hrest : z ^ 2 * hankelPolyDD l phase z - ν * hankelPoly l phase z =
      ∑ s ∈ Finset.range l,
        ((s : ℂ) * (s + 1) - ν) * hankelCoeff l s phase * z ^ (-(s : ℤ)) := by
    rw [scaled_poly_second_derivative l phase z hz]
    unfold hankelPoly
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_range_succ]
    have hlast : hankelCoeff l l phase * ((l : ℂ) * (l + 1)) * z ^ (-(l : ℤ)) -
        ν * (hankelCoeff l l phase * z ^ (-(l : ℤ))) = 0 := by dsimp [ν]; ring
    rw [hlast, add_zero]
    apply Finset.sum_congr rfl
    intro s _
    ring
  calc
    z ^ 2 * hankelPolyDD l phase z +
        2 * phase * z ^ 2 * hankelPolyD l phase z -
        (l : ℂ) * (l + 1) * hankelPoly l phase z =
        (z ^ 2 * hankelPolyDD l phase z - ν * hankelPoly l phase z) +
          2 * phase * (z ^ 2 * hankelPolyD l phase z) := by dsimp [ν]; ring
    _ = (∑ s ∈ Finset.range l,
          ((s : ℂ) * (s + 1) - ν) * hankelCoeff l s phase * z ^ (-(s : ℤ))) +
        2 * phase * (∑ s ∈ Finset.range l,
          -((s + 1 : ℕ) : ℂ) * hankelCoeff l (s + 1) phase * z ^ (-(s : ℤ))) := by
      rw [hrest, scaled_poly_first_derivative l phase z hz]
    _ = ∑ s ∈ Finset.range l,
        (((s : ℂ) * (s + 1) - ν) * hankelCoeff l s phase -
          2 * phase * (s + 1 : ℕ) * hankelCoeff l (s + 1) phase) * z ^ (-(s : ℤ)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      have hr := hankelCoeff_ode_relation l s phase hp (Finset.mem_range.mp hs)
      dsimp [ν]
      linear_combination -(z ^ (-(s : ℤ))) * hr

theorem hankelPoly_ode (l : ℕ) (phase z : ℂ)
    (hp : phase ^ 2 = -1) (hz : z ≠ 0) :
    hankelPolyDD l phase z + 2 * phase * hankelPolyD l phase z =
      ((l : ℂ) * (l + 1) / z ^ 2) * hankelPoly l phase z := by
  have h := hankelPoly_scaled_ode l phase z hp hz
  field_simp [hz]
  linear_combination h

theorem xiD_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (xiD l)
      ((((l : ℂ) * (l + 1)) / z ^ 2 - 1) * xi l z) z := by
  have he : HasDerivAt (fun w : ℂ => exp (I * w)) (exp (I * z) * I) z :=
    by simpa using ((hasDerivAt_id z).const_mul I).cexp
  have hp := hankelPoly_hasDerivAt l I z hz
  have hd := hankelPolyD_hasDerivAt l I z hz
  have ho := hankelPoly_ode l I z (by norm_num) hz
  convert (he.const_mul ((-I) ^ (l + 1))).mul ((hp.const_mul I).add hd) using 1
  dsimp [xi, p]
  linear_combination (norm := ring_nf) -((-I) ^ (l + 1) * exp (I * z)) * ho
  norm_num [pow_succ, I_sq]

theorem xiMinusD_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (xiMinusD l)
      ((((l : ℂ) * (l + 1)) / z ^ 2 - 1) * xiMinus l z) z := by
  have he : HasDerivAt (fun w : ℂ => exp (-I * w)) (exp (-I * z) * (-I)) z :=
    by simpa using ((hasDerivAt_id z).const_mul (-I)).cexp
  have hp := hankelPoly_hasDerivAt l (-I) z hz
  have hd := hankelPolyD_hasDerivAt l (-I) z hz
  have ho := hankelPoly_ode l (-I) z (by norm_num) hz
  convert (he.const_mul (I ^ (l + 1))).mul ((hp.const_mul (-I)).add hd) using 1
  dsimp [xiMinus, pMinus]
  linear_combination (norm := ring_nf) -(I ^ (l + 1) * exp (-I * z)) * ho
  norm_num [pow_succ, I_sq]

def wronskian (l : ℕ) (z : ℂ) : ℂ :=
  xi l z * xiMinusD l z - xiMinus l z * xiD l z

theorem wronskian_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (wronskian l) 0 z := by
  convert ((xi_hasDerivAt l z hz).mul (xiMinusD_hasDerivAt l z hz)).sub
    ((xiMinus_hasDerivAt l z hz).mul (xiD_hasDerivAt l z hz)) using 1 <;> ring

def inversePoly (l : ℕ) (phase w : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (l + 1), hankelCoeff l s phase * w ^ s

def inversePolyD (l : ℕ) (phase w : ℂ) : ℂ :=
  ∑ s ∈ Finset.range (l + 1), hankelCoeff l s phase * ((s : ℂ) * w ^ (s - 1))

theorem inversePoly_hasDerivAt (l : ℕ) (phase w : ℂ) :
    HasDerivAt (inversePoly l phase) (inversePolyD l phase w) w := by
  apply HasDerivAt.sum
  intro s _
  exact (hasDerivAt_pow s w).const_mul (hankelCoeff l s phase)

theorem inversePolyD_differentiable (l : ℕ) (phase : ℂ) :
    Differentiable ℂ (inversePolyD l phase) := by
  intro w
  apply DifferentiableAt.sum
  intro s _
  exact ((differentiableAt_pow (s - 1)).const_mul (s : ℂ)).const_mul
    (hankelCoeff l s phase)

theorem inversePoly_eq (l : ℕ) (phase w : ℂ) :
    inversePoly l phase w = hankelPoly l phase w⁻¹ := by
  unfold inversePoly hankelPoly
  apply Finset.sum_congr rfl
  intro s _
  simp

theorem inversePoly_zero (l : ℕ) (phase : ℂ) :
    inversePoly l phase 0 = 1 := by
  unfold inversePoly
  rw [Finset.sum_range_succ']
  simp [hankelCoeff, factorial_cast_ne_zero]
  exact div_self (factorial_cast_ne_zero l)

theorem inversePolyD_opposite_zero (l : ℕ) (phase : ℂ) :
    inversePolyD l phase 0 + inversePolyD l (-phase) 0 = 0 := by
  unfold inversePolyD
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro s _
  rcases s with _ | s
  · simp
  rcases s with _ | s
  · norm_num [hankelCoeff]
    ring
  · simp

theorem inversePolyD_eq (l : ℕ) (phase w : ℂ) (hw : w ≠ 0) :
    hankelPolyD l phase w⁻¹ = -w ^ 2 * inversePolyD l phase w := by
  have hc := (hankelPoly_hasDerivAt l phase w⁻¹ (inv_ne_zero hw)).comp w
    ((hasDerivAt_id w).inv hw)
  have heq : (fun x : ℂ => hankelPoly l phase x⁻¹) = inversePoly l phase :=
    funext (fun x => (inversePoly_eq l phase x).symm)
  dsimp only [Function.comp_def] at hc
  rw [heq] at hc
  have hd := hc.unique (inversePoly_hasDerivAt l phase w)
  dsimp at hd
  field_simp [hw] at hd
  simp only [one_div] at hd
  linear_combination -hd

theorem wronskian_laurent (l : ℕ) (z : ℂ) :
    wronskian l z = p l z * pMinusD l z - pMinus l z * pD l z -
      2 * I * p l z * pMinus l z := by
  have he : exp (I * z) * exp (-I * z) = 1 := by
    rw [← exp_add]
    convert exp_zero using 1 <;> congr 1 <;> ring
  have hp : (-I) ^ (l + 1) * I ^ (l + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  calc
    wronskian l z = ((-I) ^ (l + 1) * I ^ (l + 1)) *
        (exp (I * z) * exp (-I * z)) *
        (p l z * pMinusD l z - pMinus l z * pD l z -
          2 * I * p l z * pMinus l z) := by
      unfold wronskian xi xiD xiMinus xiMinusD
      ring
    _ = _ := by rw [hp, he]; ring

def inverseWronskian (l : ℕ) (w : ℂ) : ℂ :=
  w ^ 2 * (inversePoly l (-I) w * inversePolyD l I w -
    inversePoly l I w * inversePolyD l (-I) w) -
    2 * I * inversePoly l I w * inversePoly l (-I) w

theorem inverseWronskian_eq (l : ℕ) (w : ℂ) (hw : w ≠ 0) :
    inverseWronskian l w = wronskian l w⁻¹ := by
  rw [wronskian_laurent]
  unfold p pMinus pD pMinusD inverseWronskian
  rw [inversePolyD_eq l I w hw, inversePolyD_eq l (-I) w hw,
    ← inversePoly_eq l I w, ← inversePoly_eq l (-I) w]
  ring

theorem inverseWronskian_differentiable (l : ℕ) :
    Differentiable ℂ (inverseWronskian l) := by
  intro w
  have hp := (inversePoly_hasDerivAt l I w).differentiableAt
  have hm := (inversePoly_hasDerivAt l (-I) w).differentiableAt
  have hd := inversePolyD_differentiable l I w
  have hmd := inversePolyD_differentiable l (-I) w
  exact ((differentiableAt_pow 2).mul ((hm.mul hd).sub (hp.mul hmd))).sub
    ((hp.const_mul (2 * I)).mul hm)

theorem inverseWronskian_hasDerivAt_zero (l : ℕ) :
    HasDerivAt (inverseWronskian l) 0 0 := by
  have hp := inversePoly_hasDerivAt l I 0
  have hm := inversePoly_hasDerivAt l (-I) 0
  have hd := inversePolyD_differentiable l I 0
  have hmd := inversePolyD_differentiable l (-I) 0
  have haux := ((hm.differentiableAt.mul hd).sub
    (hp.differentiableAt.mul hmd)).hasDerivAt
  have h := ((hasDerivAt_pow 2 (0 : ℂ)).mul haux).sub
    ((hp.const_mul (2 * I)).mul hm)
  convert h using 1
  simp only [inversePoly_zero, zero_pow (by decide : 2 ≠ 0),
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_zero, zero_mul, zero_add, mul_one]
  have he := inversePolyD_opposite_zero l I
  linear_combination 2 * I * he

theorem inverseWronskian_hasDerivAt (l : ℕ) (w : ℂ) :
    HasDerivAt (inverseWronskian l) 0 w := by
  by_cases hw : w = 0
  · subst w
    exact inverseWronskian_hasDerivAt_zero l
  have h := (wronskian_hasDerivAt l w⁻¹ (inv_ne_zero hw)).comp w
    ((hasDerivAt_id w).inv hw)
  simp only [zero_mul] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hw] with x hx
  exact inverseWronskian_eq l x hx

/-- Exact Wronskian for every degree, derived from the factorial series.
The inverse-coordinate polynomial removes the apparent singularity at
infinity and evaluates the constant without any asymptotic assumption. -/
theorem hankel_wronskian (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    xi l z * xiMinusD l z - xiMinus l z * xiD l z = -2 * I := by
  have hc := is_const_of_deriv_eq_zero (inverseWronskian_differentiable l)
    (fun w => (inverseWronskian_hasDerivAt l w).deriv) z⁻¹ 0
  rw [inverseWronskian_eq l z⁻¹ (inv_ne_zero hz), inv_inv] at hc
  simpa [inverseWronskian, inversePoly_zero, wronskian] using hc

theorem coefficients_not_both_zero (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    ¬(cPlus l n z = 0 ∧ cMinus l n z = 0) := by
  have hnz : n * z ≠ 0 := mul_ne_zero hn hz
  have hw : xi l (n * z) * xiMinusD l (n * z) -
      xiMinus l (n * z) * xiD l (n * z) ≠ 0 := by
    rw [hankel_wronskian l _ hnz]
    norm_num
  have hx : xi l z ≠ 0 ∨ xiD l z ≠ 0 := by
    by_cases hx : xi l z = 0
    · right
      intro hdx
      have h := hankel_wronskian l z hz
      rw [hx, hdx] at h
      norm_num at h
    · exact Or.inl hx
  have hnot := matching_pair_not_both_zero n (xi l (n * z)) (xiMinus l (n * z))
    (xiD l (n * z)) (xiMinusD l (n * z)) (xi l z) (xiD l z) hn hw hx
  rintro ⟨hp, hm⟩
  apply hnot
  constructor
  · rw [matching_plus_factor, hp]
    ring
  · rw [matching_minus_factor, hm]
    ring

theorem plus_ne_zero_at_pole (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) : cPlus l n z ≠ 0 := by
  intro hp
  rw [tmDet_exp_factorization] at hd
  have hs := (mul_eq_zero.mp hd).resolve_left (determinant_prefactor_ne_zero l z)
  rw [hp, zero_mul, zero_add] at hs
  have hm := (mul_eq_zero.mp hs).resolve_right (exp_ne_zero _)
  exact coefficients_not_both_zero l n z hn hz ⟨hp, hm⟩

/-- The exact rational conditions for a hypothetical multiple pole hold
in every degree, with coefficient nonvanishing discharged by the proved
Wronskian. Transcendence is not asserted by this theorem. -/
theorem multiple_zero_rational_condition (l : ℕ) (n z : ℂ)
    (hn : n ≠ 0) (hz : z ≠ 0) (hd : tmDet l n z = 0)
    (hdd : deriv (tmDet l n) z = 0) :
    exp (2 * I * n * z) = rationalPole l n z ∧
    deriv (rationalPole l n) z = 2 * I * n * rationalPole l n z := by
  have hp := plus_ne_zero_at_pole l n z hn hz hd
  exact ⟨(tmDet_zero_iff_exp l n z hp).1 hd,
    multiple_tm_zero_forces_rational_derivative l n z hn hz hp hd hdd⟩

end OQ14.ModalWronskian

#print axioms OQ14.ModalWronskian.factorial_cast_ne_zero
#print axioms OQ14.ModalWronskian.hankelCoeff_recurrence
#print axioms OQ14.ModalWronskian.hankelCoeff_ode_relation
#print axioms OQ14.ModalWronskian.square_mul_zpow
#print axioms OQ14.ModalWronskian.scaled_poly_second_derivative
#print axioms OQ14.ModalWronskian.scaled_poly_first_derivative
#print axioms OQ14.ModalWronskian.hankelPoly_scaled_ode
#print axioms OQ14.ModalWronskian.hankelPoly_ode
#print axioms OQ14.ModalWronskian.xiD_hasDerivAt
#print axioms OQ14.ModalWronskian.xiMinusD_hasDerivAt
#print axioms OQ14.ModalWronskian.wronskian_hasDerivAt
#print axioms OQ14.ModalWronskian.inversePoly_hasDerivAt
#print axioms OQ14.ModalWronskian.inversePolyD_differentiable
#print axioms OQ14.ModalWronskian.inversePoly_eq
#print axioms OQ14.ModalWronskian.inversePoly_zero
#print axioms OQ14.ModalWronskian.inversePolyD_opposite_zero
#print axioms OQ14.ModalWronskian.inversePolyD_eq
#print axioms OQ14.ModalWronskian.wronskian_laurent
#print axioms OQ14.ModalWronskian.inverseWronskian_eq
#print axioms OQ14.ModalWronskian.inverseWronskian_differentiable
#print axioms OQ14.ModalWronskian.inverseWronskian_hasDerivAt_zero
#print axioms OQ14.ModalWronskian.inverseWronskian_hasDerivAt
#print axioms OQ14.ModalWronskian.hankel_wronskian
#print axioms OQ14.ModalWronskian.coefficients_not_both_zero
#print axioms OQ14.ModalWronskian.plus_ne_zero_at_pole
#print axioms OQ14.ModalWronskian.multiple_zero_rational_condition
