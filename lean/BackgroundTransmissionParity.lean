import RadialPairedFamily
import BackgroundCoreTransmission
import RestrictedTEActualCore
import RestrictedTEEffectiveBand

/-! The limiting transmission of the paired stacks is a pure parity gain times one global unimodular constant.

For the pair stack `pairs q σ n` (`n` pairs of a high segment of width `π/(2q)` and a low segment of width `π/2`)
the limiting transmission over two is `(-q/σ)^n e^{-I w_n}` on even degrees and `(-σ/q)^n e^{-I w_n}` on odd
degrees, `w_n = n (π/(2q) + π/2)` the total width.  The factors `phase l = (-I)^(l+1)` of the degree cancel
exactly, so the unimodular factor does not depend on the degree (nor on the parity); it depends on `n` and `q`
through `(-1)^n e^{-I w_n} = exp (I n π (q-1)/(2q))`.  For the TE family (`σ = 1`) the gains are `q^n` (even) and
`q^(-n)` (odd), for the TM family (`σ = q^2`) `q^(-n)` (even) and `q^n` (odd). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundTransmissionParity
open Complex Filter OQ14.RadialGreen OQ14.RadialStack OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit
  OQ14.RadialParityLimit OQ14.BackgroundCoreTransmission
open scoped Topology

/-! ### The width of the pair stacks -/

theorem width_pairs (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (n : ℕ) :
    width (pairs q σ hq hσ n) = (n : ℝ) * (Real.pi/(2*q) + Real.pi/2) := by
  induction n with
  | zero => simp [pairs, width]
  | succ n ih =>
    simp only [pairs, width, high, low, ih]
    push_cast
    ring

/-! ### The second limiting coefficient -/

theorem second_even (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    (limitingCoefficients (2*j) (pairs q σ hq hσ n)).2 =
      -((((-1 : ℝ)^j * (-σ/q)^n : ℝ)) : ℂ) := by
  rw [limitingCoefficients, backward_reference_pairs]
  simp only [act, RadialLayer.inverse, phaseBasis, phase_even, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im, I_re, I_im,
    mul_zero, zero_mul, mul_one, mul_neg, neg_zero, add_zero, zero_add, sub_zero, zero_sub,
    Complex.ofReal_neg, Complex.ofReal_zero, Complex.ofReal_mul]
  push_cast
  ring

theorem second_odd (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    (limitingCoefficients (2*j+1) (pairs q σ hq hσ n)).2 =
      ((((-1 : ℝ)^(j+1) * (-q/σ)^n : ℝ)) : ℂ) * I := by
  rw [limitingCoefficients, backward_reference_pairs]
  simp only [act, RadialLayer.inverse, phaseBasis, phase_odd, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, I_re, I_im, mul_zero, zero_mul, mul_one,
    add_zero, zero_add, sub_zero, Complex.ofReal_zero, Complex.ofReal_neg, Complex.ofReal_mul]
  push_cast
  ring

/-! ### The limiting transmission of the pair stacks -/

theorem gain_mul (n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    ((((-σ/q)^n : ℝ)) : ℂ) * ((((-q/σ)^n : ℝ)) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← mul_pow]
  have : (-σ/q) * (-q/σ) = 1 := by field_simp
  rw [this]
  simp

theorem alg_even (s u u2 t : ℂ) (hs : s * s = 1) (hg : u * u2 = 1) (ht : t ≠ 0) :
    2 * I / (s * (-I) * t * (-(s * u))) / 2 = u2 * t⁻¹ := by
  have hu : u ≠ 0 := by
    intro h
    rw [h, zero_mul] at hg
    exact zero_ne_one hg
  have hu2 : u2 = u⁻¹ := eq_inv_of_mul_eq_one_right hg
  have hden : s * (-I) * t * (-(s * u)) = I * (s * s) * t * u := by ring
  rw [hden, hs, hu2]
  field_simp [Complex.I_ne_zero]
  ring

theorem alg_odd (s v v2 t : ℂ) (hs : s * s = 1) (hg : v * v2 = 1) (ht : t ≠ 0) :
    2 * I / (s * t * (s * v * I)) / 2 = v2 * t⁻¹ := by
  have hv : v ≠ 0 := by
    intro h
    rw [h, zero_mul] at hg
    exact zero_ne_one hg
  have hv2 : v2 = v⁻¹ := eq_inv_of_mul_eq_one_right hg
  have hden : s * t * (s * v * I) = I * (s * s) * t * v := by ring
  rw [hden, hs, hv2]
  field_simp [Complex.I_ne_zero]
  ring

theorem limT_even (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    limitingTransmission (2*j) (pairs q σ hq hσ n) / 2 =
      ((((-q/σ)^n : ℝ)) : ℂ) * Complex.exp (-(I * (width (pairs q σ hq hσ n) : ℂ))) := by
  unfold limitingTransmission
  rw [second_even, Complex.ofReal_mul, phase_even, Complex.exp_neg]
  have hs : (((-1 : ℝ)^j : ℝ) : ℂ) * (((-1 : ℝ)^j : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← mul_pow]
    simp
  exact alg_even _ _ _ _ hs (gain_mul n q σ hq hσ) (Complex.exp_ne_zero _)

theorem limT_odd (j n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    limitingTransmission (2*j+1) (pairs q σ hq hσ n) / 2 =
      ((((-σ/q)^n : ℝ)) : ℂ) * Complex.exp (-(I * (width (pairs q σ hq hσ n) : ℂ))) := by
  unfold limitingTransmission
  rw [second_odd, Complex.ofReal_mul, phase_odd, Complex.exp_neg]
  have hs : (((-1 : ℝ)^(j+1) : ℝ) : ℂ) * (((-1 : ℝ)^(j+1) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← mul_pow]
    simp
  have hg : ((((-q/σ)^n : ℝ)) : ℂ) * ((((-σ/q)^n : ℝ)) : ℂ) = 1 := by
    rw [mul_comm]
    exact gain_mul n q σ hq hσ
  exact alg_odd _ _ _ _ hs hg (Complex.exp_ne_zero _)

/-! ### The global unimodular constant -/

/-- The global unimodular factor `(-1)^n e^{-I w_n}`, `w_n = n (π/(2q) + π/2)` the width of `n` pairs. -/
def parityPhase (q : ℝ) (n : ℕ) : ℂ :=
  ((-1 : ℂ)^n) * Complex.exp (-(I * (((n : ℝ) * (Real.pi/(2*q) + Real.pi/2) : ℝ) : ℂ)))

theorem parityPhase_norm (q : ℝ) (n : ℕ) : ‖parityPhase q n‖ = 1 := by
  unfold parityPhase
  have e : -(I * (((n : ℝ) * (Real.pi/(2*q) + Real.pi/2) : ℝ) : ℂ)) =
      ((-((n : ℝ) * (Real.pi/(2*q) + Real.pi/2)) : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, e, Complex.norm_exp_ofReal_mul_I]

theorem parityPhase_ne_zero (q : ℝ) (n : ℕ) : parityPhase q n ≠ 0 := by
  intro h
  have := parityPhase_norm q n
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem parityPhase_eq (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    parityPhase q n = Complex.exp (I * (((n : ℝ) * Real.pi * (q - 1) / (2*q) : ℝ) : ℂ)) := by
  unfold parityPhase
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
  have h1 : ((-1 : ℂ)^n) = Complex.exp ((n : ℂ) * (Real.pi * I)) := by
    rw [Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  rw [h1, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem parityPhase_succ (q : ℝ) (hq : q ≠ 0) (n : ℕ) :
    parityPhase q (n+1) = parityPhase q n * Complex.exp (I * ((Real.pi * (q - 1) / (2*q) : ℝ) : ℂ)) := by
  rw [parityPhase_eq q hq, parityPhase_eq q hq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- For `q > 1` the global constant changes at every step: it is not independent of `n`. -/
theorem parityPhase_succ_ne (q : ℝ) (hq : 1 < q) (n : ℕ) : parityPhase q (n+1) ≠ parityPhase q n := by
  have hq0 : q ≠ 0 := by positivity
  rw [parityPhase_succ q hq0]
  intro h
  have h1 : Complex.exp (I * ((Real.pi * (q - 1) / (2*q) : ℝ) : ℂ)) = 1 := by
    have hne := parityPhase_ne_zero q n
    exact (mul_eq_left₀ hne).mp h
  have hpos : 0 < Real.pi * (q - 1) / (2*q) := by
    have : 0 < q - 1 := by linarith
    positivity
  have hlt : Real.pi * (q - 1) / (2*q) < Real.pi / 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.pi_pos]
  generalize Real.pi * (q - 1) / (2*q) = θ at h1 hpos hlt
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp h1
  have him := congrArg Complex.im hm
  simp at him
  have hpi := Real.pi_pos
  by_cases hm0 : m ≤ 0
  · have : (m : ℝ) ≤ 0 := by exact_mod_cast hm0
    nlinarith
  · have : (1 : ℝ) ≤ m := by exact_mod_cast (not_le.mp hm0)
    nlinarith

/-! ### The TE and TM families -/

theorem te_even (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    limitingTransmission (2*j) (RadialPairedFamily.te q hq n) / 2 = ((q^n : ℝ) : ℂ) * parityPhase q n := by
  unfold RadialPairedFamily.te
  rw [limT_even, width_pairs, parityPhase]
  have : ((((-q/1)^n : ℝ)) : ℂ) = ((-1 : ℂ)^n) * ((q^n : ℝ) : ℂ) := by
    rw [div_one, neg_pow]
    push_cast
    ring
  rw [this]
  ring

theorem te_odd (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    limitingTransmission (2*j+1) (RadialPairedFamily.te q hq n) / 2 =
      (((q^n)⁻¹ : ℝ) : ℂ) * parityPhase q n := by
  unfold RadialPairedFamily.te
  rw [limT_odd, width_pairs, parityPhase]
  have : ((((-1/q)^n : ℝ)) : ℂ) = ((-1 : ℂ)^n) * (((q^n)⁻¹ : ℝ) : ℂ) := by
    rw [neg_div, neg_pow, div_eq_mul_inv, one_mul, inv_pow]
    push_cast
    ring
  rw [this]
  ring

theorem tm_even (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    limitingTransmission (2*j) (RadialPairedFamily.tm q hq n) / 2 =
      (((q^n)⁻¹ : ℝ) : ℂ) * parityPhase q n := by
  unfold RadialPairedFamily.tm
  rw [limT_even, width_pairs, parityPhase]
  have h2 : (-q/q^2) = -(q⁻¹) := by
    field_simp
    ring
  have : ((((-q/q^2)^n : ℝ)) : ℂ) = ((-1 : ℂ)^n) * (((q^n)⁻¹ : ℝ) : ℂ) := by
    rw [h2, neg_pow, inv_pow]
    push_cast
    ring
  rw [this]
  ring

theorem tm_odd (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    limitingTransmission (2*j+1) (RadialPairedFamily.tm q hq n) / 2 = ((q^n : ℝ) : ℂ) * parityPhase q n := by
  unfold RadialPairedFamily.tm
  rw [limT_odd, width_pairs, parityPhase]
  have h2 : (-(q^2)/q) = -q := by
    field_simp
    ring
  have : ((((-(q^2)/q)^n : ℝ)) : ℂ) = ((-1 : ℂ)^n) * ((q^n : ℝ) : ℂ) := by
    rw [h2, neg_pow]
    push_cast
    ring
  rw [this]
  ring

theorem te_even_norm (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    ‖limitingTransmission (2*j) (RadialPairedFamily.te q hq n) / 2‖ = q^n := by
  rw [te_even, norm_mul, parityPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos hq n)]

theorem te_odd_norm (j n : ℕ) (q : ℝ) (hq : 0 < q) :
    ‖limitingTransmission (2*j+1) (RadialPairedFamily.te q hq n) / 2‖ = (q^n)⁻¹ := by
  rw [te_odd, norm_mul, parityPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (pow_pos hq n))]

/-! ### The limiting degreewise transmissions of the actual device -/

open OQ14.RestrictedTEActualCore (transInf Vec TwistUnitary)
open OQ14.BackgroundCoreTransmission (scaledCoeff scaledCoeff_apply)

theorem transInf_even (q : ℝ) (hq : 1 ≤ q) (n l : ℕ) (hl : Even l) :
    transInf q hq n l = ((q^n : ℝ) : ℂ) * parityPhase q n := by
  obtain ⟨j, rfl⟩ : ∃ j, l = 2*j := ⟨l/2, by have := Nat.even_iff.mp hl; omega⟩
  exact te_even j n q (zero_lt_one.trans_le hq)

theorem transInf_odd (q : ℝ) (hq : 1 ≤ q) (n l : ℕ) (hl : ¬ Even l) :
    transInf q hq n l = (((q^n)⁻¹ : ℝ) : ℂ) * parityPhase q n := by
  obtain ⟨j, rfl⟩ : ∃ j, l = 2*j+1 := ⟨l/2, by have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hl); omega⟩
  exact te_odd j n q (zero_lt_one.trans_le hq)

theorem scaledCoeff_even (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec) (hA : ∀ k ∈ A.support, Even k.val.1) :
    scaledCoeff A (transInf q hq n) = ((q^n : ℝ) : ℂ) • (parityPhase q n • A) := by
  ext k
  rw [scaledCoeff_apply]
  by_cases hk : k ∈ A.support
  · rw [transInf_even q hq n _ (hA k hk)]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    ring
  · have : A k = 0 := Finsupp.not_mem_support_iff.mp hk
    simp [this]

theorem scaledCoeff_odd (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec) (hA : ∀ k ∈ A.support, ¬ Even k.val.1) :
    scaledCoeff A (transInf q hq n) = (((q^n)⁻¹ : ℝ) : ℂ) • (parityPhase q n • A) := by
  ext k
  rw [scaledCoeff_apply]
  by_cases hk : k ∈ A.support
  · rw [transInf_odd q hq n _ (hA k hk)]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    ring
  · have : A k = 0 := Finsupp.not_mem_support_iff.mp hk
    simp [this]

/-- The general vector: the parity gains on the two parities times the one global unimodular constant. -/
theorem scaledCoeff_parity (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec) :
    scaledCoeff A (transInf q hq n) =
      parityPhase q n • scaledCoeff A (fun l => if Even l then ((q^n : ℝ) : ℂ) else (((q^n)⁻¹ : ℝ) : ℂ)) := by
  ext k
  rw [Finsupp.smul_apply, scaledCoeff_apply, scaledCoeff_apply]
  by_cases hl : Even k.val.1
  · rw [transInf_even q hq n _ hl, if_pos hl]
    simp only [smul_eq_mul]
    ring
  · rw [transInf_odd q hq n _ hl, if_neg hl]
    simp only [smul_eq_mul]
    ring

/-! ### The effective (active) part and the physical input -/

theorem input_effective (A : Vec) :
    RestrictedTEInput.input (RestrictedTEEffectiveBand.effective A) = RestrictedTEInput.input A := by
  have h : RestrictedTEInput.rawInput (RestrictedTEEffectiveBand.effective A) =
      RestrictedTEInput.rawInput A := by
    unfold RestrictedTEInput.rawInput
    exact congrArg (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ)
      (RestrictedTEEffectiveBand.amplitudeMap_eq A)
  change (1/(Real.sqrt 2 : ℂ)) • RestrictedTEInput.rawInput (RestrictedTEEffectiveBand.effective A) =
    (1/(Real.sqrt 2 : ℂ)) • RestrictedTEInput.rawInput A
  rw [h]

theorem effective_scaledCoeff (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec) :
    RestrictedTEEffectiveBand.effective (scaledCoeff A (transInf q hq n)) =
      (((q^n : ℝ) : ℂ) * parityPhase q n) • RestrictedTEEffectiveBand.effective A := by
  classical
  ext k
  simp only [RestrictedTEEffectiveBand.effective, Finsupp.filter_apply, Finsupp.smul_apply, smul_eq_mul]
  by_cases hk : RestrictedTEEffectiveBand.Active k
  · rw [if_pos hk, if_pos hk, scaledCoeff_apply, transInf_even q hq n _ hk.1]
    ring
  · rw [if_neg hk, if_neg hk]
    ring

/-- **The physical input of the rescaled vector.**  For every finite coefficient vector (the odd and degree-zero
columns of the input vanish) the physical input of the vector rescaled degreewise by the limiting TE
transmissions over two is `q^n e^{iφ}` times the physical input of the vector, where `e^{iφ}` is the global
unimodular factor `parityPhase q n`. -/
theorem input_scaledCoeff (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec) :
    RestrictedTEInput.input (scaledCoeff A (transInf q hq n)) =
      (((q^n : ℝ) : ℂ) * parityPhase q n) • RestrictedTEInput.input A := by
  rw [← input_effective (scaledCoeff A (transInf q hq n)), effective_scaledCoeff, map_smul, input_effective]

theorem physicalPower_scaledCoeff (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec) :
    RestrictedTEIncoming.physicalPower (scaledCoeff A (transInf q hq n)) =
      (q^n)^2 * RestrictedTEIncoming.physicalPower A := by
  rw [← RestrictedTEInput.input_norm_sq, ← RestrictedTEInput.input_norm_sq, input_scaledCoeff,
    norm_smul, mul_pow, norm_mul, parityPhase_norm, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (pow_pos (zero_lt_one.trans_le hq) n)]

/-! ### The twist -/

/-- The global phase as a linear equivalence of the coefficient space. -/
def phaseTwist (c : ℂ) (hc : c ≠ 0) : Vec ≃ₗ[ℂ] Vec := LinearEquiv.smulOfNeZero ℂ Vec c hc

theorem phaseTwist_apply (c : ℂ) (hc : c ≠ 0) (x : Vec) : phaseTwist c hc x = c • x := rfl

section Unitary
open scoped ComplexInnerProductSpace

theorem phaseTwist_unitary (c : ℂ) (hc : c ≠ 0) (hn : ‖c‖ = 1) : TwistUnitary (phaseTwist c hc) := by
  intro x y
  have hcc : c * (starRingEnd ℂ) c = 1 := by
    rw [mul_comm, Complex.conj_mul', hn]
    norm_num
  simp only [phaseTwist_apply, map_smul, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, hcc, one_mul]

end Unitary

/-- The twist of the actual device: the global unimodular constant of the limiting TE transmissions. -/
def parityTwist (q : ℝ) (n : ℕ) : Vec ≃ₗ[ℂ] Vec := phaseTwist (parityPhase q n) (parityPhase_ne_zero q n)

theorem parityTwist_unitary (q : ℝ) (n : ℕ) : TwistUnitary (parityTwist q n) :=
  phaseTwist_unitary _ _ (parityPhase_norm q n)

theorem parityTwist_power (q : ℝ) (n : ℕ) (x : Vec) :
    RestrictedTEIncoming.physicalPower (parityTwist q n x) = RestrictedTEIncoming.physicalPower x :=
  (parityTwist_unitary q n).power x

/-- **The twist identity** in the form of the channel assembly: for a coefficient vector supported on even
degrees, the vector rescaled degreewise by the limiting TE transmissions over two is `q^n` times the unitary
twist of the vector, the twist being the multiplication by the global unimodular constant
`(-1)^n e^{-I w_n} = exp (I n π (q-1)/(2q))` (it does not depend on the degree). -/
theorem scaledCoeff_even_twist (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec)
    (hA : ∀ k ∈ A.support, Even k.val.1) :
    scaledCoeff A (transInf q hq n) = ((q^n : ℝ) : ℂ) • (parityTwist q n A) :=
  scaledCoeff_even q hq n A hA

/-! ### Statements in the form requested by the assembly -/

/-- **Even degrees, TE family.**  The limiting transmission over two is `q^n` times a unimodular constant that
does not depend on the degree. -/
theorem limitingTransmission_even (q : ℝ) (hq : 0 < q) (n l : ℕ) (hl : Even l) :
    limitingTransmission l (RadialPairedFamily.te q hq n) / 2 = ((q^n : ℝ) : ℂ) * parityPhase q n := by
  obtain ⟨j, rfl⟩ : ∃ j, l = 2*j := ⟨l/2, by have := Nat.even_iff.mp hl; omega⟩
  exact te_even j n q hq

/-- **Odd degrees, TE family.**  The limiting transmission over two is `q^(-n)` times the same constant. -/
theorem limitingTransmission_odd (q : ℝ) (hq : 0 < q) (n l : ℕ) (hl : ¬ Even l) :
    limitingTransmission l (RadialPairedFamily.te q hq n) / 2 = (((q^n)⁻¹ : ℝ) : ℂ) * parityPhase q n := by
  obtain ⟨j, rfl⟩ : ∃ j, l = 2*j+1 := ⟨l/2, by have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hl); omega⟩
  exact te_odd j n q hq

/-- **Even degrees, TM family.**  Gain `q^(-n)`. -/
theorem limitingTransmission_tm_even (q : ℝ) (hq : 0 < q) (n l : ℕ) (hl : Even l) :
    limitingTransmission l (RadialPairedFamily.tm q hq n) / 2 = (((q^n)⁻¹ : ℝ) : ℂ) * parityPhase q n := by
  obtain ⟨j, rfl⟩ : ∃ j, l = 2*j := ⟨l/2, by have := Nat.even_iff.mp hl; omega⟩
  exact tm_even j n q hq

/-- **Odd degrees, TM family.**  Gain `q^n`. -/
theorem limitingTransmission_tm_odd (q : ℝ) (hq : 0 < q) (n l : ℕ) (hl : ¬ Even l) :
    limitingTransmission l (RadialPairedFamily.tm q hq n) / 2 = ((q^n : ℝ) : ℂ) * parityPhase q n := by
  obtain ⟨j, rfl⟩ : ∃ j, l = 2*j+1 := ⟨l/2, by have := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp hl); omega⟩
  exact tm_odd j n q hq

/-- The twist identity with the gain written as `(q : ℂ)^n`. -/
theorem scaledCoeff_even_literal (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (A : Vec)
    (hA : ∀ k ∈ A.support, Even k.val.1) :
    scaledCoeff A (fun l => limitingTransmission l (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) / 2) =
      ((q : ℂ)^n) • (parityTwist q n A) := by
  have h := scaledCoeff_even_twist q hq n A hA
  simpa using h

end OQ14.BackgroundTransmissionParity
#print axioms OQ14.BackgroundTransmissionParity.te_even
#print axioms OQ14.BackgroundTransmissionParity.te_odd
#print axioms OQ14.BackgroundTransmissionParity.tm_even
#print axioms OQ14.BackgroundTransmissionParity.tm_odd
#print axioms OQ14.BackgroundTransmissionParity.te_even_norm
#print axioms OQ14.BackgroundTransmissionParity.te_odd_norm
#print axioms OQ14.BackgroundTransmissionParity.transInf_even
#print axioms OQ14.BackgroundTransmissionParity.transInf_odd
#print axioms OQ14.BackgroundTransmissionParity.scaledCoeff_even
#print axioms OQ14.BackgroundTransmissionParity.scaledCoeff_odd
#print axioms OQ14.BackgroundTransmissionParity.scaledCoeff_parity
#print axioms OQ14.BackgroundTransmissionParity.input_effective
#print axioms OQ14.BackgroundTransmissionParity.effective_scaledCoeff
#print axioms OQ14.BackgroundTransmissionParity.input_scaledCoeff
#print axioms OQ14.BackgroundTransmissionParity.physicalPower_scaledCoeff
#print axioms OQ14.BackgroundTransmissionParity.phaseTwist_apply
#print axioms OQ14.BackgroundTransmissionParity.phaseTwist_unitary
#print axioms OQ14.BackgroundTransmissionParity.parityTwist_unitary
#print axioms OQ14.BackgroundTransmissionParity.parityTwist_power
#print axioms OQ14.BackgroundTransmissionParity.scaledCoeff_even_twist
#print axioms OQ14.BackgroundTransmissionParity.limitingTransmission_even
#print axioms OQ14.BackgroundTransmissionParity.limitingTransmission_odd
#print axioms OQ14.BackgroundTransmissionParity.limitingTransmission_tm_even
#print axioms OQ14.BackgroundTransmissionParity.limitingTransmission_tm_odd
#print axioms OQ14.BackgroundTransmissionParity.scaledCoeff_even_literal
#print axioms OQ14.BackgroundTransmissionParity.width_pairs
#print axioms OQ14.BackgroundTransmissionParity.second_even
#print axioms OQ14.BackgroundTransmissionParity.second_odd
#print axioms OQ14.BackgroundTransmissionParity.gain_mul
#print axioms OQ14.BackgroundTransmissionParity.alg_even
#print axioms OQ14.BackgroundTransmissionParity.alg_odd
#print axioms OQ14.BackgroundTransmissionParity.limT_even
#print axioms OQ14.BackgroundTransmissionParity.limT_odd
#print axioms OQ14.BackgroundTransmissionParity.parityPhase_norm
#print axioms OQ14.BackgroundTransmissionParity.parityPhase_ne_zero
#print axioms OQ14.BackgroundTransmissionParity.parityPhase_eq
#print axioms OQ14.BackgroundTransmissionParity.parityPhase_succ
#print axioms OQ14.BackgroundTransmissionParity.parityPhase_succ_ne
