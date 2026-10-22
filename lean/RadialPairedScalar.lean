import RadialScalarUniform
import RadialPairedFamily

/-! Explicit quarter-wave parity limits for the actual uniformly convergent scalar series. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialPairedScalar

open Complex Filter OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.RadialScalarUniform
open scoped Topology

def parityCoefficient (q σ : ℝ) (p l : ℕ) : ℂ :=
  if l%2=0 then -I*((q/σ)^(2*p) : ℝ) else -I*((σ/q)^(2*p) : ℝ)

theorem limiting_ratio (l p : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) :
    (limitingCoefficients l (pairs q σ hq hσ p)).1 /
      (limitingCoefficients l (pairs q σ hq hσ p)).2 = parityCoefficient q σ p l := by
  rcases Nat.mod_two_eq_zero_or_one l with hl | hl
  · have he : l=2*(l/2) := by omega
    rw [parityCoefficient,if_pos hl]
    convert OQ14.RadialParityLimit.even_ratio (l/2) p q σ hq hσ using 1
    rw [← he]
  · have he : l=2*(l/2)+1 := by omega
    rw [parityCoefficient,if_neg (by omega)]
    convert OQ14.RadialParityLimit.odd_ratio (l/2) p q σ hq hσ using 1
    rw [← he]

def parityMap (q σ : ℝ) (p k m n : ℕ) (s : ℝ) (l : ℕ) : C(Region s,ℂ) :=
  ((l+1 : ℝ)^k) • (parityCoefficient q σ p l • basisMap l m n s)

theorem limiting_map (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ)
    (p k m n : ℕ) (s : ℝ) (l : ℕ) :
    limitMap (pairs q σ hq hσ p) k m n s l = parityMap q σ p k m n s l := by
  rw [limitMap,limiting_ratio,parityMap]

theorem paired_limiting_summable (q σ s b : ℝ) (p k m n : ℕ)
    (hq : 1 ≤ q) (hσ : 1 ≤ σ) (hσq : σ ≤ q^2) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b) :
    Summable (parityMap q σ p k m n s) := by
  have h := limiting_summable (pairs q σ (zero_lt_one.trans_le hq) (zero_lt_one.trans_le hσ) p)
    q (q^2) s b k m n hq (sq_nonneg q) hb hmb hnb
    (RadialPairedFamily.pairs_parameters q σ hq hσ hσq p)
  have he : limitMap (pairs q σ (zero_lt_one.trans_le hq) (zero_lt_one.trans_le hσ) p) k m n s =
      parityMap q σ p k m n s := funext (fun l => limiting_map q σ _ _ p k m n s l)
  rw [he] at h
  exact h

theorem uniform_paired_series_limit (q σ s b : ℝ) (p k m n : ℕ)
    (hq : 1 ≤ q) (hσ : 1 ≤ σ) (hσq : σ ≤ q^2) (hb : 0 < b)
    (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b) :
    Tendsto (fun j : ℕ => ∑' l : ℕ, actualMap
      (pairs q σ (zero_lt_one.trans_le hq) (zero_lt_one.trans_le hσ) p) k m n s j l) atTop
        (𝓝 (∑' l : ℕ, parityMap q σ p k m n s l)) := by
  have h := uniform_actual_series_limit
    (pairs q σ (zero_lt_one.trans_le hq) (zero_lt_one.trans_le hσ) p)
    q (q^2) s b k m n hq (sq_nonneg q) hb hmb hnb
    (RadialPairedFamily.pairs_parameters q σ hq hσ hσq p)
  simpa only [limiting_map] using h

def teCoefficient (q : ℝ) (p l : ℕ) : ℂ :=
  if l%2=0 then -I*(q^(2*p) : ℝ) else -I*(q^(-((2*p : ℕ) : ℤ)) : ℝ)

def tmCoefficient (q : ℝ) (p l : ℕ) : ℂ :=
  if l%2=0 then -I*(q^(-((2*p : ℕ) : ℤ)) : ℝ) else -I*(q^(2*p) : ℝ)

theorem te_coefficient (q : ℝ) (p l : ℕ) : parityCoefficient q 1 p l = teCoefficient q p l := by
  simp only [parityCoefficient,teCoefficient,div_one,one_div,zpow_neg,zpow_natCast,inv_pow]

theorem tm_coefficient (q : ℝ) (hq : 0 < q) (p l : ℕ) :
    parityCoefficient q (q^2) p l = tmCoefficient q p l := by
  have he : q/q^2=q⁻¹ := by field_simp; ring
  have he' : q^2/q=q := by field_simp; ring
  simp only [parityCoefficient,tmCoefficient,he,he',zpow_neg,zpow_natCast,inv_pow]

theorem uniform_te_series_limit (q s b : ℝ) (p k m n : ℕ)
    (hq : 1 ≤ q) (hb : 0 < b) (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b) :
    Tendsto (fun j : ℕ => ∑' l : ℕ, actualMap
      (RadialPairedFamily.te q (zero_lt_one.trans_le hq) p) k m n s j l) atTop
        (𝓝 (∑' l : ℕ, ((l+1 : ℝ)^k) • (teCoefficient q p l • basisMap l m n s))) := by
  have hq2 : 1 ≤ q^2 := by nlinarith
  simpa only [RadialPairedFamily.te,parityMap,te_coefficient] using
    uniform_paired_series_limit q 1 s b p k m n hq le_rfl hq2 hb hmb hnb

theorem uniform_tm_series_limit (q s b : ℝ) (p k m n : ℕ)
    (hq : 1 ≤ q) (hb : 0 < b) (hmb : s+(m : ℝ) ≤ b) (hnb : s+(n : ℝ) ≤ b) :
    Tendsto (fun j : ℕ => ∑' l : ℕ, actualMap
      (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) p) k m n s j l) atTop
        (𝓝 (∑' l : ℕ, ((l+1 : ℝ)^k) • (tmCoefficient q p l • basisMap l m n s))) := by
  have hq2 : 1 ≤ q^2 := by nlinarith
  simpa only [RadialPairedFamily.tm,parityMap,tm_coefficient q (zero_lt_one.trans_le hq)] using
    uniform_paired_series_limit q (q^2) s b p k m n hq hq2 le_rfl hb hmb hnb

end OQ14.RadialPairedScalar

#print axioms OQ14.RadialPairedScalar.limiting_ratio
#print axioms OQ14.RadialPairedScalar.limiting_map
#print axioms OQ14.RadialPairedScalar.paired_limiting_summable
#print axioms OQ14.RadialPairedScalar.uniform_paired_series_limit
#print axioms OQ14.RadialPairedScalar.te_coefficient
#print axioms OQ14.RadialPairedScalar.tm_coefficient
#print axioms OQ14.RadialPairedScalar.uniform_te_series_limit
#print axioms OQ14.RadialPairedScalar.uniform_tm_series_limit
