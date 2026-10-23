import RadialParityLimit

/-! Literal TE/TM quarter-stack reaction limits with central-inversion parity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RadialVectorParity
open Complex OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.RadialParityLimit

def parityFactor (q : ℝ) (n l : ℕ) (tm : Bool) : ℂ :=
  I*((((q^(2*n) : ℝ) : ℂ)-1)*(1+(-1 : ℂ)^(l+if tm then 1 else 0))/2+
    ((((q^(2*n))⁻¹ : ℝ) : ℂ)-1)*(1-(-1 : ℂ)^(l+if tm then 1 else 0))/2)

theorem reaction_even (j n : ℕ) (q σ : ℝ) (hq : 0<q) (hσ : 0<σ) :
    -((limitingCoefficients (2*j) (pairs q σ hq hσ n)).1/
      (limitingCoefficients (2*j) (pairs q σ hq hσ n)).2+I)=
        I*((((q/σ)^(2*n) : ℝ) : ℂ)-1) := by
  rw [even_ratio]
  ring

theorem reaction_odd (j n : ℕ) (q σ : ℝ) (hq : 0<q) (hσ : 0<σ) :
    -((limitingCoefficients (2*j+1) (pairs q σ hq hσ n)).1/
      (limitingCoefficients (2*j+1) (pairs q σ hq hσ n)).2+I)=
        I*((((σ/q)^(2*n) : ℝ) : ℂ)-1) := by
  rw [odd_ratio]
  ring

theorem te_parity (q : ℝ) (hq : 0<q) (n l : ℕ) :
    -((limitingCoefficients l (pairs q 1 hq zero_lt_one n)).1/
      (limitingCoefficients l (pairs q 1 hq zero_lt_one n)).2+I)=parityFactor q n l false := by
  rcases Nat.even_or_odd l with ⟨j,hj⟩|⟨j,hj⟩
  · have he : l=2*j := by omega
    rw [he]
    rw [reaction_even]
    simp [parityFactor,pow_mul]
    ring
  · have he : l=2*j+1 := by omega
    rw [he]
    rw [reaction_odd]
    simp [parityFactor,pow_add,pow_mul,one_div,inv_pow]
    ring

theorem tm_parity (q : ℝ) (hq : 0<q) (n l : ℕ) :
    -((limitingCoefficients l (pairs q (q^2) hq (sq_pos_of_pos hq) n)).1/
      (limitingCoefficients l (pairs q (q^2) hq (sq_pos_of_pos hq) n)).2+I)=parityFactor q n l true := by
  have hdiv : q/q^2=q⁻¹ := by field_simp;ring
  have hdiv' : q^2/q=q := by field_simp;ring
  rcases Nat.even_or_odd l with ⟨j,hj⟩|⟨j,hj⟩
  · have he : l=2*j := by omega
    rw [he]
    rw [reaction_even,hdiv]
    simp [parityFactor,pow_add,pow_mul,inv_pow]
    ring
  · have he : l=2*j+1 := by omega
    rw [he]
    rw [reaction_odd,hdiv']
    simp [parityFactor,pow_add,pow_mul]
    ring

end OQ14.RadialVectorParity

#print axioms OQ14.RadialVectorParity.reaction_even
#print axioms OQ14.RadialVectorParity.reaction_odd
#print axioms OQ14.RadialVectorParity.te_parity
#print axioms OQ14.RadialVectorParity.tm_parity
