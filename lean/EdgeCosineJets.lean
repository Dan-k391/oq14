import BivariateExponentialPackets
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Actual independence of tangential two-jets of symmetric scalar plane waves at edge points. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.EdgeCosineJets
variable {ι : Type*} [Fintype ι]

def sign (e : Fin 2) : ℂ := if e=0 then 1 else -1
def frequency (r : ℝ) (e : Fin 2) : ℂ := sign e*(Complex.I*(r : ℂ))
def vertical (y : ι → ℝ) (e : Fin 2) (j : ι) : ℂ := (sign e*Complex.I)*(y j : ℂ)

def coefficient (J : ι → Fin 6 → ℂ) (e : Fin 2) (j : ι) (a b : Fin 3) : ℂ :=
  (if a=0 then (if b=0 then J j 0 else if b=1 then sign e*Complex.I*J j 2 else -J j 5)
   else if a=1 then (if b=0 then sign e*Complex.I*J j 1 else if b=1 then -J j 4 else 0)
   else if b=0 then -J j 3 else 0)/2

def functional (r : ℝ) (y : ι → ℝ) (J : ι → Fin 6 → ℂ) (s t : ℂ) : ℂ :=
  ∑ j, ((J j 0-J j 3*s^2-J j 4*s*t-J j 5*t^2)*Complex.cos ((r : ℂ)*s+(y j : ℂ)*t)-
    (J j 1*s+J j 2*t)*Complex.sin ((r : ℂ)*s+(y j : ℂ)*t))

theorem expansion (r : ℝ) (y : ι → ℝ) (J : ι → Fin 6 → ℂ) (s t : ℂ) :
    BivariateExponentialPackets.expression (frequency r) (vertical y) (coefficient J) s t=functional r y J s t := by
  unfold functional
  rw [BivariateExponentialPackets.double_sum,Fin.sum_univ_two,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hp : ((r : ℂ)*s+(y j : ℂ)*t)*Complex.I=
      (Complex.I*(r : ℂ))*s+Complex.I*(y j : ℂ)*t := by ring
  have hm : -((r : ℂ)*s+(y j : ℂ)*t)*Complex.I=
      -(Complex.I*(r : ℂ))*s+(-Complex.I)*(y j : ℂ)*t := by ring
  dsimp [functional,coefficient,frequency,vertical,sign]
  rw [Complex.cos,Complex.sin,hp,hm]
  ring

theorem frequency_injective (r : ℝ) (hr : r ≠ 0) : Function.Injective (frequency r) := by
  have hn : Complex.I*(r : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hr)
  intro e f h
  have hs : sign e=sign f := mul_right_cancel₀ hn h
  fin_cases e <;> fin_cases f <;> norm_num [sign] at hs ⊢

theorem coefficients_zero (r : ℝ) (hr : r ≠ 0) (y : ι → ℝ) (hy : Function.Injective y)
    (J : ι → Fin 6 → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hz : ∀ s t : ℝ, -δ < s → s < δ → -δ < t → t < δ → functional r y J s t=0) :
    ∀ j a, J j a=0 := by
  have hv (e : Fin 2) : Function.Injective (vertical y e) := by
    have hs : sign e ≠ 0 := by fin_cases e <;> norm_num [sign]
    intro j k h
    apply hy
    exact_mod_cast mul_left_cancel₀ (mul_ne_zero hs Complex.I_ne_zero) h
  have hc := BivariateExponentialPackets.coefficients_zero (frequency r) (vertical y) (coefficient J)
    (frequency_injective r hr) hv δ hδ (fun s t hs hs' ht ht' =>
      (expansion r y J s t).trans (hz s t hs hs' ht ht'))
  intro j a
  have h00 := hc 0 j 0 0
  have h10 := hc 0 j 1 0
  have h01 := hc 0 j 0 1
  have h20 := hc 0 j 2 0
  have h11 := hc 0 j 1 1
  have h02 := hc 0 j 0 2
  change -J j 3/2=0 at h20
  change -J j 5/2=0 at h02
  norm_num [coefficient,sign] at h00 h10 h01 h20 h11 h02
  fin_cases a
  · exact h00
  · exact h10
  · exact h01
  · exact h20
  · exact h11
  · exact h02

end OQ14.EdgeCosineJets
#print axioms OQ14.EdgeCosineJets.expansion
#print axioms OQ14.EdgeCosineJets.frequency_injective
#print axioms OQ14.EdgeCosineJets.coefficients_zero
