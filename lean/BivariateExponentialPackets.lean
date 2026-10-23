import EntireRealIdentity

/-! Actual finite two-variable exponential-polynomial independence on a real rectangle. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BivariateExponentialPackets
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def row (μ : ι → κ → ℂ) (A : ι → κ → Fin 3 → Fin 3 → ℂ) (i : ι) (r : Fin 3) (t : ℂ) : ℂ :=
  ∑ j, (A i j r 0+A i j r 1*t+A i j r 2*t^2)*Complex.exp (μ i j*t)

def expression (ζ : ι → ℂ) (μ : ι → κ → ℂ) (A : ι → κ → Fin 3 → Fin 3 → ℂ) (s t : ℂ) : ℂ :=
  ∑ i, (row μ A i 0 t+row μ A i 1 t*s+row μ A i 2 t*s^2)*Complex.exp (ζ i*s)

theorem double_sum (ζ : ι → ℂ) (μ : ι → κ → ℂ) (A : ι → κ → Fin 3 → Fin 3 → ℂ) (s t : ℂ) :
    expression ζ μ A s t=∑ i, ∑ j,
      ((A i j 0 0+A i j 0 1*t+A i j 0 2*t^2)+
        (A i j 1 0+A i j 1 1*t+A i j 1 2*t^2)*s+
        (A i j 2 0+A i j 2 1*t+A i j 2 2*t^2)*s^2)*Complex.exp (ζ i*s+μ i j*t) := by
  unfold expression row
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul,Finset.sum_mul,← Finset.sum_add_distrib,← Finset.sum_add_distrib,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.exp_add]
  ring

theorem coefficients_zero (ζ : ι → ℂ) (μ : ι → κ → ℂ) (A : ι → κ → Fin 3 → Fin 3 → ℂ)
    (hζ : Function.Injective ζ) (hμ : ∀ i, Function.Injective (μ i)) (δ : ℝ) (hδ : 0 < δ)
    (hz : ∀ s t : ℝ, -δ < s → s < δ → -δ < t → t < δ → expression ζ μ A s t=0) :
    ∀ i j r v, A i j r v=0 := by
  have hr (t : ℝ) (hl : -δ < t) (hu : t < δ) :
      ∀ i, row μ A i 0 t=0 ∧ row μ A i 1 t=0 ∧ row μ A i 2 t=0 :=
    EntireRealIdentity.distinct_packets_on_interval ζ
      (fun i => row μ A i 0 t) (fun i => row μ A i 1 t) (fun i => row μ A i 2 t) hζ δ hδ
      (fun s hs hs' => hz s t hs hs' hl hu)
  intro i j r v
  have hzrow (t : ℝ) (hl : -δ < t) (hu : t < δ) : row μ A i r t=0 := by
    have h := hr t hl hu i
    fin_cases r
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have hc := EntireRealIdentity.distinct_packets_on_interval (μ i)
    (fun j => A i j r 0) (fun j => A i j r 1) (fun j => A i j r 2) (hμ i) δ hδ hzrow j
  fin_cases v
  · exact hc.1
  · exact hc.2.1
  · exact hc.2.2

end OQ14.BivariateExponentialPackets
#print axioms OQ14.BivariateExponentialPackets.coefficients_zero
#print axioms OQ14.BivariateExponentialPackets.double_sum
