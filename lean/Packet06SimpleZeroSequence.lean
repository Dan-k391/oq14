import Packet06SimpleZeroGeneral
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SimpleZero
open Filter Metric Set
open scoped Topology

theorem simple_zero_sequence (U : Set ℂ) (hU : IsOpen U) (a : ℂ) (haU : a ∈ U)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hzero : f a = 0) (hder : deriv f a ≠ 0)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    ∃ z : ℕ → ℂ, Tendsto z atTop (𝓝 a) ∧
      ∀ᶠ n in atTop, F n (z n) = 0 ∧ deriv (F n) (z n) ≠ 0 := by
  classical
  obtain ⟨r, hr, _, hevent⟩ := unique_simple_zeros_near U hU a haU F f hf hzero hder hF hconv 1 zero_lt_one
  let z : ℕ → ℂ := fun n => if h : ∃ w ∈ closedBall a r, F n w = 0 then Classical.choose h else a
  have hz (n : ℕ) (h : ∃ w ∈ closedBall a r, F n w = 0) :
      z n ∈ closedBall a r ∧ F n (z n) = 0 := by
    dsimp [z]
    rw [dif_pos h]
    exact Classical.choose_spec h
  have hgood : ∀ᶠ n in atTop, z n ∈ closedBall a r ∧ F n (z n) = 0 ∧ deriv (F n) (z n) ≠ 0 ∧
      ∀ w ∈ closedBall a r, F n w = 0 → w = z n := by
    filter_upwards [hevent] with n hn
    obtain ⟨w,hw,hw0,hwder,huniq⟩ := hn
    have h := hz n ⟨w,hw,hw0⟩
    have heq : z n = w := huniq (z n) h.1 h.2
    refine ⟨h.1,h.2,?_,?_⟩
    · simpa [heq] using hwder
    · intro v hv hv0
      exact (huniq v hv hv0).trans heq.symm
  refine ⟨z,?_,?_⟩
  · apply Metric.tendsto_atTop.mpr
    intro ε hε
    apply Filter.eventually_atTop.mp
    let δ := min ε r / 2
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδε : δ < ε := by dsimp [δ]; have := min_le_left ε r; linarith
    have hδr : δ < r := by dsimp [δ]; have := min_le_right ε r; linarith
    have hnear := zeros_near_simple U hU a haU F f hf hzero hder hF hconv δ hδ
    filter_upwards [hgood,hnear] with n hn hn'
    obtain ⟨w,hw,hw0⟩ := hn'
    have hwball : w ∈ closedBall a r := mem_closedBall.mpr (le_of_lt (hw.trans hδr))
    have heq : w = z n := hn.2.2.2 w hwball hw0
    rw [←heq]
    exact hw.trans hδε
  · filter_upwards [hgood] with n hn
    exact ⟨hn.2.1,hn.2.2.1⟩
#print axioms OQ14.Packet06SimpleZero.simple_zero_sequence
end OQ14.Packet06SimpleZero
