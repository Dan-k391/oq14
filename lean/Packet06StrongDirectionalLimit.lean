import Packet06PhysicalVolumeLimits
import Packet06PhaseWeightedMaximum

/-! Directional limits for the given, unchanged genuine trace vectors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet06StrongDirectionalLimit
open Filter Packet06PhysicalVolumeLimits Packet06PhaseWeightedMaximum
open scoped Topology

theorem from_given_vectors (E : ℕ → Fin 3 → ℂ) (b : ℕ → Bool) (n η : ℝ)
    (hn : 1 < n) (hη : 0 ≤ η) (W : ℕ → ℝ)
    (hw : ∀ j, W j = phasePermittivity n η (b j) * (amplitude (E j))^2)
    (hdiv : Tendsto W atTop atTop) :
    Tendsto (fun j => amplitude (E j)) atTop atTop ∧
    ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ j in atTop, E (φ j) k ≠ 0) ∧
      Tendsto (fun j => (((phasePermittivity n η (b (φ j)) : ℝ) : ℂ)*(E (φ j) k)^2)⁻¹)
        atTop (𝓝 0) := by
  let C : ℝ := 1+(1+η)*n^2
  have hC : 0 < C := by dsimp [C]; positivity
  have hp (j : ℕ) : 1 ≤ phasePermittivity n η (b j) := by
    have hn2 : 1 ≤ n^2 := by nlinarith
    cases h : b j <;> simp only [phasePermittivity,h,Bool.false_eq_true,if_false,if_true] <;>
      nlinarith [mul_nonneg hη (sq_nonneg n)]
  have hpC (j : ℕ) : phasePermittivity n η (b j) ≤ C := by
    dsimp [C]
    cases h : b j <;> simp only [phasePermittivity,h,Bool.false_eq_true,if_false,if_true] <;>
      nlinarith [mul_nonneg hη (sq_nonneg n)]
  have hE : Tendsto (fun j => amplitude (E j)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro L
    filter_upwards [hdiv.eventually_ge_atTop (C*(max 0 L)^2 + 1)] with j hj
    have hsq : W j ≤ C*(amplitude (E j))^2 := by
      rw [hw j]
      exact mul_le_mul_of_nonneg_right (hpC j) (sq_nonneg _)
    have ha : 0 ≤ amplitude (E j) := Real.sqrt_nonneg _
    have hL := le_max_right (0 : ℝ) L
    have hL0 := le_max_left (0 : ℝ) L
    have hsq' : (max 0 L)^2 < (amplitude (E j))^2 := (mul_lt_mul_left hC).mp (by linarith)
    nlinarith
  exact ⟨hE,(physical_and_directional_volumes E (fun j => phasePermittivity n η (b j)) hE hp).2⟩
end OQ14.Packet06StrongDirectionalLimit
#print axioms OQ14.Packet06StrongDirectionalLimit.from_given_vectors
