import Packet06FrameWeightedMaximum
import Packet06PhysicalVolumeLimits

/-! Divergent genuine weighted maxima yield a fixed Cartesian directional
mode-volume subsequence at actual one-sided maximizing fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06WeightedDirectionalFamily
open Filter Metric Set Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum Packet06PhaseWeightedMaximum
  Packet06RigidWeightedMaximum Packet06FrameWeightedMaximum Packet06PhysicalVolumeLimits
open scoped Topology
abbrev Space := Maxwell.Space

theorem directional_from_weighted {N : ℕ} (z : ℕ → ℂ) (r M B : ℕ → ℝ)
    (d : ∀ j, Packet06RigidHotspotState.State N (z j) (r j) (M j) (B j)) (i : Fin N)
    (n η : ℝ) (hn : 1 < n) (hη : 0 ≤ η) (W : ℕ → ℝ)
    (hmax : ∀ j, HasValue (d j) i n η (W j)) (hdiv : Tendsto W atTop atTop) :
    ∃ (inside outside : ℕ → Fin 3 → Space → ℂ) (b : ℕ → Bool) (x : ℕ → Space),
      (∀ j, HasWeightedMaximum (d j).material (z j) (d j).unknown (d j).body
        (closedBall ((d j).center i) (r j)) n η (inside j) (outside j) (b j) (x j)) ∧
      (∀ j, W j = phasePermittivity n η (b j) *
        (physicalAmplitude (phaseField (inside j) (outside j) (b j)) (x j))^2) ∧
      Tendsto (fun j => amplitude (fun k => phaseField (inside j) (outside j) (b j) k (x j))) atTop atTop ∧
      ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, phaseField (inside (φ j)) (outside (φ j)) (b (φ j)) k (x (φ j)) ≠ 0) ∧
        Tendsto (fun j => (((phasePermittivity n η (b (φ j)) : ℝ) : ℂ)*
          (phaseField (inside (φ j)) (outside (φ j)) (b (φ j)) k (x (φ j)))^2)⁻¹) atTop (𝓝 0) := by
  classical
  choose inside outside b x hm hw using hmax
  let E : ℕ → Fin 3 → ℂ := fun j k => phaseField (inside j) (outside j) (b j) k (x j)
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
  have hd := (physical_and_directional_volumes E (fun j => phasePermittivity n η (b j)) hE hp).2
  exact ⟨inside,outside,b,x,hm,hw,hE,hd⟩
end OQ14.Packet06WeightedDirectionalFamily
#print axioms OQ14.Packet06WeightedDirectionalFamily.directional_from_weighted
