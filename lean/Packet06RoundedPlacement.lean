import Packet06PlacedPeaks
import Packet06ConcreteModalRounding
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06RoundedPlacement
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06ConcreteModalGeometry
  OQ14.Packet06ConcreteModalRounding

theorem sphere_susceptibility_positive {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (j : ℕ) (x : Maxwell.Space) (hx : x ∈ ball 0 1) :
    0 < (rounded n hn g η hη j).value (VectorFourier.coordinateMap x) := by
  have he := dielectric_values n hn g η hη j x
  have hx' : ‖x‖ < 1 := by simpa using hx
  classical
  split_ifs at he with hbody
  · nlinarith [sq_nonneg n,mul_nonneg hη (sq_nonneg n)]
  · nlinarith

theorem scaled_threshold (s s₀ M : ℝ) (hs₀ : 0 < s₀) (hs : s₀ ≤ s) :
    M ≤ (Real.sqrt s*s)*(max M 0/(Real.sqrt s₀*s₀)) := by
  have hspos : 0 < s := hs₀.trans_le hs
  have hA : 0 < Real.sqrt s₀*s₀ := mul_pos (Real.sqrt_pos.2 hs₀) hs₀
  have hB : Real.sqrt s₀*s₀ ≤ Real.sqrt s*s :=
    mul_le_mul (Real.sqrt_le_sqrt hs) hs (le_of_lt hs₀) (Real.sqrt_nonneg _)
  have hm : 0 ≤ max M 0 / (Real.sqrt s₀*s₀) := div_nonneg (le_max_right _ _) hA.le
  calc
    M ≤ max M 0 := le_max_left _ _
    _ = (Real.sqrt s₀*s₀)*(max M 0/(Real.sqrt s₀*s₀)) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hB hm

#print axioms OQ14.Packet06RoundedPlacement.sphere_susceptibility_positive
#print axioms OQ14.Packet06RoundedPlacement.scaled_threshold
end OQ14.Packet06RoundedPlacement
