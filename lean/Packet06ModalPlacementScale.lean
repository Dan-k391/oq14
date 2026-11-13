import Packet06PlacedRoundedVolumeLimits

/-! Positive totalized target-frequency placement scales coincide eventually
with the physical scale and converge to its positive limiting value. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06ModalPlacementScale
open Filter
open scoped Topology

def scale (target : ℝ) (z₀ : ℂ) (z : ℕ → ℂ) (j : ℕ) : ℝ :=
  if 0 < (z j).re then target/(z j).re else target/z₀.re

theorem target_scale (target : ℝ) (ht : 0 < target) (z₀ : ℂ) (hz₀ : 0 < z₀.re)
    (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 z₀)) :
    (∀ j, 0 < scale target z₀ z j) ∧
    Tendsto (scale target z₀ z) atTop (𝓝 (target/z₀.re)) ∧
    (∀ᶠ j in atTop, scale target z₀ z j = target/(z j).re) := by
  have hreal : Tendsto (fun j => (z j).re) atTop (𝓝 z₀.re) := Complex.continuous_re.continuousAt.tendsto.comp hz
  have hpos : ∀ᶠ j in atTop, 0 < (z j).re := (tendsto_order.mp hreal).1 0 hz₀
  have heq : ∀ᶠ j in atTop, scale target z₀ z j = target/(z j).re := by
    filter_upwards [hpos] with j hj
    simp [scale,hj]
  refine ⟨?_,?_,heq⟩
  · intro j
    by_cases hj : 0 < (z j).re <;> simp [scale,hj,div_pos ht, hz₀]
  · exact (tendsto_const_nhds.div hreal (ne_of_gt hz₀)).congr' (heq.mono (fun _ h => h.symm))
end OQ14.Packet06ModalPlacementScale
#print axioms OQ14.Packet06ModalPlacementScale.target_scale
