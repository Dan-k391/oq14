import Packet06RoundedVolumeLimits
import Packet06PlacedPhaseField

/-! Variable normalized placements preserve the actual diverging maxima and
physical inverse-square volume limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06PlacedRoundedVolumeLimits
open Filter Maxwell Packet06PlacedPhaseField Packet06PlacementHomeomorph
  Packet06RoundedVolumeLimits Packet06PhysicalVolumeLimits Packet05ActualMaximum
open scoped Topology
abbrev Space := Maxwell.Space

def placedVector (d : MaximumData) (s : ℝ) (hs : 0 < s) (a : Space) : Fin 3 → ℂ :=
  fun k => transport s hs a (Packet05BinaryPhaseMaximum.phaseField d.inside d.outside d.side) k
    ((placement s hs a) d.point)

theorem amplitude_placedVector (d : MaximumData) (s : ℝ) (hs : 0 < s) (a : Space) :
    amplitude (placedVector d s hs a) = scale s * amplitude (vector d) := by
  simpa [amplitude, placedVector, vector, physicalAmplitude] using
    amplitude_transport s hs a (Packet05BinaryPhaseMaximum.phaseField d.inside d.outside d.side)
      ((placement s hs a) d.point)

theorem variable_placement_volume (d : ℕ → MaximumData) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (s₀ : ℝ) (hs₀ : 0 < s₀) (hscale : Tendsto s atTop (𝓝 s₀)) (a : Space)
    (c : ℕ → StaticCoefficient.Coefficient)
    (hc : ∀ j x, 1 ≤ MaterialMaxwell.dielectric (c j) x)
    (hmax : Tendsto (fun j => amplitude (vector (d j))) atTop atTop) :
    Tendsto (fun j => amplitude (placedVector (d j) (s j) (hs j) a)) atTop atTop ∧
    Tendsto (fun j => 1/(MaterialMaxwell.dielectric
      (Packet06PlacedKernel.placedCoefficient (s j) a (c j)) ((placement (s j) (hs j) a) (d j).point) *
      (amplitude (placedVector (d j) (s j) (hs j) a))^2)) atTop (𝓝 0) ∧
    ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ j in atTop, placedVector (d (φ j)) (s (φ j)) (hs (φ j)) a k ≠ 0) ∧
      Tendsto (fun j => (((MaterialMaxwell.dielectric
        (Packet06PlacedKernel.placedCoefficient (s (φ j)) a (c (φ j)))
        ((placement (s (φ j)) (hs (φ j)) a) (d (φ j)).point) : ℝ) : ℂ)*
        (placedVector (d (φ j)) (s (φ j)) (hs (φ j)) a k)^2)⁻¹) atTop (𝓝 0) := by
  have hcont : Continuous scale := Real.continuous_sqrt.mul continuous_id
  have hsc := hcont.continuousAt.tendsto.comp hscale
  have hcpos : 0 < scale s₀/2 := half_pos (scale_pos s₀ hs₀)
  have hevent : ∀ᶠ j in atTop, scale s₀/2 ≤ scale (s j) :=
    (tendsto_order.mp hsc).1 _ (by linarith [scale_pos s₀ hs₀]) |>.mono (fun _ h => h.le)
  have hdiv : Tendsto (fun j => amplitude (placedVector (d j) (s j) (hs j) a)) atTop atTop := by
    apply Filter.tendsto_atTop.mpr
    intro M
    filter_upwards [hevent,hmax.eventually_ge_atTop (max 0 (M/(scale s₀/2)))] with j hj hjm
    rw [amplitude_placedVector]
    have hn : 0 ≤ amplitude (vector (d j)) := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_right hj hn
    have hM : M ≤ (scale s₀/2)*amplitude (vector (d j)) := by
      have := le_max_right (0 : ℝ) (M/(scale s₀/2))
      have := le_trans this hjm
      simpa [mul_comm] using (div_le_iff₀ hcpos).mp this
    exact hM.trans hh
  have hε (j : ℕ) : 1 ≤ MaterialMaxwell.dielectric
      (Packet06PlacedKernel.placedCoefficient (s j) a (c j)) ((placement (s j) (hs j) a) (d j).point) := by
    rw [Packet06BoundedModalMaterial.placed_dielectric]
    exact hc j _
  have h := physical_and_directional_volumes (fun j => placedVector (d j) (s j) (hs j) a)
    (fun j => MaterialMaxwell.dielectric (Packet06PlacedKernel.placedCoefficient (s j) a (c j))
      ((placement (s j) (hs j) a) (d j).point)) hdiv hε
  exact ⟨hdiv,h.1,h.2⟩
end OQ14.Packet06PlacedRoundedVolumeLimits
#print axioms OQ14.Packet06PlacedRoundedVolumeLimits.amplitude_placedVector
#print axioms OQ14.Packet06PlacedRoundedVolumeLimits.variable_placement_volume
