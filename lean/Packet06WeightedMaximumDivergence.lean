import Packet06PlacedRoundedVolumeLimits
import Packet06PhaseWeightedMaximum

/-! The actual phase-weighted maxima diverge, not merely their inverses
along a possibly vanishing denominator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06WeightedMaximumDivergence
open Filter Metric Set Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PhysicalVolumeLimits Packet06RoundedVolumeLimits Packet06PhaseWeightedMaximum
  Packet06PlacedRoundedVolumeLimits Packet06PlacedPhaseField Packet06ConcreteModalRounding
open scoped Topology

theorem weighted_diverges {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (r : ℝ)
    (d : ℕ → Fin N → MaximumData) (b : ℕ → Fin N → Bool) (x : ℕ → Fin N → Maxwell.Space)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (a : Maxwell.Space) (i : Fin N)
    (hmax : ∀ᶠ j in atTop, Valid n hn g η hη (z j) (v j) j i r (d j i) ∧
      ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
        weighted n η (d j i) b' y ≤ weighted n η (d j i) (b j i) (x j i))
    (hdiv : Tendsto (fun j => amplitude (placedVector (d j i) (s j) (hs j) a)) atTop atTop) :
    Tendsto (fun j => scale (s j)^2 * weighted n η (d j i) (b j i) (x j i)) atTop atTop := by
  apply Filter.tendsto_atTop_mono' atTop _ hdiv
  filter_upwards [hmax,hdiv.eventually_ge_atTop 1] with j hj hj1
  have he : 1 ≤ phasePermittivity n η (d j i).side := by
    have hn2 : 1 ≤ n^2 := by nlinarith
    cases h : (d j i).side <;> simp only [phasePermittivity,h,Bool.false_eq_true,if_false,if_true] <;>
      nlinarith [mul_nonneg hη (sq_nonneg n)]
  have hw : (amplitude (vector (d j i)))^2 ≤ weighted n η (d j i) (d j i).side (d j i).point := by
    have hh := mul_le_mul_of_nonneg_right he (sq_nonneg (amplitude (vector (d j i))))
    simpa [weighted,vector,amplitude,physicalAmplitude] using hh
  have hh := (hw.trans (hj.2 (d j i).side (d j i).point hj.1.2.2.2.2.1))
  have hh' := mul_le_mul_of_nonneg_left hh (sq_nonneg (scale (s j)))
  rw [amplitude_placedVector] at hj1 ⊢
  have hnon : 0 ≤ scale (s j)*amplitude (vector (d j i)) := mul_nonneg (scale_pos _ (hs j)).le (Real.sqrt_nonneg _)
  nlinarith
end OQ14.Packet06WeightedMaximumDivergence
#print axioms OQ14.Packet06WeightedMaximumDivergence.weighted_diverges
