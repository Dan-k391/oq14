import Packet06PhaseWeightedMaximum
import Packet06StrongRoundedMaximum
import Packet06PlacedRoundedVolumeLimits

/-! A single actual modal family supplies a genuine phase-weighted maximum
and vanishing weighted physical volume on every selected ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet06AllStrongWeightedVolumes
open Set Metric Filter MeasureTheory Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum Packet06RoundedVolumeLimits Packet06PhysicalVolumeLimits
  Packet06PhaseWeightedMaximum Packet06PlacedRoundedVolumeLimits Packet06PlacedPhaseField Packet06StrongRoundedMaximum
open scoped Topology

theorem all_strong_weighted_volumes {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (hz : ∀ᶠ j in atTop, z j ≠ 0)
    (hm : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (r : ℝ) (hr : 0 < r) (hrg : r < g.radius)
    (hp : ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i : Fin N,
      0 < (volume.restrict (closedBall (g.center i) r))
      {x | M < physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x})
    (K : ℝ) (hK : 1 < K) (hceil : (1+η)*n^2 ≤ K^2)
    (s : ℕ → ℝ) (hs : ∀ j, 0 < s j) (s₀ : ℝ) (hs₀ : 0 < s₀)
    (hst : Tendsto s atTop (𝓝 s₀)) :
    ∃ (d : ℕ → Fin N → MaximumData) (b : ℕ → Fin N → Bool) (x : ℕ → Fin N → Maxwell.Space),
      (∀ᶠ j in atTop, ∀ i, StrongValid n hn g η hη (z j) (v j) j i r (d j i) ∧
        x j i ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) (b j i) ∧
        ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
          weighted n η (d j i) b' y ≤ weighted n η (d j i) (b j i) (x j i)) ∧
      (∀ i, Tendsto (fun j => amplitude (placedVector (d j i) (s j) (hs j) 0)) atTop atTop) ∧
      (∀ i, Tendsto (fun j => (scale (s j)^2 * weighted n η (d j i) (b j i) (x j i))⁻¹) atTop (𝓝 0)) ∧
      ∀ i, ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) 0 k ≠ 0) ∧
        Tendsto (fun j => (((phasePermittivity n η (d (φ j) i).side : ℝ) : ℂ)*
          (placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) 0 k)^2)⁻¹) atTop (𝓝 0) := by
  classical
  have heach (i : Fin N) := strong_maximum_family n hn g η hη z v hz hm i r hr hrg
    (fun M => (hp M).mono (fun j hj => hj i))
  choose di hdi using heach
  let d : ℕ → Fin N → MaximumData := fun j i => di i j
  have hvalid : ∀ᶠ j in atTop, ∀ i, StrongValid n hn g η hη (z j) (v j) j i r (d j i) := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hdi i).1
  let pick : ℕ → Fin N → Bool × Maxwell.Space := fun j i =>
    if h : ∃ b x, x ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b ∧
        (∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
          weighted n η (d j i) b' y ≤ weighted n η (d j i) b x) ∧
        (amplitude (vector (d j i)))^2 ≤ weighted n η (d j i) b x
    then (Classical.choose h,Classical.choose (Classical.choose_spec h)) else (false,0)
  let b := fun j i => (pick j i).1
  let x := fun j i => (pick j i).2
  have hpick : ∀ᶠ j in atTop, ∀ i,
      x j i ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) (b j i) ∧
      (∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
        weighted n η (d j i) b' y ≤ weighted n η (d j i) (b j i) (x j i)) ∧
      (amplitude (vector (d j i)))^2 ≤ weighted n η (d j i) (b j i) (x j i) := by
    filter_upwards [hvalid] with j hj i
    have h := weighted_attains n hn g η hη (z j) (v j) j i r hr (d j i) (hj i).1
    simp only [b,x,pick,dif_pos h]
    exact Classical.choose_spec (Classical.choose_spec h)
  have hplaced (i : Fin N) := variable_placement_volume (fun j => d j i) s hs s₀ hs₀ hst 0
    (fun j => rounded n hn g η hη j)
    (fun j y => (Packet06BoundedModalMaterial.rounded_bounds n hn g η hη K hK hceil j y).1) (hdi i).2
  have hphase (i : Fin N) (j : ℕ) : 1 ≤ phasePermittivity n η (d j i).side := by
    have hn2 : 1 ≤ n^2 := by nlinarith
    cases h : (d j i).side <;> simp only [phasePermittivity,h,Bool.false_eq_true,if_false,if_true] <;>
      nlinarith [mul_nonneg hη (sq_nonneg n)]
  have hdir (i : Fin N) := (physical_and_directional_volumes
    (fun j => placedVector (d j i) (s j) (hs j) 0)
    (fun j => phasePermittivity n η (d j i).side) (hplaced i).1 (hphase i)).2
  refine ⟨d,b,x,?_,fun i => (hplaced i).1,?_,hdir⟩
  · filter_upwards [hvalid,hpick] with j hj hk i
    exact ⟨hj i,(hk i).1,(hk i).2.1⟩
  · intro i
    have hdiv : Tendsto (fun j => scale (s j)^2 * weighted n η (d j i) (b j i) (x j i)) atTop atTop := by
      apply Filter.tendsto_atTop_mono' atTop _ (hplaced i).1
      filter_upwards [hpick,(hplaced i).1.eventually_ge_atTop 1] with j hj hjone
      have hsq := mul_le_mul_of_nonneg_left (hj i).2.2 (sq_nonneg (scale (s j)))
      have hident := amplitude_placedVector (d j i) (s j) (hs j) 0
      rw [hident] at hjone
      have hnon : 0 ≤ scale (s j)*amplitude (vector (d j i)) := mul_nonneg (scale_pos _ (hs j)).le (Real.sqrt_nonneg _)
      nlinarith
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hdiv
end OQ14.Packet06AllStrongWeightedVolumes
#print axioms OQ14.Packet06AllStrongWeightedVolumes.all_strong_weighted_volumes
