import Packet06RoundedHotspot

/-! Choose collar constants before the common peak index, simultaneously
for a finite family of actual rounded mode hotspots. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06HotspotFamilyAssembly
open MeasureTheory Set Filter Metric Maxwell Packet05ActualMaximum
  Packet06ConcreteModalGeometry Packet06ConcreteModalRounding Packet06RoundedHotspot
open scoped Topology
abbrev Space := Maxwell.Space

theorem hotspots_of_uniform_collars {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
    (r : ℝ) (hr : 0 < r) (hrb : r < g.radius)
    (hmode : ∀ᶠ j in atTop, z j ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη j) (z j) 1 (v j)=0)
    (hcollar : ∀ i : Fin N, ∃ A : Set Space, ∃ B : ℝ,
      IsOpen A ∧ A ⊆ ball (g.center i) g.radius ∧ sphere (g.center i) r ⊆ A ∧ 0 ≤ B ∧
      ∀ᶠ j in atTop, ∀ᵐ x ∂volume.restrict A,
        physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x ≤ B)
    (hpeak : ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i : Fin N,
      0 < (volume.restrict (closedBall (g.center i) r)) {x | M <
        physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
          (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
          (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x}) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i : Fin N,
      HotspotAbove (rounded n hn g η hη j) (z j) (v j) (body g j) (g.center i) r M B := by
  classical
  choose A B hA hAV hAsphere hB hbound using hcollar
  let B₀ : ℝ := ∑ i : Fin N, B i
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg (fun i _ => hB i)
  have hle (i : Fin N) : B i ≤ B₀ :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ i)
  have hbounds : ∀ᶠ j in atTop, ∀ i : Fin N, ∀ᵐ x ∂volume.restrict (A i),
      physicalAmplitude (fun k y => Packet06ComplexElectric.electric (z j)
        (StaticCoefficient.sqrtMultiplier (rounded n hn g η hη j) (v j))
        (DynamicVolume.source (rounded n hn g η hη j) (v j)) y k) x ≤ B₀ := by
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [hbound i] with j hj
    filter_upwards [hj] with x hx
    exact hx.trans (hle i)
  refine ⟨B₀,hB₀,?_⟩
  intro M
  filter_upwards [hmode,hbounds,hpeak (max M (2*B₀)),
    eventually_actual_hotspot n hn g η hη] with j hj hbnd hpk hhot i
  exact hhot (z j) hj.1 (v j) hj.2 i r hr hrb (A i) (hA i) (hAV i)
    (hAsphere i) B₀ hB₀ M (hbnd i) (hpk i)

end OQ14.Packet06HotspotFamilyAssembly
#print axioms OQ14.Packet06HotspotFamilyAssembly.hotspots_of_uniform_collars
