import Packet07HotspotComponent
import Packet05HighMaximum

/-! Actual a.e. field peaks and a low collar force a compact half-amplitude hotspot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet07PeakAttainment
open MeasureTheory Set Metric Maxwell Packet07HotspotComponent

theorem positive_volume_exceeds_maximum {J : Type*}
    (K : Set Space) (hK : MeasurableSet K) (D : J → Set Space)
    (amp : J → Space → ℝ) (Eamp : Space → ℝ)
    (hae : ∀ᵐ y ∂volume.restrict K, ∃ j, y ∈ D j ∧ Eamp y=amp j y)
    (j : J) (x : Space)
    (hmax : ∀ k y, y ∈ K ∩ D k → amp k y ≤ amp j x)
    (M : ℝ) (hpeak : 0 < (volume.restrict K) {y | M < Eamp y}) : M < amp j x := by
  by_contra hn
  have hbound : ∀ᵐ y ∂volume.restrict K, Eamp y ≤ M := by
    filter_upwards [hae,ae_restrict_mem hK] with y hy hyK
    obtain ⟨k,hk,he⟩ := hy
    rw [he]
    exact (hmax k y ⟨hyK,hk⟩).trans (not_lt.mp hn)
  rw [ae_iff] at hbound
  have hz : (volume.restrict K) {y | M < Eamp y}=0 := by simpa only [not_le] using hbound
  exact (ne_of_gt hpeak) hz

theorem half_peak_component {J : Type*} [Finite J]
    (D : J → Set Space) (amp : J → Space → ℝ)
    (hD : ∀ j, IsClosed (D j)) (c x : Space) (r B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ j, ContinuousOn (amp j) (closedBall c r ∩ D j))
    (j : J) (hx : x ∈ closedBall c r ∩ D j) (hhigh : 2*B < amp j x)
    (hcollar : ∀ k y, y ∈ D k → dist y c=r → amp k y ≤ B) :
    let S := branchSuperlevel D amp (amp j x/2)
    x ∈ ball c r ∧ x ∈ connectedComponentIn S x ∧
      IsConnected (connectedComponentIn S x) ∧
      IsCompact (connectedComponentIn S x) ∧ connectedComponentIn S x ⊆ ball c r := by
  let S := branchSuperlevel D amp (amp j x/2)
  have hpos : 0 < amp j x := lt_of_le_of_lt (by positivity) hhigh
  have hlevel : amp j x/2 ≤ amp j x := by linarith
  have hxS : x ∈ S := mem_iUnion.mpr ⟨j,hx.2,hlevel⟩
  have hxr : x ∈ ball c r := by
    have hle : dist x c ≤ r := hx.1
    by_contra hn
    have he : dist x c=r := le_antisymm hle (not_lt.mp hn)
    have hb := hcollar j x hx.2 he
    linarith
  have hbarrier : ∀ y ∈ S, dist y c ≠ r := by
    intro y hy he
    obtain ⟨k,hk,hklevel⟩ := mem_iUnion.mp hy
    change amp j x/2 ≤ amp k y at hklevel
    have hb := hcollar k y hk he
    linarith
  have hclosed : IsClosed (S ∩ closedBall c r) := by
    have he : S ∩ closedBall c r =
        branchSuperlevel (fun k => closedBall c r ∩ D k) amp (amp j x/2) := by
      ext y
      simp only [S,branchSuperlevel,mem_inter_iff,mem_iUnion,mem_setOf_eq]
      constructor
      · rintro ⟨⟨k,hk,hl⟩,hy⟩
        exact ⟨k,⟨hy,hk⟩,hl⟩
      · rintro ⟨k,⟨hy,hk⟩,hl⟩
        exact ⟨⟨k,hk,hl⟩,hy⟩
    rw [he]
    exact branch_superlevel_closed _ amp _ (fun k => isClosed_closedBall.inter (hD k)) hcont
  obtain ⟨hcompact,hinside⟩ := locally_closed_component_inside S c x r hclosed hxS hxr hbarrier
  exact ⟨hxr,mem_connectedComponentIn hxS,
    ⟨⟨x,mem_connectedComponentIn hxS⟩,isPreconnected_connectedComponentIn⟩,hcompact,hinside⟩

end OQ14.Packet07PeakAttainment
#print axioms OQ14.Packet07PeakAttainment.positive_volume_exceeds_maximum
#print axioms OQ14.Packet07PeakAttainment.half_peak_component
