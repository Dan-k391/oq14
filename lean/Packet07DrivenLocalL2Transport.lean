import Packet07DrivenAffineLocal
import SmallVolumeMaxwell

/-! Local L² persists under homeomorphisms with finite constant volume scaling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07DrivenLocalL2Transport
open MeasureTheory Set Metric Maxwell
abbrev Space := Maxwell.Space

def LocalL2 (f : Space → ℂ) : Prop :=
  ∀ R : ℝ, MemLp f 2 (volume.restrict (closedBall 0 R))

theorem comp_scaled (e : Space ≃ₜ Space) (c : ENNReal) (hc : c ≠ ⊤)
    (he : Measure.map e volume = c • volume) (f : Space → ℂ) (hf : LocalL2 f) :
    LocalL2 (fun x => f (e x)) := by
  intro T
  have hcompact := (isCompact_closedBall (0 : Space) T).image e.continuous
  obtain ⟨R,hR⟩ := hcompact.isBounded.subset_closedBall (0 : Space)
  have hg : MemLp ((closedBall (0 : Space) R).indicator f) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall).2 (hf R)
  have hm : MemLp ((closedBall (0 : Space) R).indicator f) 2 (Measure.map e volume) := by
    rw [he]
    exact hg.smul_measure hc
  have hcomp : MemLp (((closedBall (0 : Space) R).indicator f) ∘ e) 2 volume :=
    hm.comp_of_map e.continuous.measurable.aemeasurable
  apply (hcomp.mono_measure Measure.restrict_le_self).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  have heR : e x ∈ closedBall (0 : Space) R := hR ⟨x,hx,rfl⟩
  simp [heR]

theorem isometry_comp (L : Space ≃ₗᵢ[ℝ] Space) (f : Space → ℂ) (hf : LocalL2 f) :
    LocalL2 (fun x => f (L x)) := by
  apply comp_scaled L.toHomeomorph 1 (by simp) ?_ f hf
  simpa using L.measurePreserving.map_eq

theorem affine_comp (s : ℝ) (hs : 0 < s) (a : Space) (f : Space → ℂ) (hf : LocalL2 f) :
    LocalL2 (fun x => f (Packet07AffineGeometry.map s a x)) := by
  apply comp_scaled (Packet07DrivenUniformAffineGeometry.placement s hs a).symm
    (ENNReal.ofReal (|(s^3)⁻¹|)) ENNReal.ofReal_ne_top ?_ f hf
  exact Packet07DrivenAffineLocal.affine_map_measure s hs a
end OQ14.Packet07DrivenLocalL2Transport
#print axioms OQ14.Packet07DrivenLocalL2Transport.comp_scaled
#print axioms OQ14.Packet07DrivenLocalL2Transport.isometry_comp
#print axioms OQ14.Packet07DrivenLocalL2Transport.affine_comp
