import Packet07DrivenFrameAffine
import Packet07DrivenUniformAffineGeometry

/-! Local integrability is preserved by positive dilation and translation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenAffineLocal
open MeasureTheory Set Maxwell Packet07DrivenUniformAffineGeometry
abbrev Space := Maxwell.Space

theorem affine_map_measure (s : ℝ) (hs : 0 < s) (a : Space) :
    Measure.map (Packet07AffineGeometry.map s a) volume = ENNReal.ofReal (|(s^3)⁻¹|) • volume := by
  have htrans : Measure.map (fun x : Space => x-a) volume = volume :=
    (measurePreserving_add_right (volume : Measure Space) (-a)).map_eq
  have hmap : Packet07AffineGeometry.map s a = (fun x : Space => s • x) ∘ (fun x : Space => x-a) := rfl
  rw [hmap,← Measure.map_map (show Measurable (fun x : Space => s • x) from measurable_const_smul s) (show Measurable (fun x : Space => x-a) from measurable_id.sub measurable_const),htrans]
  have h := Measure.map_addHaar_smul (volume : Measure Space) hs.ne'
  rwa [DilationL2.finrank_space] at h

theorem affine_local (s : ℝ) (hs : 0 < s) (a : Space) (f : Space → ℂ) (hf : LocallyIntegrable f) :
    LocallyIntegrable (fun x => f (Packet07AffineGeometry.map s a x)) := by
  let e := (placement s hs a).symm
  have hmap : Measure.map e volume = ENNReal.ofReal (|(s^3)⁻¹|) • volume := affine_map_measure s hs a
  have hscaled : LocallyIntegrable f (ENNReal.ofReal (|(s^3)⁻¹|) • volume) := by
    intro x
    obtain ⟨U,hU,hint⟩ := hf x
    refine ⟨U,hU,?_⟩
    change Integrable f ((ENNReal.ofReal (|(s^3)⁻¹|) • volume).restrict U)
    rw [Measure.restrict_smul]
    exact hint.smul_measure ENNReal.ofReal_ne_top
  exact (locallyIntegrable_map_homeomorph e).mp (by rw [hmap]; exact hscaled)
end OQ14.Packet07DrivenAffineLocal
#print axioms OQ14.Packet07DrivenAffineLocal.affine_map_measure
#print axioms OQ14.Packet07DrivenAffineLocal.affine_local
