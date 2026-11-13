import Packet07AffineGeometry
import Packet06PlacedHotspotGeometry
import Packet07DrivenUniformSelectedHotspots

/-! Affine similarity and phase geometry for driven hotspot placement. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformAffineGeometry
open Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum Packet07HotspotComponent
abbrev Space := Maxwell.Space

def placement (s : ℝ) (hs : 0 < s) (a : Space) : Space ≃ₜ Space where
  toFun := Packet07AffineGeometry.place s a
  invFun := Packet07AffineGeometry.map s a
  left_inv := Packet07AffineGeometry.map_place s hs.ne' a
  right_inv := by intro x; simp [Packet07AffineGeometry.map,Packet07AffineGeometry.place,smul_sub,smul_smul,hs.ne']
  continuous_toFun := (continuous_id.const_smul s⁻¹).add continuous_const
  continuous_invFun := Packet07AffineGeometry.map_continuous s a

theorem image_phase (s : ℝ) (hs : 0 < s) (a : Space) (body : Set Space) (b : Bool) :
    placement s hs a '' phaseDomain body b = phaseDomain (placement s hs a '' body) b := by
  cases b <;> simp only [phaseDomain, (placement s hs a).image_closure, (placement s hs a).image_compl]

theorem image_ball (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ) :
    placement s hs a '' ball c r = ball (placement s hs a c) (r/s) := by
  rw [(placement s hs a).image_eq_preimage]
  exact Packet07AffineGeometry.preimage_ball s hs a c r

theorem image_closedBall (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ) :
    placement s hs a '' closedBall c r = closedBall (placement s hs a c) (r/s) := by
  ext y
  rw [(placement s hs a).image_eq_preimage]
  simp only [mem_preimage,mem_closedBall,dist_eq_norm]
  have hd : s • (y-a)-c = s • (y-(s⁻¹ • c+a)) := by
    simp [smul_sub,smul_add,smul_smul,hs.ne']; module
  change ‖s • (y-a)-c‖ ≤ r ↔ ‖y-(s⁻¹ • c+a)‖ ≤ r/s
  rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos hs]
  simpa only [mul_comm] using (le_div_iff₀ hs).symm

theorem image_phase_ball (s : ℝ) (hs : 0 < s) (a c : Space) (r : ℝ) (body : Set Space) (b : Bool) :
    placement s hs a '' (closedBall c r ∩ phaseDomain body b) =
      closedBall (placement s hs a c) (r/s) ∩ phaseDomain (placement s hs a '' body) b := by
  rw [Set.image_inter (placement s hs a).injective,image_closedBall,image_phase]
end OQ14.Packet07DrivenUniformAffineGeometry
#print axioms OQ14.Packet07DrivenUniformAffineGeometry.image_phase
#print axioms OQ14.Packet07DrivenUniformAffineGeometry.image_ball
#print axioms OQ14.Packet07DrivenUniformAffineGeometry.image_closedBall
#print axioms OQ14.Packet07DrivenUniformAffineGeometry.image_phase_ball
