import Packet07DrivenAffineLocal

/-! Genuine Maxwell data remain locally integrable under affine scaling. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenAffineGood
open MeasureTheory Maxwell Packet07DrivenFrameMaxwell Packet07DrivenAffineLocal
abbrev Space := Maxwell.Space

theorem affine_good (s : ℝ) (hs : 0 < s) (a : Space) (k : ℝ) (ε : Space → ℝ) (E H : Field)
    (h : Good (k : ℂ) ε E H) :
    Good ((s*k : ℝ) : ℂ) (fun x => ε (Packet07AffineGeometry.map s a x))
      (Packet07AffineMaxwell.affineField s a E) (Packet07AffineMaxwell.affineField s a H) := by
  have hm : MaterialMaxwell.TestMaxwell k ε E H := h.maxwell
  have hscaled := Packet07AffineMaxwell.testMaxwell_scale_any s k hs ε E H hm
  have hmul := FrequencyScalingMaxwell.testMaxwell_smul (s*k) (fun x => ε (s • x))
    (PuncturedMaxwellScaling.fieldAtFrequency s E) (PuncturedMaxwellScaling.fieldAtFrequency s H) (s : ℂ) hscaled
  have hM := Packet07MaxwellTranslation.testMaxwell_translate (s*k) (fun x => ε (s • x)) _ _ hmul a
  refine ⟨?_,?_,?_,hM⟩
  · intro i
    simpa only [Packet07AffineMaxwell.affineField,FrequencyScalingMaxwell.scaleField_apply,
      Packet07AffineGeometry.map,smul_eq_mul] using (affine_local s hs a (fun x => E x i) (h.electric_local i)).smul (s : ℂ)
  · intro i
    simpa only [Packet07AffineMaxwell.affineField,FrequencyScalingMaxwell.scaleField_apply,
      Packet07AffineGeometry.map,smul_eq_mul] using (affine_local s hs a (fun x => H x i) (h.magnetic_local i)).smul (s : ℂ)
  · intro i
    have hh := (affine_local s hs a (fun x => (ε x : ℂ)*E x i) (h.dielectric_local i)).smul (s : ℂ)
    convert hh using 1
    funext x
    simp only [Packet07AffineMaxwell.affineField,FrequencyScalingMaxwell.scaleField_apply,
      Packet07AffineGeometry.map,Pi.smul_apply,smul_eq_mul]
    ring
end OQ14.Packet07DrivenAffineGood
#print axioms OQ14.Packet07DrivenAffineGood.affine_good
