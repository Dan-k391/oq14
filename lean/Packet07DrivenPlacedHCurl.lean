import Packet07DrivenLocalL2Transport
import Packet07DrivenRigidFields
import Packet07SelectedRadiation
import MaterialHCurl

/-! Literal driven fields are locally square-integrable before and after placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet07DrivenPlacedHCurl
open MeasureTheory Set Metric Maxwell Packet07DrivenLocalL2Transport Packet07DrivenFrameMaxwell
  Packet07DrivenRigidHotspot ModalAxialRotation Packet07DrivenAxialPair
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

def FieldLocalL2 (F : Field) : Prop := ∀ i, LocalL2 (fun x => F x i)

theorem actual_fields {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k : ℝ) (input : Input) (j : ℕ) :
    FieldLocalL2 (g.electric k j input) ∧ FieldLocalL2 (g.magnetic k j input) := by
  let c := g.rounded j
  let I := FiniteAngularHerglotz.incident k input
  let u := Packet07SelectedRadiation.actualUnknown g k j input
  have hc := ConicalCommonBinaryPeaks.support g.dataFamily g.radii g.centers d g.contrast_pos.le
    g.contrast_bound g.radii_outer g.outer_sep g.radii_pos g.enclosing g.outer_enclosed j
  constructor
  · intro i T
    exact SmallVolumeMaxwell.total_electric_memLp_ball c k g.enclosing T u I.E hc
      (fun j => SmallVolumeMaxwell.continuous_memLp_ball _ (I.smoothE j).continuous T) i
  · intro i T
    exact SmallVolumeMaxwell.total_magnetic_memLp_ball c k g.enclosing T u I.H hc
      (fun j => SmallVolumeMaxwell.continuous_memLp_ball _ (I.smoothH j).continuous T) i

theorem axial_field (θ : ℝ) (F : Field) (hF : FieldLocalL2 F) : FieldLocalL2 (rotateField θ F) := by
  have h0 := isometry_comp (rotation (-θ)) (fun x => F x 0) (hF 0)
  have h1 := isometry_comp (rotation (-θ)) (fun x => F x 1) (hF 1)
  have h2 := isometry_comp (rotation (-θ)) (fun x => F x 2) (hF 2)
  intro i T
  fin_cases i
  · simpa only [rotateField,vector,Matrix.cons_val_zero,smul_eq_mul] using ((h0 T).const_mul (Real.cos θ : ℂ)).sub ((h1 T).const_mul (Real.sin θ : ℂ))
  · simpa only [rotateField,vector,Matrix.cons_val_one,smul_eq_mul] using ((h0 T).const_mul (Real.sin θ : ℂ)).add ((h1 T).const_mul (Real.cos θ : ℂ))
  · exact h2 T

theorem cyclic_field (F : Field) (hF : FieldLocalL2 F) :
    FieldLocalL2 (Packet06CyclicRotationMaxwell.rotateField F) := by
  intro i
  exact isometry_comp Packet06CyclicRotation.rotation.symm (fun x => F x (WeakCurl.previous i)) (hF _)

theorem frame_field (θ φ : ℝ) (F : Field) (hF : FieldLocalL2 F) : FieldLocalL2 (frameField θ φ F) := by
  have h1 := cyclic_field F hF
  have h2 := axial_field φ _ h1
  have h3 := cyclic_field _ h2
  have h4 := cyclic_field _ h3
  have h5 := axial_field θ _ h4
  simpa only [frameField,Packet07DrivenInverseCyclic.twice_field] using h5

theorem affine_field (s : ℝ) (hs : 0 < s) (a : Space) (F : Field) (hF : FieldLocalL2 F) :
    FieldLocalL2 (Packet07AffineMaxwell.affineField s a F) := by
  intro i T
  have hh := affine_comp s hs a (fun x => F x i) (hF i) T
  simpa only [Packet07AffineMaxwell.affineField,FrequencyScalingMaxwell.scaleField_apply,
    Packet07AffineGeometry.map,smul_eq_mul] using hh.const_mul (s : ℂ)

theorem rigid_field (θ φ : ℝ) (a : Space) (F : Field) (hF : FieldLocalL2 F) :
    FieldLocalL2 (field θ φ a F) := by
  intro i T
  have hh := affine_comp 1 (by norm_num) a (fun x => frameField θ φ F x i) (frame_field θ φ F hF i) T
  simpa [field,Packet07AffineGeometry.map] using hh

theorem placed_fields {N : ℕ} {P : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N P d t) (k s : ℝ) (hs : 0 < s) (input : Input)
    (j : ℕ) (θ φ : ℝ) (a b : Space) :
    FieldLocalL2 (field θ φ a (Packet07AffineMaxwell.affineField s b (g.electric k j input))) ∧
    FieldLocalL2 (field θ φ a (Packet07AffineMaxwell.affineField s b (g.magnetic k j input))) := by
  obtain ⟨hE,hH⟩ := actual_fields g k input j
  exact ⟨rigid_field θ φ a _ (affine_field s hs b _ hE),rigid_field θ φ a _ (affine_field s hs b _ hH)⟩
end OQ14.Packet07DrivenPlacedHCurl
#print axioms OQ14.Packet07DrivenPlacedHCurl.actual_fields
#print axioms OQ14.Packet07DrivenPlacedHCurl.axial_field
#print axioms OQ14.Packet07DrivenPlacedHCurl.cyclic_field
#print axioms OQ14.Packet07DrivenPlacedHCurl.frame_field
#print axioms OQ14.Packet07DrivenPlacedHCurl.affine_field
#print axioms OQ14.Packet07DrivenPlacedHCurl.rigid_field
#print axioms OQ14.Packet07DrivenPlacedHCurl.placed_fields
