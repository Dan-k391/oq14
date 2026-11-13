import Packet07DrivenCyclicHerglotz
import Packet07DrivenFrameMaxwell

/-! The exact normal-reaching frame transports the complete Herglotz illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4500000
namespace OQ14.Packet07DrivenFrameAngular
open MeasureTheory Maxwell SphereHarmonicBasis Packet07DrivenFrameMaxwell
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def amplitude (θ φ : ℝ) (A : C(Sphere,Vector)) : C(Sphere,Vector) :=
  Packet07DrivenAxialAngular.rotated θ (Packet07DrivenCyclicAngular.rotated (Packet07DrivenCyclicAngular.rotated
    (Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A))))

theorem amplitude_norm (θ φ : ℝ) (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (amplitude θ φ A)‖ = ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  simp only [amplitude,Packet07DrivenAxialAngular.rotated_norm,Packet07DrivenCyclicAngular.rotated_norm]

theorem amplitude_tangent (θ φ : ℝ) (A : C(Sphere,Vector))
    (hA : ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (A n)=0) :
    ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (amplitude θ φ A n)=0 := by
  exact Packet07DrivenAxialTangency.rotated_tangent θ _ (Packet07DrivenCyclicTangency.rotated_tangent _
    (Packet07DrivenCyclicTangency.rotated_tangent _ (Packet07DrivenAxialTangency.rotated_tangent φ _
      (Packet07DrivenCyclicTangency.rotated_tangent A hA))))

theorem electric_covariant (θ φ k : ℝ) (A : C(Sphere,Vector)) :
    AngularHerglotz.electric k (fun n j => amplitude θ φ A n j) =
      frameField θ φ (AngularHerglotz.electric k (fun n j => A n j)) := by
  funext x i
  unfold amplitude frameField
  rw [Packet07DrivenAxialHerglotz.electric_covariant]
  change Packet07DrivenAxialPair.rotateField θ (AngularHerglotz.electric k
    (fun n j => Packet07DrivenCyclicAngular.rotated (Packet07DrivenCyclicAngular.rotated
      (Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A))) n j)) x i = _
  have h1 : AngularHerglotz.electric k (fun n j => Packet07DrivenCyclicAngular.rotated (Packet07DrivenCyclicAngular.rotated
      (Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A))) n j) =
    Packet06CyclicRotationMaxwell.rotateField (Packet06CyclicRotationMaxwell.rotateField
      (AngularHerglotz.electric k (fun n j => Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A) n j))) := by
    funext y l
    rw [Packet07DrivenCyclicHerglotz.electric_covariant]
    simp only [Packet06CyclicRotationMaxwell.rotateField,Packet07DrivenCyclicHerglotz.electric_covariant]
  rw [h1,Packet07DrivenInverseCyclic.twice_field]
  have h2 : AngularHerglotz.electric k (fun n j => Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A) n j) =
    Packet07DrivenAxialPair.rotateField φ (Packet06CyclicRotationMaxwell.rotateField (AngularHerglotz.electric k (fun n j => A n j))) := by
    funext y l
    rw [Packet07DrivenAxialHerglotz.electric_covariant]
    have he : AngularHerglotz.electric k (fun n j => Packet07DrivenCyclicAngular.rotated A n j) =
        Packet06CyclicRotationMaxwell.rotateField (AngularHerglotz.electric k (fun n j => A n j)) := by
      funext p q
      exact Packet07DrivenCyclicHerglotz.electric_covariant k A p q
    rw [he]
    rfl
  rw [h2]

theorem magnetic_covariant (θ φ k : ℝ) (A : C(Sphere,Vector)) :
    AngularHerglotz.magnetic k (fun n j => amplitude θ φ A n j) =
      frameField θ φ (AngularHerglotz.magnetic k (fun n j => A n j)) := by
  funext x i
  unfold amplitude frameField
  rw [Packet07DrivenAxialHerglotzMagnetic.magnetic_covariant]
  change Packet07DrivenAxialPair.rotateField θ (AngularHerglotz.magnetic k
    (fun n j => Packet07DrivenCyclicAngular.rotated (Packet07DrivenCyclicAngular.rotated
      (Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A))) n j)) x i = _
  have h1 : AngularHerglotz.magnetic k (fun n j => Packet07DrivenCyclicAngular.rotated (Packet07DrivenCyclicAngular.rotated
      (Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A))) n j) =
    Packet06CyclicRotationMaxwell.rotateField (Packet06CyclicRotationMaxwell.rotateField
      (AngularHerglotz.magnetic k (fun n j => Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A) n j))) := by
    funext y l
    rw [Packet07DrivenCyclicHerglotz.magnetic_covariant]
    simp only [Packet06CyclicRotationMaxwell.rotateField,Packet07DrivenCyclicHerglotz.magnetic_covariant]
  rw [h1,Packet07DrivenInverseCyclic.twice_field]
  have h2 : AngularHerglotz.magnetic k (fun n j => Packet07DrivenAxialAngular.rotated φ (Packet07DrivenCyclicAngular.rotated A) n j) =
    Packet07DrivenAxialPair.rotateField φ (Packet06CyclicRotationMaxwell.rotateField (AngularHerglotz.magnetic k (fun n j => A n j))) := by
    funext y l
    rw [Packet07DrivenAxialHerglotzMagnetic.magnetic_covariant]
    have he : AngularHerglotz.magnetic k (fun n j => Packet07DrivenCyclicAngular.rotated A n j) =
        Packet06CyclicRotationMaxwell.rotateField (AngularHerglotz.magnetic k (fun n j => A n j)) := by
      funext p q
      exact Packet07DrivenCyclicHerglotz.magnetic_covariant k A p q
    rw [he]
    rfl
  rw [h2]
end OQ14.Packet07DrivenFrameAngular
#print axioms OQ14.Packet07DrivenFrameAngular.amplitude_norm
#print axioms OQ14.Packet07DrivenFrameAngular.amplitude_tangent
#print axioms OQ14.Packet07DrivenFrameAngular.electric_covariant
#print axioms OQ14.Packet07DrivenFrameAngular.magnetic_covariant
