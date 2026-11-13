import Packet07DrivenRigidFields
import Packet07DrivenAngularTranslationSmooth

/-! The rigid placement acts on the same smooth transverse incident wave. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenRigidAngular
open Maxwell SphereHarmonicBasis Packet07DrivenFrameAngular Packet07AngularTranslation
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def amplitude (θ φ k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector)) : C(Sphere,Vector) :=
  translatedAmplitude k a (Packet07DrivenFrameAngular.amplitude θ φ A)

theorem amplitude_norm (θ φ k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (amplitude θ φ k a A)‖ = ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  rw [amplitude,translated_norm,Packet07DrivenFrameAngular.amplitude_norm]

theorem amplitude_tangent (θ φ k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector))
    (h : ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (A n)=0) :
    ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (amplitude θ φ k a A n)=0 :=
  translated_tangent k a _ (Packet07DrivenFrameAngular.amplitude_tangent θ φ A h)

theorem electric (θ φ k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector)) :
    AngularHerglotz.electric k (fun n j => amplitude θ φ k a A n j) =
      Packet07DrivenRigidHotspot.field θ φ a (AngularHerglotz.electric k (fun n j => A n j)) := by
  funext x i
  rw [amplitude,translated_electric,Packet07DrivenFrameAngular.electric_covariant]
  rfl

theorem magnetic (θ φ k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector)) :
    AngularHerglotz.magnetic k (fun n j => amplitude θ φ k a A n j) =
      Packet07DrivenRigidHotspot.field θ φ a (AngularHerglotz.magnetic k (fun n j => A n j)) := by
  funext x i
  rw [amplitude,translated_magnetic,Packet07DrivenFrameAngular.magnetic_covariant]
  rfl
end OQ14.Packet07DrivenRigidAngular
#print axioms OQ14.Packet07DrivenRigidAngular.amplitude_norm
#print axioms OQ14.Packet07DrivenRigidAngular.amplitude_tangent
#print axioms OQ14.Packet07DrivenRigidAngular.electric
#print axioms OQ14.Packet07DrivenRigidAngular.magnetic
