import Packet07DrivenFrameAngular
import Packet07DrivenCyclicAngularSmooth
import Packet07DrivenAxialAngularSmooth

/-! The frame-rotated angular density has a genuine smooth ambient extension. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenFrameAngularSmooth
open Maxwell Packet07DrivenFrameAngular
abbrev Space := Maxwell.Space
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def extension (θ φ : ℝ) (F : Fin 3 → Space → ℂ) : Fin 3 → Space → ℂ :=
  Packet07DrivenAxialAngularSmooth.extension θ
    (Packet07DrivenCyclicAngularSmooth.extension (Packet07DrivenCyclicAngularSmooth.extension
      (Packet07DrivenAxialAngularSmooth.extension φ (Packet07DrivenCyclicAngularSmooth.extension F))))

theorem extension_smooth (θ φ : ℝ) (F : Fin 3 → Space → ℂ) (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) :
    ∀ i, ContDiff ℝ (⊤ : ℕ∞) (extension θ φ F i) := by
  exact Packet07DrivenAxialAngularSmooth.extension_smooth θ _
    (Packet07DrivenCyclicAngularSmooth.extension_smooth _ (Packet07DrivenCyclicAngularSmooth.extension_smooth _
      (Packet07DrivenAxialAngularSmooth.extension_smooth φ _ (Packet07DrivenCyclicAngularSmooth.extension_smooth F hF))))

theorem extension_on_sphere (θ φ : ℝ) (F : Fin 3 → Space → ℂ) (A : C(Sphere,Vector))
    (hF : ∀ (n : Sphere) i, F i n=A n i) :
    ∀ (n : Sphere) i, extension θ φ F i n=amplitude θ φ A n i := by
  apply Packet07DrivenAxialAngularSmooth.extension_on_sphere θ _ _
  apply Packet07DrivenCyclicAngularSmooth.extension_on_sphere _ _
  apply Packet07DrivenCyclicAngularSmooth.extension_on_sphere _ _
  apply Packet07DrivenAxialAngularSmooth.extension_on_sphere φ _ _
  exact Packet07DrivenCyclicAngularSmooth.extension_on_sphere F A hF
end OQ14.Packet07DrivenFrameAngularSmooth
#print axioms OQ14.Packet07DrivenFrameAngularSmooth.extension_smooth
#print axioms OQ14.Packet07DrivenFrameAngularSmooth.extension_on_sphere
