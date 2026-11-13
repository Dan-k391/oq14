import Packet07DrivenCyclicTangency

/-! Cyclic rotation preserves smooth angular extensions. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenCyclicAngularSmooth
open Maxwell Packet06CyclicRotation Packet07DrivenCyclicAngularVector Packet07DrivenCyclicAngular SphereAngularSymmetry
abbrev Space := Maxwell.Space
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def extension (F : Fin 3 → Space → ℂ) (i : Fin 3) (x : Space) : ℂ := F (WeakCurl.previous i) (unrotate x)

theorem extension_smooth (F : Fin 3 → Space → ℂ) (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (extension F i) :=
  (hF _).comp rotation.symm.toContinuousLinearEquiv.contDiff

theorem extension_on_sphere (F : Fin 3 → Space → ℂ) (A : C(Sphere,Vector))
    (hF : ∀ (n : Sphere) i, F i n=A n i) (n : Sphere) (i : Fin 3) :
    extension F i n = rotated A n i := by
  exact hF (sphereMap rotation.symm n) (WeakCurl.previous i)
end OQ14.Packet07DrivenCyclicAngularSmooth
#print axioms OQ14.Packet07DrivenCyclicAngularSmooth.extension_smooth
#print axioms OQ14.Packet07DrivenCyclicAngularSmooth.extension_on_sphere
