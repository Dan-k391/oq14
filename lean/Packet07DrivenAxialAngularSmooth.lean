import Packet07DrivenAxialTangency

/-! Smooth ambient angular extensions stay smooth under axial rotation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenAxialAngularSmooth
open Maxwell ModalAxialRotation Packet07DrivenAxialAngularVector Packet07DrivenAxialAngular SphereAngularSymmetry
abbrev Space := Maxwell.Space
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def extension (θ : ℝ) (F : Fin 3 → Space → ℂ) (i : Fin 3) (x : Space) : ℂ :=
  ModalAxialRotation.vector θ (fun j => F j (rotation (-θ) x)) i

theorem extension_smooth (θ : ℝ) (F : Fin 3 → Space → ℂ)
    (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (extension θ F i) := by
  have h (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (fun x => F j (rotation (-θ) x)) :=
    (hF j).comp (rotation (-θ)).toContinuousLinearEquiv.contDiff
  fin_cases i
  · exact (contDiff_const.mul (h 0)).sub (contDiff_const.mul (h 1))
  · exact (contDiff_const.mul (h 0)).add (contDiff_const.mul (h 1))
  · exact h 2

theorem extension_on_sphere (θ : ℝ) (F : Fin 3 → Space → ℂ) (A : C(Sphere,Vector))
    (hF : ∀ (n : Sphere) i, F i n=A n i) (n : Sphere) (i : Fin 3) :
    extension θ F i n = rotated θ A n i := by
  have h0 := hF (sphereMap (rotation (-θ)) n) 0
  have h1 := hF (sphereMap (rotation (-θ)) n) 1
  have h2 := hF (sphereMap (rotation (-θ)) n) 2
  change F 0 (rotation (-θ) n)=_ at h0
  change F 1 (rotation (-θ) n)=_ at h1
  change F 2 (rotation (-θ) n)=_ at h2
  fin_cases i <;> simp [extension,rotated,pull,rotate,vector,h0,h1,h2]
end OQ14.Packet07DrivenAxialAngularSmooth
#print axioms OQ14.Packet07DrivenAxialAngularSmooth.extension_smooth
#print axioms OQ14.Packet07DrivenAxialAngularSmooth.extension_on_sphere
