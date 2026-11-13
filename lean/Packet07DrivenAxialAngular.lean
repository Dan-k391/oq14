import Packet07DrivenAxialAngularVector
import SphereAngularSymmetry
import Packet07AngularTranslation

/-! Rotated physical angular densities retain their exact incoming L² power. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenAxialAngular
open MeasureTheory Maxwell SphereHarmonicBasis SphereAngularSymmetry ModalAxialRotation Packet07DrivenAxialAngularVector
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def pull (θ : ℝ) (A : C(Sphere,Vector)) : C(Sphere,Vector) where
  toFun n := A (sphereMap (rotation (-θ)) n)
  continuous_toFun := A.continuous.comp (sphereMap (rotation (-θ))).continuous

def rotated (θ : ℝ) (A : C(Sphere,Vector)) : C(Sphere,Vector) where
  toFun n := rotate θ (pull θ A n)
  continuous_toFun := (rotate_continuous θ).comp (pull θ A).continuous

theorem pull_norm (θ : ℝ) (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (pull θ A)‖ = ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  let L : Lp Vector 2 angularMeasure →ₗᵢ[ℂ] Lp Vector 2 angularMeasure := Lp.compMeasurePreservingₗᵢ ℂ (sphereMap (rotation (-θ))) (measurePreserving_sphereMap (rotation (-θ)))
  have he : ContinuousMap.toLp 2 angularMeasure ℂ (pull θ A) = L (ContinuousMap.toLp 2 angularMeasure ℂ A) := by
    apply Lp.ext
    filter_upwards [(pull θ A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 angularMeasure ℂ A) (measurePreserving_sphereMap (rotation (-θ))),
      (measurePreserving_sphereMap (rotation (-θ))).quasiMeasurePreserving.ae
        (A.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure)] with n h1 h2 h3
    change (L (ContinuousMap.toLp 2 angularMeasure ℂ A) : Sphere → Vector) n = _ at h2
    rw [h1,h2]
    change A (sphereMap (rotation (-θ)) n) = (ContinuousMap.toLp 2 angularMeasure ℂ A : Sphere → Vector) (sphereMap (rotation (-θ)) n)
    exact h3.symm
  rw [he,L.norm_map]

theorem rotated_norm (θ : ℝ) (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (rotated θ A)‖ = ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  rw [←pull_norm θ A]
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(rotated θ A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      (pull θ A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n h1 h2
    rw [h1,h2]
    exact (rotate_norm θ _).le
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(rotated θ A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      (pull θ A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n h1 h2
    rw [h1,h2]
    exact (rotate_norm θ _).ge
end OQ14.Packet07DrivenAxialAngular
#print axioms OQ14.Packet07DrivenAxialAngular.pull_norm
#print axioms OQ14.Packet07DrivenAxialAngular.rotated_norm
