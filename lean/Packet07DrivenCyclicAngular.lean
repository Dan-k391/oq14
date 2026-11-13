import Packet07DrivenCyclicAngularVector
import SphereAngularSymmetry
import Packet07AngularTranslation

/-! Rotated physical angular densities retain their exact incoming L² power. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenCyclicAngular
open MeasureTheory Maxwell SphereHarmonicBasis SphereAngularSymmetry Packet06CyclicRotation Packet07DrivenCyclicAngularVector
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def pull (A : C(Sphere,Vector)) : C(Sphere,Vector) where
  toFun n := A (sphereMap rotation.symm n)
  continuous_toFun := A.continuous.comp (sphereMap rotation.symm).continuous

def rotated (A : C(Sphere,Vector)) : C(Sphere,Vector) where
  toFun n := rotate (pull A n)
  continuous_toFun := rotate_continuous.comp (pull A).continuous

theorem pull_norm (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (pull A)‖ = ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  let L : Lp Vector 2 angularMeasure →ₗᵢ[ℂ] Lp Vector 2 angularMeasure := Lp.compMeasurePreservingₗᵢ ℂ (sphereMap rotation.symm) (measurePreserving_sphereMap rotation.symm)
  have he : ContinuousMap.toLp 2 angularMeasure ℂ (pull A) = L (ContinuousMap.toLp 2 angularMeasure ℂ A) := by
    apply Lp.ext
    filter_upwards [(pull A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      Lp.coeFn_compMeasurePreserving (ContinuousMap.toLp 2 angularMeasure ℂ A) (measurePreserving_sphereMap rotation.symm),
      (measurePreserving_sphereMap rotation.symm).quasiMeasurePreserving.ae
        (A.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure)] with n h1 h2 h3
    change (L (ContinuousMap.toLp 2 angularMeasure ℂ A) : Sphere → Vector) n = _ at h2
    rw [h1,h2]
    change A (sphereMap rotation.symm n) = (ContinuousMap.toLp 2 angularMeasure ℂ A : Sphere → Vector) (sphereMap rotation.symm n)
    exact h3.symm
  rw [he,L.norm_map]

theorem rotated_norm (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (rotated A)‖ = ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  rw [←pull_norm A]
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(rotated A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      (pull A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n h1 h2
    rw [h1,h2]
    exact (Packet07DrivenCyclicAngularVector.rotate_norm _).le
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(rotated A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      (pull A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n h1 h2
    rw [h1,h2]
    exact (Packet07DrivenCyclicAngularVector.rotate_norm _).ge
end OQ14.Packet07DrivenCyclicAngular
#print axioms OQ14.Packet07DrivenCyclicAngular.pull_norm
#print axioms OQ14.Packet07DrivenCyclicAngular.rotated_norm
