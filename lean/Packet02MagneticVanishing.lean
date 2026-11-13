import Packet02GoodRotation
import Packet02MagneticRotation
import Packet02VanishingAlgebra

/-! Radial vanishing of the actual magnetic convolution on a single conull,
frequency-independent, rotation-invariant domain of absolute convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02MagneticVanishing
open MeasureTheory Metric OQ14.Maxwell OQ14.ModalWeightedMode
open OQ14.ModalAxialRotation OQ14.ModalMeridionalReflection
open OQ14.Packet02GoodSet OQ14.WeakDebyeScalar

theorem magnetic_rotation (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) (z : ℂ) (θ : ℝ) (x : Space) (hx : good n hn u x) :
    ComplexSphereMaxwell.magnetic n hn z u (rotation θ x) =
      vector θ (ComplexSphereMaxwell.magnetic n hn z u x) := by
  funext i
  exact (Packet02MagneticRotation.magnetic_covariant n hn u hu.1 z θ x i
    (fun j l => good_gradient_integrable n hn u x hx z j l)).trans (matrix_vector θ _ i)

theorem radial_zero_good (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) (z : ℂ) (x : Space) (hx : good n hn u x) :
    radialDot (fun j y => ComplexSphereMaxwell.magnetic n hn z u y j) x = 0 := by
  apply Packet02VanishingAlgebra.radial_zero (good n hn u)
    (ComplexSphereMaxwell.magnetic n hn z u) _ _ _ x hx
  · intro θ y hy
    exact (Packet02GoodRotation.good_rotation n hn u hu.1 θ y).mpr hy
  · exact fun θ y hy => magnetic_rotation n hn u hu z θ y hy
  · exact fun y _ i => ComplexMagneticReflection.sector_magnetic_axial n hn z u hu y i

theorem radial_zero_ae (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) (z : ℂ) :
    ∀ᵐ x ∂(volume : Measure Space),
      radialDot (fun j y => ComplexSphereMaxwell.magnetic n hn z u y j) x = 0 := by
  filter_upwards [good_ae n hn u] with x hx
  exact radial_zero_good n hn u hu z x hx

def representative (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2)
    (x : Space) : Fin 3 → ℂ := by
  classical
  exact if good n hn u x then ComplexSphereMaxwell.magnetic n hn z u x else 0

theorem representative_ae (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorFourier.VectorL2) :
    representative n hn z u =ᵐ[volume] ComplexSphereMaxwell.magnetic n hn z u := by
  filter_upwards [good_ae n hn u] with x hx
  simp only [representative, if_pos hx]

theorem representative_radial_zero (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (x : Space) :
    radialDot (fun j y => representative n hn z u y j) x = 0 := by
  by_cases hx : good n hn u x
  · simpa only [radialDot, representative, if_pos hx] using radial_zero_good n hn u hu z x hx
  · simp [radialDot, representative, hx]

theorem representative_rotation (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (θ : ℝ) (x : Space) :
    representative n hn z u (rotation θ x) = vector θ (representative n hn z u x) := by
  by_cases hx : good n hn u x
  · simp only [representative, if_pos hx,
      if_pos ((Packet02GoodRotation.good_rotation n hn u hu.1 θ x).mpr hx)]
    exact magnetic_rotation n hn u hu z θ x hx
  · have hy := (Packet02GoodRotation.good_rotation n hn u hu.1 θ x).not.mpr hx
    funext i
    fin_cases i <;> simp [representative, hx, hy, vector]

theorem representative_reflection (n : ℝ) (hn : 1 < n) (z : ℂ)
    (u : VectorFourier.VectorL2) (hu : u ∈ electricSector) (x : Space) (i : Fin 3) :
    representative n hn z u (reflection x) i = -(sign i : ℂ) * representative n hn z u x i := by
  by_cases hx : good n hn u x
  · simp only [representative, if_pos hx,
      if_pos ((Packet02GoodRotation.good_reflection n hn u hu x).mpr hx)]
    exact ComplexMagneticReflection.sector_magnetic_axial n hn z u hu x i
  · have hy := (Packet02GoodRotation.good_reflection n hn u hu x).not.mpr hx
    simp [representative, hx, hy]

end OQ14.Packet02MagneticVanishing
#print axioms OQ14.Packet02MagneticVanishing.magnetic_rotation
#print axioms OQ14.Packet02MagneticVanishing.radial_zero_good
#print axioms OQ14.Packet02MagneticVanishing.radial_zero_ae
#print axioms OQ14.Packet02MagneticVanishing.representative_ae
#print axioms OQ14.Packet02MagneticVanishing.representative_radial_zero
#print axioms OQ14.Packet02MagneticVanishing.representative_rotation
#print axioms OQ14.Packet02MagneticVanishing.representative_reflection
