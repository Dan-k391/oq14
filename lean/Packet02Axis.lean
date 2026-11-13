import Packet02MagneticRotation
import ComplexMagneticReflection
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02Axis
open Complex MeasureTheory OQ14.Maxwell OQ14.ModalAxialRotation OQ14.ComplexGreenKernel
  OQ14.ModalMeridionalReflection
open OQ14.WeakCurl (next previous)

def halfsign (i : Fin 3) : ℂ := if i = 2 then 1 else -1

theorem source_halfturn (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (i : Fin 3) :
    (fun y => DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i (rotation Real.pi y)) =ᵐ[volume]
      fun y => halfsign i * DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i y := by
  filter_upwards [Packet02SourceSymmetry.source_covariant n hn u hu Real.pi i] with y hy
  rw [hy]
  fin_cases i <;> simp [matrix, halfsign, Fin.sum_univ_three]

theorem gradient_halfturn (z : ℂ) (x : Space) (i : Fin 3) :
    phiGradient z (rotation Real.pi x) i = halfsign i * phiGradient z x i := by
  rw [Packet02MagneticRotation.gradient_covariant]
  fin_cases i <;> simp [matrix, halfsign, Fin.sum_univ_three]

theorem response_halfturn (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (z : ℂ) (x : Space) (j l : Fin 3) :
    KernelConvolution.response (fun v => phiGradient z v j)
      (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u l) (rotation Real.pi x) =
      (halfsign j * halfsign l) * KernelConvolution.response (fun v => phiGradient z v j)
      (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u l) x := by
  unfold KernelConvolution.response
  have hc := (rotation Real.pi).measurePreserving.integral_comp (rotation Real.pi).toHomeomorph.measurableEmbedding
    (fun y => DynamicVolume.source (ModalWeightedMode.coefficient n hn) u l y * phiGradient z (rotation Real.pi x-y) j)
  rw [← hc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [source_halfturn n hn u hu l] with y hy
  rw [hy, ← map_sub (rotation Real.pi), gradient_halfturn]
  ring

theorem magnetic_halfturn (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (z : ℂ) (x : Space) (i : Fin 3) :
    ComplexSphereMaxwell.magnetic n hn z u (rotation Real.pi x) i =
      halfsign i * ComplexSphereMaxwell.magnetic n hn z u x i := by
  unfold ComplexSphereMaxwell.magnetic ComplexMagneticLocal.magnetic
  rw [response_halfturn n hn u hu z x (next i) (previous i),
    response_halfturn n hn u hu z x (previous i) (next i)]
  fin_cases i <;> simp [next, previous, halfsign] <;> ring

theorem axis_vector_zero (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) (z : ℂ) (x : Space) (hx0 : x 0 = 0) (hx1 : x 1 = 0) :
    ComplexSphereMaxwell.magnetic n hn z u x = 0 := by
  have hr : rotation Real.pi x = x := by
    ext i
    fin_cases i <;> simp [rotation, spatial, WithLp.equiv_symm_pi_apply, hx0, hx1]
  have h0 := magnetic_halfturn n hn u hu.1 z x 0
  have h1 := magnetic_halfturn n hn u hu.1 z x 1
  rw [hr] at h0 h1
  simp [halfsign] at h0 h1
  have href : reflection x = x := by
    ext i
    fin_cases i <;> simp [reflection_coordinate, sign, hx1]
  have h2 := ComplexMagneticReflection.sector_magnetic_axial n hn z u hu x 2
  rw [href] at h2
  simp [sign] at h2
  funext i
  fin_cases i
  · change ComplexSphereMaxwell.magnetic n hn z u x 0 = 0
    linear_combination (1/2 : ℂ) * h0
  · change ComplexSphereMaxwell.magnetic n hn z u x 1 = 0
    linear_combination (1/2 : ℂ) * h1
  · change ComplexSphereMaxwell.magnetic n hn z u x 2 = 0
    linear_combination (1/2 : ℂ) * h2

#print axioms OQ14.Packet02Axis.source_halfturn
#print axioms OQ14.Packet02Axis.gradient_halfturn
#print axioms OQ14.Packet02Axis.response_halfturn
#print axioms OQ14.Packet02Axis.magnetic_halfturn
#print axioms OQ14.Packet02Axis.axis_vector_zero
end OQ14.Packet02Axis
