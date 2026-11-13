import ComplexMagneticDebye
import ModalMeridionalVolume

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexMagneticReflection
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalMeridionalReflection
  OQ14.ModalMeridionalStatic OQ14.ModalWeightedMode OQ14.ComplexGreenKernel
open OQ14.WeakCurl (next previous)
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem gradient_reflection (z : ℂ) (x : Space) (j : Fin 3) :
    phiGradient z (reflection x) j = (sign j : ℂ) * phiGradient z x j := by
  unfold phiGradient
  rw [reflection.norm_map, reflection_coordinate]
  push_cast
  ring

theorem gradient_response_reflection (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (x : Space) (j l : Fin 3) :
    KernelConvolution.response (fun v => phiGradient z v j)
      (DynamicVolume.source (coefficient n hn) (action u) l) x =
      (sign j : ℂ) * (sign l : ℂ) *
        KernelConvolution.response (fun v => phiGradient z v j)
          (DynamicVolume.source (coefficient n hn) u l) (reflection x) := by
  unfold KernelConvolution.response
  have h1 : (∫ y, DynamicVolume.source (coefficient n hn) (action u) l y * phiGradient z (x-y) j) =
      ∫ y, (sign l : ℂ) * (DynamicVolume.source (coefficient n hn) u l (reflection y) * phiGradient z (x-y) j) := by
    apply integral_congr_ae
    filter_upwards [source_action n hn u l] with y hy
    rw [hy]
    ring
  have h2 := reflection.measurePreserving.integral_comp reflection.toHomeomorph.measurableEmbedding
    (fun y => DynamicVolume.source (coefficient n hn) u l y * phiGradient z (reflection x-y) j)
  simp only [reflection_reflection] at h2
  rw [h1, integral_const_mul]
  have h3 : (∫ y, DynamicVolume.source (coefficient n hn) u l (reflection y) * phiGradient z (x-y) j) =
      (sign j : ℂ) * ∫ y, DynamicVolume.source (coefficient n hn) u l y * phiGradient z (reflection x-y) j := by
    rw [← h2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have h := gradient_reflection z (x-y) j
    rw [map_sub] at h
    rw [h]
    have hs := sign_sq j
    linear_combination -(DynamicVolume.source (coefficient n hn) u l (reflection y) * phiGradient z (x-y) j) * hs
  rw [h3]
  ring

theorem magnetic_reflection (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (x : Space) (i : Fin 3) :
    ComplexSphereMaxwell.magnetic n hn z (action u) x i =
      -(sign i : ℂ) * ComplexSphereMaxwell.magnetic n hn z u (reflection x) i := by
  unfold ComplexSphereMaxwell.magnetic ComplexMagneticLocal.magnetic
  rw [gradient_response_reflection n hn z u x (next i) (previous i),
    gradient_response_reflection n hn z u x (previous i) (next i)]
  fin_cases i <;> simp [next, previous, sign] <;> ring

theorem sector_magnetic_axial (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (hu : u ∈ electricSector) (x : Space) (i : Fin 3) :
    ComplexSphereMaxwell.magnetic n hn z u (reflection x) i =
      -(sign i : ℂ) * ComplexSphereMaxwell.magnetic n hn z u x i := by
  have hu' : action u = u := by
    have h := hu.2
    change (action - 1) u = 0 at h
    simpa using sub_eq_zero.mp h
  have h := magnetic_reflection n hn z u (reflection x) i
  rw [hu', reflection_reflection] at h
  exact h

theorem radialDot_odd (n : ℝ) (hn : 1 < n) (z : ℂ) (u : VectorL2)
    (hu : u ∈ electricSector) (x : Space) :
    WeakDebyeScalar.radialDot (fun j y => ComplexSphereMaxwell.magnetic n hn z u y j) (reflection x) =
      -WeakDebyeScalar.radialDot (fun j y => ComplexSphereMaxwell.magnetic n hn z u y j) x := by
  unfold WeakDebyeScalar.radialDot
  simp only [reflection_coordinate, ofReal_mul, sector_magnetic_axial n hn z u hu]
  simp only [Fin.sum_univ_three]
  simp [sign]
  ring

#print axioms OQ14.ComplexMagneticReflection.radialDot_odd
#print axioms OQ14.ComplexMagneticReflection.gradient_reflection
#print axioms OQ14.ComplexMagneticReflection.magnetic_reflection
#print axioms OQ14.ComplexMagneticReflection.gradient_response_reflection
#print axioms OQ14.ComplexMagneticReflection.sector_magnetic_axial
end OQ14.ComplexMagneticReflection
