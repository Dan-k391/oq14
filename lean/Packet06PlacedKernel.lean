import Packet06TranslationReciprocal
import Packet06ComplexReciprocal

/-! Actual normalized complex material kernels under the combined rigid and
    frequency placement, with the exact physical reciprocal normalization. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PlacedKernel
open Metric Maxwell Packet06PhysicalNormalization

def placedCoefficient (s : ℝ) (a : Space) (c : StaticCoefficient.Coefficient) : StaticCoefficient.Coefficient :=
  Packet06TranslationMaterial.coefficient a (FrequencyScalingMaxwell.scaleCoeff s (Packet06CyclicMaterial.coefficient c))

def placedUnknown (s : ℝ) (a : Space) (u : VectorFourier.VectorL2) : VectorFourier.VectorL2 :=
  Packet06TranslationL2.action a ((Real.sqrt s : ℂ) • DilationL2.dilate s (Packet06CyclicL2.action u))

theorem placed_normalized_kernel (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : VectorFourier.VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u = 0)
    (hN : reciprocalNorm c R z u = 1) (s : ℝ) (hs : 0 < s) (a : Space) :
    (∀ x : Space, x ∉ closedBall 0 (R/s+‖a‖) → (placedCoefficient s a c).value (VectorFourier.coordinateMap x) = 0) ∧
    ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z) (R/s+‖a‖)
      (placedUnknown s a u) = 0 ∧
    reciprocalNorm (placedCoefficient s a c) (R/s+‖a‖) ((s : ℂ)*z) (placedUnknown s a u) = 1 ∧
    placedUnknown s a u ≠ 0 := by
  let cr := Packet06CyclicMaterial.coefficient c
  let ur := Packet06CyclicL2.action u
  let cd := FrequencyScalingMaxwell.scaleCoeff s cr
  let ud := (Real.sqrt s : ℂ) • DilationL2.dilate s ur
  have hcr : ∀ x : Space, x ∉ closedBall 0 R → cr.value (VectorFourier.coordinateMap x) = 0 :=
    Packet06CyclicDynamic.coefficient_support c R hc
  have hkr : ComplexConvolutionAnalytic.volumeBlock cr z R ur = 0 :=
    Packet06CyclicReciprocal.kernel_rotation c R hR hc z u hu
  have hNr : reciprocalNorm cr R z ur = 1 := by
    rw [Packet06CyclicReciprocal.reciprocalNorm_rotation c R hR hc]
    exact hN
  have hcd : ∀ x : Space, x ∉ closedBall 0 (R/s) → cd.value (VectorFourier.coordinateMap x) = 0 :=
    ComplexDilationVolume.coefficient_support s R hs cr hcr
  have hkd : ComplexConvolutionAnalytic.volumeBlock cd ((s : ℂ)*z) (R/s) ud = 0 := by
    have h := congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L ur)
      (ComplexDilationVolume.complex_comp s R hs hR cr z)
    change ComplexConvolutionAnalytic.volumeBlock cd ((s : ℂ)*z) (R/s) (DilationL2.dilate s ur) =
      DilationL2.dilate s (ComplexConvolutionAnalytic.volumeBlock cr z R ur) at h
    rw [hkr,map_zero] at h
    change ComplexConvolutionAnalytic.volumeBlock cd ((s : ℂ)*z) (R/s)
      ((Real.sqrt s : ℂ) • DilationL2.dilate s ur) = 0
    rw [map_smul,h,smul_zero]
  have hNd : reciprocalNorm cd (R/s) ((s : ℂ)*z) ud = 1 := by
    change reciprocalNorm (FrequencyScalingMaxwell.scaleCoeff s cr) (R/s)
      ((s : ℂ)*z) ((Real.sqrt s : ℂ) • DilationL2.dilate s ur) = 1
    rw [Packet06ComplexReciprocal.reciprocalNorm_dilate_rescale s R hs hR cr z (Real.sqrt s : ℂ) ur, hNr]
    have hsq : (Real.sqrt s : ℂ)^2 = (s : ℂ) := by exact_mod_cast Real.sq_sqrt hs.le
    rw [hsq]
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
  have hT := Packet06TranslationReciprocal.reciprocalNorm_translation a cd (R/s) (div_nonneg hR hs.le) hcd ((s : ℂ)*z) ud
  have hK := Packet06TranslationReciprocal.kernel_translation a cd (R/s) (div_nonneg hR hs.le) hcd ((s : ℂ)*z) ud hkd
  have hP : reciprocalNorm (placedCoefficient s a c) (R/s+‖a‖) ((s : ℂ)*z) (placedUnknown s a u) = 1 := by
    change reciprocalNorm (Packet06TranslationMaterial.coefficient a cd) (R/s+‖a‖)
      ((s : ℂ)*z) (Packet06TranslationL2.action a ud) = 1
    rw [hT,hNd]
  refine ⟨Packet06TranslationMaterial.coefficient_support a cd (R/s) hcd, hK, hP, ?_⟩
  intro hz
  rw [hz] at hP
  simp [reciprocalNorm,KernelReciprocity.vectorPair,KernelReciprocity.scalarPair] at hP

end OQ14.Packet06PlacedKernel
#print axioms OQ14.Packet06PlacedKernel.placed_normalized_kernel
