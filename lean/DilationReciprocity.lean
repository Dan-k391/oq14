import ComplexDilationVolume
import ModalVolumeNormalization

/-! Physical dilation of the bilinear volume derivative normalization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4000
namespace OQ14.DilationReciprocity
open Complex MeasureTheory OQ14.DilationL2 OQ14.KernelReciprocity
  OQ14.ComplexVolumeReciprocity OQ14.ComplexConvolutionAnalytic
  OQ14.FrequencyScalingMaxwell

abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

theorem vectorPair_dilate (s : ℝ) (hs : 0 < s) (u v : VectorL2) :
    vectorPair (dilate s u) (dilate s v) = (s : ℂ)⁻¹ * vectorPair u v := by
  unfold vectorPair scalarPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (∫ x : Space, NewtonL2.physicalCoordinate (dilate s u) i x *
      NewtonL2.physicalCoordinate (dilate s v) i x) =
      (s : ℂ)⁻¹ * ∫ x : Space, NewtonL2.physicalCoordinate u i x * NewtonL2.physicalCoordinate v i x
  have he : (∫ x : Space, NewtonL2.physicalCoordinate (dilate s u) i x *
      NewtonL2.physicalCoordinate (dilate s v) i x) =
      (s : ℂ)^2 * ∫ x : Space, NewtonL2.physicalCoordinate u i (s • x) *
        NewtonL2.physicalCoordinate v i (s • x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [physicalCoordinate_dilate s hs u i, physicalCoordinate_dilate s hs v i]
      with x hu hv
    rw [hu, hv]
    ring
  rw [he, integral_comp_smul_space (fun x => NewtonL2.physicalCoordinate u i x *
    NewtonL2.physicalCoordinate v i x) s, abs_of_pos (by positivity), Complex.real_smul]
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  push_cast
  field_simp
  ring

theorem derivative_chain (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R)
    (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorL2) :
    (s : ℂ) •
      (deriv (fun w => volumeBlock (scaleCoeff s c) w (R/s)) ((s : ℂ)*z) (dilate s u)) =
      dilate s (deriv (fun w => volumeBlock c w R) z u) := by
  have hA : HasDerivAt (fun w : ℂ => volumeBlock (scaleCoeff s c) w (R/s))
      (deriv (fun w => volumeBlock (scaleCoeff s c) w (R/s)) ((s : ℂ)*z)) ((s : ℂ)*z) :=
    (volumeBlock_differentiable (scaleCoeff s c) (R/s) (div_nonneg hR hs.le) ((s : ℂ)*z)).hasDerivAt
  have hscale : HasDerivAt (fun w : ℂ => (s : ℂ)*w) (s : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (s : ℂ)
  have hcomp := hA.scomp z hscale
  have hf := hcomp.clm_apply (hasDerivAt_const z (dilate s u))
  have hg := (dilate s).hasFDerivAt.comp_hasDerivAt z
    (((volumeBlock_differentiable c R hR z).hasDerivAt).clm_apply (hasDerivAt_const z u))
  have he : (fun w : ℂ => volumeBlock (scaleCoeff s c) ((s : ℂ)*w) (R/s) (dilate s u)) =
      fun w => dilate s (volumeBlock c w R u) := by
    funext w
    exact congrFun (congrArg DFunLike.coe (ComplexDilationVolume.complex_comp s R hs hR c w)) u
  change HasDerivAt (fun w : ℂ => volumeBlock (scaleCoeff s c) ((s : ℂ)*w) (R/s) (dilate s u)) _ z at hf
  rw [he] at hf
  simpa only [ContinuousLinearMap.smul_apply, map_zero, add_zero] using hf.unique hg

theorem derivative_apply (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R)
    (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorL2) :
    deriv (fun w => volumeBlock (scaleCoeff s c) w (R/s)) ((s : ℂ)*z) (dilate s u) =
      (s : ℂ)⁻¹ • dilate s (deriv (fun w => volumeBlock c w R) z u) := by
  rw [← derivative_chain s R hs hR c z u, inv_smul_smul₀ (ofReal_ne_zero.mpr hs.ne')]

theorem derivative_pairing_scale (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R)
    (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorL2) :
    vectorPair
      (deriv (fun w => volumeBlock (scaleCoeff s c) w (R/s)) ((s : ℂ)*z) (dilate s u))
      (dilate s u) =
      ((s : ℂ)⁻¹)^2 * vectorPair (deriv (fun w => volumeBlock c w R) z u) u := by
  rw [derivative_apply s R hs hR c z u, vectorPair_smul_left, vectorPair_dilate s hs]
  ring

theorem unit_pairing_transport (s R : ℝ) (hs : 0 < s) (hR : 0 ≤ R)
    (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorL2)
    (hu : vectorPair (deriv (fun w => volumeBlock c w R) z u) u = 1) :
    vectorPair
      (deriv (fun w => volumeBlock (scaleCoeff s c) w (R/s)) ((s : ℂ)*z)
        ((s : ℂ) • dilate s u)) ((s : ℂ) • dilate s u) = 1 := by
  rw [ModalVolumeNormalization.pairing_rescale, derivative_pairing_scale s R hs hR c z u, hu]
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  field_simp

end OQ14.DilationReciprocity

#print axioms OQ14.DilationReciprocity.vectorPair_dilate
#print axioms OQ14.DilationReciprocity.derivative_chain
#print axioms OQ14.DilationReciprocity.derivative_apply
#print axioms OQ14.DilationReciprocity.derivative_pairing_scale
#print axioms OQ14.DilationReciprocity.unit_pairing_transport
