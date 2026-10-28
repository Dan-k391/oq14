import ModalSphereVolumePoles
import ComplexDilationVolume

/-! Actual sphere volume poles at a prescribed positive real frequency,
with a fixed material contrast and arbitrarily large quality factor. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalFixedFrequencyVolumePoles
open Complex Metric Filter OQ14.ComplexConvolutionAnalytic
  OQ14.FrequencyScalingMaxwell
open scoped Topology

def coefficient (n : ℝ) (hn : 1 < n) (s : ℝ) : StaticCoefficient.Coefficient :=
  scaleCoeff s (ModalWeightedMode.coefficient n hn)

theorem coefficient_bound (n : ℝ) (hn : 1 < n) (s : ℝ) :
    (coefficient n hn s).bound = n ^ 2 - 1 := rfl

theorem coefficient_value (n : ℝ) (hn : 1 < n) (s : ℝ) (hs : 0 < s)
    (x : Maxwell.Space) :
    (coefficient n hn s).value (VectorFourier.coordinateMap x) =
      if ‖x‖ < 1 / s then n ^ 2 - 1 else 0 := by
  unfold coefficient
  rw [scaleCoeff_value, ← coordinateMap_smul, ModalWeightedMode.coefficient_value]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  congr 1
  rw [lt_div_iff₀ hs, mul_comm]

theorem coefficient_support (n : ℝ) (hn : 1 < n) (s : ℝ) (hs : 0 < s)
    (x : Maxwell.Space) (hx : x ∉ closedBall 0 (1 / s)) :
    (coefficient n hn s).value (VectorFourier.coordinateMap x) = 0 :=
  ComplexDilationVolume.coefficient_support s 1 hs _
    (ModalWeightedMode.coefficient_support n hn) x hx

theorem scaled_pole (n : ℝ) (hn : 1 < n) (s : ℝ) (hs : 0 < s)
    (z : ℂ) (hz : z ≠ 0) (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    ∃ hm : MeromorphicAt
      (fun w => Ring.inverse (volumeBlock (coefficient n hn s) w (1 / s)))
      ((s : ℂ) * z), hm.order < 0 := by
  have hc := coefficient_support n hn s hs
  have hR : 0 ≤ 1 / s := (one_div_pos.mpr hs).le
  refine ⟨VolumeAnalyticAlternative.inverse_meromorphicAt _ _ hR hc _, ?_⟩
  apply VolumeAnalyticAlternative.inverse_order_negative _ _ hR hc
  intro hu
  exact ModalSphereVolumeKernel.volumeBlock_not_isUnit n hn z hz hd
    ((ComplexDilationVolume.volumeBlock_isUnit_iff s 1 hs (by norm_num) _ z).mp hu)

theorem prescribed_frequency (n : ℝ) (hn : 1 < n)
    (ω : ℝ) (hω : 0 < ω) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ s : ℝ, 0 < s ∧ ∃ z : ℂ, ∃ u : VectorFourier.VectorL2,
      z.re = ω ∧ z.im < 0 ∧ Q < z.re / (-2 * z.im) ∧
      (coefficient n hn s).bound = n ^ 2 - 1 ∧
      (∀ x : Maxwell.Space, x ∉ closedBall 0 (1 / s) →
        (coefficient n hn s).value (VectorFourier.coordinateMap x) = 0) ∧
      u ≠ 0 ∧ volumeBlock (coefficient n hn s) z (1 / s) u = 0 ∧
      (∃ hm : MeromorphicAt
        (fun w => Ring.inverse (volumeBlock (coefficient n hn s) w (1 / s))) z,
        hm.order < 0) ∧
      (∀ᶠ w in 𝓝[≠] z, IsUnit (volumeBlock (coefficient n hn s) w (1 / s))) := by
  obtain ⟨k, f, hk, hi, hquality, hd, _, hu, hker, _, _⟩ :=
    ModalSphereVolumePoles.high_quality_volume_poles n hn 0 Q hQ
  let s := ω / k.val.re
  have hs : 0 < s := div_pos hω hk
  let z := (s : ℂ) * k.val
  have hre : z.re = s * k.val.re := by simp [z]
  have him : z.im = s * k.val.im := by simp [z]
  have htarget : z.re = ω := by rw [hre]; exact div_mul_cancel₀ ω hk.ne'
  have hnegative : z.im < 0 := by rw [him]; exact mul_neg_of_pos_of_neg hs hi
  have hratio : z.re / (-2 * z.im) = k.val.re / (-2 * k.val.im) := by
    rw [hre, him]
    have hi0 : k.val.im ≠ 0 := ne_of_lt hi
    field_simp
    ring
  have htransport := ComplexDilationVolume.nonzero_kernel_transport s 1 hs (by norm_num)
    (ModalWeightedMode.coefficient n hn) k.val (ModalWeightedMode.weightedMode n hn k f) hu hker
  refine ⟨s, hs, z, DilationL2.dilate s (ModalWeightedMode.weightedMode n hn k f),
    htarget, hnegative, hratio ▸ hquality, coefficient_bound n hn s,
    coefficient_support n hn s hs, htransport.1, htransport.2,
    scaled_pole n hn s hs k.val k.property hd, ?_⟩
  exact VolumeAnalyticAlternative.volumeBlock_punctured_isUnit _ _
    (one_div_pos.mpr hs).le (coefficient_support n hn s hs) z

end OQ14.ModalFixedFrequencyVolumePoles

#print axioms OQ14.ModalFixedFrequencyVolumePoles.coefficient_bound
#print axioms OQ14.ModalFixedFrequencyVolumePoles.coefficient_value
#print axioms OQ14.ModalFixedFrequencyVolumePoles.coefficient_support
#print axioms OQ14.ModalFixedFrequencyVolumePoles.scaled_pole
#print axioms OQ14.ModalFixedFrequencyVolumePoles.prescribed_frequency
