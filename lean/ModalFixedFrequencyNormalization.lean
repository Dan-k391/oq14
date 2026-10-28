import ModalFixedFrequencyVolumePoles
import DilationReciprocity

/-! Actual reciprocal-normalized sphere volume modes at prescribed frequency. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000

namespace OQ14.ModalFixedFrequencyNormalization
open Complex Metric Filter OQ14.ComplexConvolutionAnalytic OQ14.KernelReciprocity
  OQ14.ComplexVolumeReciprocity OQ14.ModalFixedFrequencyVolumePoles
open scoped Topology

theorem prescribed_frequency (n : ℝ) (hn : 1 < n)
    (ω : ℝ) (hω : 0 < ω) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ s : ℝ, 0 < s ∧ ∃ z : ℂ, ∃ u : VectorFourier.VectorL2,
      z.re = ω ∧ z.im < 0 ∧ Q < z.re / (-2 * z.im) ∧
      (coefficient n hn s).bound = n ^ 2 - 1 ∧
      (∀ x : Maxwell.Space, x ∉ closedBall 0 (1 / s) →
        (coefficient n hn s).value (VectorFourier.coordinateMap x) = 0) ∧
      u ≠ 0 ∧ volumeBlock (coefficient n hn s) z (1 / s) u = 0 ∧
      pairFunctional u ≠ 0 ∧
      (∀ v, pairFunctional u (volumeBlock (coefficient n hn s) z (1 / s) v) = 0) ∧
      pairFunctional u (deriv (fun w => volumeBlock (coefficient n hn s) w (1 / s)) z u) = 1 ∧
      (∃ hm : MeromorphicAt
        (fun w => Ring.inverse (volumeBlock (coefficient n hn s) w (1 / s))) z,
        hm.order < 0) ∧
      (∀ᶠ w in 𝓝[≠] z, IsUnit (volumeBlock (coefficient n hn s) w (1 / s))) := by
  obtain ⟨k, _, hk, hi, hquality, hd, hsimple, _, _, _, _⟩ :=
    ModalSphereVolumePoles.high_quality_volume_poles n hn 0 Q hQ
  obtain ⟨f, a, _, hu0, hker0, _, _, hunit0⟩ :=
    ModalVolumeNormalization.exists_normalized_weighted_mode n hn k hd hsimple
  let u0 := a • ModalWeightedMode.weightedMode n hn k f
  let s := ω / k.val.re
  have hs : 0 < s := div_pos hω hk
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  let z := (s : ℂ) * k.val
  let u := (s : ℂ) • DilationL2.dilate s u0
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
    (ModalWeightedMode.coefficient n hn) k.val u0 hu0 hker0
  have hu : u ≠ 0 := smul_ne_zero hs0 htransport.1
  have hker : volumeBlock (coefficient n hn s) z (1 / s) u = 0 := by
    change volumeBlock (FrequencyScalingMaxwell.scaleCoeff s (ModalWeightedMode.coefficient n hn))
      ((s : ℂ)*k.val) (1/s) ((s : ℂ) • DilationL2.dilate s u0) = 0
    rw [map_smul, htransport.2, smul_zero]
  have hunit : pairFunctional u
      (deriv (fun w => volumeBlock (coefficient n hn s) w (1 / s)) z u) = 1 :=
    DilationReciprocity.unit_pairing_transport s 1 hs (by norm_num)
      (ModalWeightedMode.coefficient n hn) k.val u0 hunit0
  have hleft (v : VectorFourier.VectorL2) :
      pairFunctional u (volumeBlock (coefficient n hn s) z (1 / s) v) = 0 := by
    change vectorPair (volumeBlock (coefficient n hn s) z (1 / s) v) u = 0
    rw [volumeBlock_reciprocity _ (1/s) (one_div_pos.mpr hs).le, hker, vectorPair_comm]
    exact (pairFunctional v).map_zero
  have hfunctional : pairFunctional u ≠ 0 := by
    intro hzero
    have h := hunit
    rw [hzero, ContinuousLinearMap.zero_apply] at h
    exact zero_ne_one h
  exact ⟨s, hs, z, u, htarget, hnegative, hratio ▸ hquality,
    coefficient_bound n hn s, coefficient_support n hn s hs, hu, hker, hfunctional,
    hleft, hunit, scaled_pole n hn s hs k.val k.property hd,
    VolumeAnalyticAlternative.volumeBlock_punctured_isUnit _ _
      (one_div_pos.mpr hs).le (coefficient_support n hn s hs) z⟩

end OQ14.ModalFixedFrequencyNormalization

#print axioms OQ14.ModalFixedFrequencyNormalization.prescribed_frequency
