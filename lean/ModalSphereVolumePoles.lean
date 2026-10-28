import ModalSphereVolumeKernel
import VolumeAnalyticAlternative

/-! Actual sphere volume-resolvent poles with arbitrarily high frequency-to-decay ratio. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ModalSphereVolumePoles
open OQ14.ModalAlgebra OQ14.ModalMatching OQ14.ComplexConvolutionAnalytic
open scoped Topology

theorem inverse_pole (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : tmDet 1 (n : ℂ) z = 0) :
    ∃ hm : MeromorphicAt
      (fun w => Ring.inverse (volumeBlock (ModalWeightedMode.coefficient n hn) w 1)) z,
      hm.order < 0 :=
  ⟨VolumeAnalyticAlternative.inverse_meromorphicAt _ 1 (by norm_num)
      (ModalWeightedMode.coefficient_support n hn) z,
    VolumeAnalyticAlternative.inverse_order_negative _ 1 (by norm_num)
      (ModalWeightedMode.coefficient_support n hn) z
      (ModalSphereVolumeKernel.volumeBlock_not_isUnit n hn z hz hd)⟩

theorem punctured_invertibility (n : ℝ) (hn : 1 < n) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, IsUnit (volumeBlock (ModalWeightedMode.coefficient n hn) w 1) :=
  VolumeAnalyticAlternative.volumeBlock_punctured_isUnit _ 1 (by norm_num)
    (ModalWeightedMode.coefficient_support n hn) z

theorem high_quality_volume_poles (n : ℝ) (hn : 1 < n) (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k : ModalShell.Frequency, ∃ f : Amplitudes,
      L < k.val.re ∧ k.val.im < 0 ∧ Q < k.val.re / (-2*k.val.im) ∧
      tmDet 1 (n : ℂ) k.val = 0 ∧ deriv (tmDet 1 (n : ℂ)) k.val ≠ 0 ∧
      ModalWeightedMode.weightedMode n hn k f ≠ 0 ∧
      volumeBlock (ModalWeightedMode.coefficient n hn) k.val 1
        (ModalWeightedMode.weightedMode n hn k f) = 0 ∧
      (∃ hm : MeromorphicAt
        (fun w => Ring.inverse (volumeBlock (ModalWeightedMode.coefficient n hn) w 1)) k.val,
        hm.order < 0) ∧
      (∀ᶠ w in 𝓝[≠] k.val, IsUnit (volumeBlock (ModalWeightedMode.coefficient n hn) w 1)) := by
  obtain ⟨z,hz,hd,hs,hL,hi,hQz⟩ := ModalAsymptotics.tm_high_quality_zeros 1 n hn L Q hQ
  obtain ⟨f,hf,hker⟩ := ModalSphereVolumeKernel.exists_nonzero_weighted_residue n hn ⟨z,hz⟩ hd hs
  exact ⟨⟨z,hz⟩,f,hL,hi,hQz,hd,hs,hf,hker,inverse_pole n hn z hz hd,
    punctured_invertibility n hn z⟩

end OQ14.ModalSphereVolumePoles

#print axioms OQ14.ModalSphereVolumePoles.inverse_pole
#print axioms OQ14.ModalSphereVolumePoles.punctured_invertibility
#print axioms OQ14.ModalSphereVolumePoles.high_quality_volume_poles
