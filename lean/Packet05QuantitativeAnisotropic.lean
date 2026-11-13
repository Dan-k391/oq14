import Packet05GraphNormalFluxH1
import Packet05AnisotropicWeakEmbedding

/-! Preserve the explicit anisotropic Fourier supremum bound when converting
actual weak partials into a continuous representative. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativeAnisotropic
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05AnisotropicEmbedding OQ14.Packet05AnisotropicWeakEmbedding

theorem continuous_weak_tangential_h1_bound (u : L2Scalar) (hu : CompactRepresentative u)
    (D : Fin 3 → L2Scalar) (hD : ∀ i, HasWeakPartial u (D i) i)
    (H : Fin 3 → Fin 3 → L2Scalar)
    (hH : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (D i) (H i j) j) :
    let hw := anisotropic_weight_memLp_of_weak_partials u hu D hD H hH
    ∃ f : Space → ℂ, Continuous f ∧ (u : Space → ℂ) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ ‖spectralInverse_memLp.toLp spectralInverse‖ *
        ‖hw.toLp (fun x : Space => (spectralFactor x : ℂ) *
          (FourierL2.fourierEquiv.symm u) x)‖ := by
  exact continuous_of_anisotropic_fourier u
    (anisotropic_weight_memLp_of_weak_partials u hu D hD H hH)

end OQ14.Packet05QuantitativeAnisotropic
#print axioms OQ14.Packet05QuantitativeAnisotropic.continuous_weak_tangential_h1_bound
