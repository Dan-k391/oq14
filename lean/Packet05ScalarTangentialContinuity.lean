import Packet05GraphTransmissionReconstruction
import Packet05QuantitativeAnisotropic

/-! The two actual tangential derivative directions suffice for a continuous
scalar representative after nested localization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ScalarTangentialContinuity
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05TangentialGradientH1 OQ14.Packet05LocalizedAnisotropic

theorem scalar_tangential_continuity (V : Set Space) (hV : IsOpen V)
    (u : L2Scalar) (C : L2Vector) (hC : ∀ j, HasWeakPartial u (C j) j)
    (τ χ : Test) (hτ : ∀ x ∈ V, τ.function x = 1)
    (hχ : tsupport χ.function ⊆ V) (hχ2 : ContDiff ℝ 2 χ.function)
    (hDer : ∀ i, i ≠ 2 → ∀ j, ∃ v : L2Scalar,
      HasWeakPartial (scaleL2 τ.function τ.regular.continuous τ.compact (C j)) v i) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact u x) =ᵐ[MeasureTheory.volume] f := by
  apply cutoff_continuous_of_tangential_h1 u C hC χ hχ2
  intro i hi j
  obtain ⟨D,hD⟩ := localized_tangential_gradient_h1 V hV u C hC τ χ hτ hχ i (hDer i hi)
  exact ⟨D j,hD j⟩

end OQ14.Packet05ScalarTangentialContinuity
#print axioms OQ14.Packet05ScalarTangentialContinuity.scalar_tangential_continuity
