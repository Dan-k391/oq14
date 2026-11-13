import Packet05QuantitativeCutoffNorms
import Packet05ScalarCutoffRepresentative

/-! Explicit plateau bounds for the two graph-tangential scalar gradients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TangentialPlateauBound
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05PartialProduct MaxwellCutoffCommutator Packet05ScalarCutoffTransfer

theorem tangential_plateau_original_bound (T : Set Space) (hT : IsOpen T)
    (κ : RealTest Set.univ) (χ : Test) (hκ : ∀ x ∈ T, κ.function x = 1)
    (hχ : ∀ x ∈ T, χ.function x = 1) (u : L2Scalar) (D : Fin 3 → L2Scalar)
    (hD : ∀ i, HasWeakPartial (cutScalar κ u) (D i) i)
    (hχ2 : ContDiff ℝ 2 χ.function) (V : Fin 3 → Fin 3 → L2Scalar)
    (hV : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (D i)) (V i j) j)
    (a b c : ℝ) (ha : ∀ x, ‖χ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ c) :
    ∃ f : Space → ℂ, Continuous f ∧ (u : Space → ℂ) =ᵐ[volume.restrict T] f ∧
      ∀ x, ‖f x‖ ≤ Packet05ExplicitAnisotropicBound.universalConstant *
        ((a+3*b+6*c)*‖cutScalar κ u‖ + (a+2*b)*(∑ i : Fin 3, ‖D i‖) +
          ∑ i : Fin 2, ∑ j : Fin 3, ‖V i.castSucc j‖) := by
  obtain ⟨f,hf,hae,hbound⟩ := Packet05QuantitativeCutoffNorms.cutoff_original_derivatives
    (cutScalar κ u) D hD χ hχ2 V hV a b c ha hb hc
  exact ⟨f,hf,Packet05ScalarCutoffRepresentative.uncut_on_plateau T hT κ χ hκ hχ u f hae,hbound⟩

end OQ14.Packet05TangentialPlateauBound
#print axioms OQ14.Packet05TangentialPlateauBound.tangential_plateau_original_bound
