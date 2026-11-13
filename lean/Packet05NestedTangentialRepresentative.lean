import Packet05LocalizedTangentialGradient

/-! A tangential scalar-gradient representative and explicit bound directly
from the nested local derivative outputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05NestedTangentialRepresentative
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05ScalarCutoffTransfer Packet05RegionalScalarLocalization
  Packet05LocalizedTangentialGradient Packet05TangentialGradientArrays MaxwellCutoffCommutator

theorem nested_tangential_representative (V W T : Set Space) (hV : IsOpen V) (hW : IsOpen W)
    (hT : IsOpen T)
    (u : L2Scalar) (C : L2Vector) (hC : ∀ j, HasWeakPartial u (C j) j)
    (i : Fin 3) (D H0 H1 : L2Vector) (hD : ∀ j, HasPartialOn V (C j) (D j) i)
    (κ ζ : RealTest univ) (hκV : tsupport κ.function ⊆ V) (hκT : ∀ x ∈ T, κ.function x = 1)
    (hζW : ∀ x ∈ W, ζ.function x = 1)
    (hH0 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) D j)) (H0 j) 0)
    (hH1 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) D j)) (H1 j) 1)
    (θ : Test) (hθW : tsupport θ.function ⊆ W) (hθT : ∀ x ∈ T, θ.function x = 1)
    (hθ2 : ContDiff ℝ 2 θ.function) (a b c : ℝ)
    (ha : ∀ x, ‖θ.function x‖ ≤ a) (hb : ∀ j x, ‖dcoord θ.function x j‖ ≤ b)
    (hc : ∀ j k x, ‖dcoord (derivativeCutoff θ hθ2 j).function x k‖ ≤ c) :
    let G := localizedGradient κ (C i) D
    let H : Fin 3 → Fin 3 → L2Scalar := ![H0,H1,0]
    let M := Packet05TangentialGradientArrays.mixedArray θ G H
    ∃ f : Space → ℂ, Continuous f ∧ (fun x => C i x) =ᵐ[volume.restrict T] f ∧
      ∀ x, ‖f x‖ ≤ Packet05ExplicitAnisotropicBound.universalConstant *
        ((a+3*b+6*c)*‖cutScalar κ (C i)‖ + (a+2*b)*(∑ j : Fin 3, ‖G j‖) +
          ∑ j : Fin 2, ∑ k : Fin 3, ‖M j.castSucc k‖) := by
  dsimp only
  let G := localizedGradient κ (C i) D
  let H : Fin 3 → Fin 3 → L2Scalar := ![H0,H1,0]
  have hκV' : tsupport κ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hκV
  have hgrad (j : Fin 3) : HasWeakPartial (cutScalar κ (C i)) (G j) j := by
    have hm : HasPartialOn V (C i) (D j) j :=
      mixed_partial_on_commute V hV u (C j) (C i) (D j) j i
        (global_partial_on V u (C j) j (hC j)) (global_partial_on V u (C i) i (hC i)) (hD j)
    exact Packet05LocalPartialProduct.local_cutoff_weak_partial V κ.complexTest.toTest hκV' (C i) (D j) j hm
  have hH : ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (cutScalar ζ (G j)) (H t j) t := by
    intro t ht j
    fin_cases t
    · exact hH0 j
    · exact hH1 j
    · exact (ht rfl).elim
  obtain ⟨hM,_⟩ := tangential_gradient_arrays W hW (cutScalar κ (C i)) G hgrad ζ hζW θ hθW H hH a b ha hb
  exact Packet05TangentialPlateauBound.tangential_plateau_original_bound T hT κ θ hκT hθT
    (C i) G hgrad hθ2 (mixedArray θ G H) hM a b c ha hb hc

end OQ14.Packet05NestedTangentialRepresentative
#print axioms OQ14.Packet05NestedTangentialRepresentative.nested_tangential_representative
