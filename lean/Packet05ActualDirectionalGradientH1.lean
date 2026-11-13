import Packet05TangentialGradientH1
import Packet05ScalarDirectionalTangentialH2

/-! Actual H¹ regularity of a localized tangential scalar-gradient component,
derived from the variable-coefficient transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05ActualDirectionalGradientH1
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05ScalarDirectionalTangentialH2 OQ14.Packet05TangentialGradientH1
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_directional_gradient_h1
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (u D : L2Scalar) (C F JF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (S₀ : Set Space) (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) (hi : i ≠ 2)
    (hJF : ∀ j, HasWeakPartial (F j) (JF j) i)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (hζS : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (hA : ∀ x ∈ tsupport ζ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a ηa ηb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hηa : ∀ x, ‖ζ.complexTest.function x‖ ≤ ηa)
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb)
    (V : Set Space) (hV : IsOpen V) (hζ : ∀ x ∈ V, ζ.function x = 1)
    (χ : Test) (hχ : tsupport χ.function ⊆ V) :
    ∃ DU : Fin 3 → L2Scalar, ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (C i)) (DU j) j := by
  have hDer (j : Fin 3) : ∃ v : L2Scalar, HasWeakPartial
      (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact (C j)) v i := by
    obtain ⟨v,hv,_⟩ := directional_tangential_gradient_derivative g hg ζ A u D C F JF d hd hC hdiv hu hF S₀ δ hδ i j hi hJF hD hζS b hb M hM B hB hA a ηa ηb ha hηa hηb
    exact ⟨v,hv⟩
  have hζ' : ∀ x ∈ V, ζ.complexTest.function x = 1 := by
    intro x hx
    simp [RealTest.complexTest, hζ x hx]
  exact localized_tangential_gradient_h1 V hV u C hC ζ.complexTest.toTest χ hζ' hχ i hDer

end OQ14.Packet05ActualDirectionalGradientH1
#print axioms OQ14.Packet05ActualDirectionalGradientH1.actual_directional_gradient_h1
