import Packet05ScalarDirectionalTangentialH2
import Packet05EnergyEnvelope

/-! The first PDE iteration controls the complete actual derivative array. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05FirstTangentialArrayBound
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakConservation
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05ScalarDirectionalUniformQuotients OQ14.Packet05ScalarDirectionalTangentialH2
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem first_tangential_array_bound
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (u D : L2Scalar) (C F : L2Vector) (JF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (S₀ : Set Space) (δ : ℝ) (hδ : 0 < δ) (i : Fin 3) (hi : i ≠ 2)
    (hJF : ∀ j, HasWeakPartial (F j) (JF j) i)
    (hD : ∀ᵐ x ∂MeasureTheory.volume, x ∈ S₀ → D x = 0)
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
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb) :
    ∃ DC : L2Vector, (∀ j, HasWeakPartial (cutScalar ζ (C j)) (DC j) i) ∧
      (∑ j : Fin 3, ‖DC j‖) ≤ 3 * Real.sqrt (uniformEnergyBound C JF d b M a ηa ηb) +
        3*ηb*(‖C 0‖+‖C 1‖+‖C 2‖) := by
  have hex (j : Fin 3) := directional_tangential_gradient_derivative g hg ζ A u D C F JF d hd hC hdiv hu hF
    S₀ δ hδ i j hi hJF hD hζS b hb M hM B hB hA a ηa ηb ha hηa hηb
  choose DC hDC using hex
  refine ⟨DC,fun j => (hDC j).1,?_⟩
  have h0 := (hDC 0).2
  have h1 := (hDC 1).2
  have h2 := (hDC 2).2
  simp only [Fin.sum_univ_three]
  linarith

end OQ14.Packet05FirstTangentialArrayBound
#print axioms OQ14.Packet05FirstTangentialArrayBound.first_tangential_array_bound
