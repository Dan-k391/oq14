import Packet05NestedTangentialRepresentative

/-! Collapse the nested tangential representative estimate to uniform
component ceilings supplied by the scalar difference-quotient iteration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05NestedTangentialUniform
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05ScalarCutoffTransfer Packet05RegionalScalarLocalization
  Packet05LocalizedTangentialGradient Packet05TangentialGradientArrays MaxwellCutoffCommutator

theorem nested_tangential_uniform (V W T : Set Space) (hV : IsOpen V) (hW : IsOpen W) (hT : IsOpen T)
    (u : L2Scalar) (C : L2Vector) (hC : ∀ j, HasWeakPartial u (C j) j)
    (i : Fin 3) (D H0 H1 : L2Vector) (hD : ∀ j, HasPartialOn V (C j) (D j) i)
    (κ ζ : RealTest univ) (hκV : tsupport κ.function ⊆ V) (hκT : ∀ x ∈ T, κ.function x = 1)
    (hζW : ∀ x ∈ W, ζ.function x = 1)
    (hH0 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) D j)) (H0 j) 0)
    (hH1 : ∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) D j)) (H1 j) 1)
    (θ : Test) (hθW : tsupport θ.function ⊆ W) (hθT : ∀ x ∈ T, θ.function x = 1)
    (hθ2 : ContDiff ℝ 2 θ.function) (a b c ak bk L P Q : ℝ)
    (ha : ∀ x, ‖θ.function x‖ ≤ a) (hb : ∀ j x, ‖dcoord θ.function x j‖ ≤ b)
    (hc : ∀ j k x, ‖dcoord (derivativeCutoff θ hθ2 j).function x k‖ ≤ c)
    (hak : ∀ x, ‖κ.complexTest.function x‖ ≤ ak)
    (hbk : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ bk)
    (hL : ‖C i‖ ≤ L) (hP : ∀ j, ‖D j‖ ≤ P)
    (hQ0 : ∀ j, ‖H0 j‖ ≤ Q) (hQ1 : ∀ j, ‖H1 j‖ ≤ Q) :
    ∃ f : Space → ℂ, Continuous f ∧ (fun x => C i x) =ᵐ[volume.restrict T] f ∧
      ∀ x, ‖f x‖ ≤ Packet05ExplicitAnisotropicBound.universalConstant *
        ((a+3*b+6*c)*ak*L+(a+2*b)*3*(ak*P+bk*L)+6*(a*Q+b*(ak*P+bk*L))) := by
  obtain ⟨f,hf,he,hbound⟩ := Packet05NestedTangentialRepresentative.nested_tangential_representative
    V W T hV hW hT u C hC i D H0 H1 hD κ ζ hκV hκT hζW hH0 hH1 θ hθW hθT hθ2 a b c ha hb hc
  refine ⟨f,hf,he,?_⟩
  intro x
  apply (hbound x).trans
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0 0)
  have hak0 : 0 ≤ ak := (norm_nonneg _).trans (hak 0)
  have hbk0 : 0 ≤ bk := (norm_nonneg _).trans (hbk 0 0)
  have hu := InteriorTestDensity.scaleL2_norm_le κ.complexTest.function κ.complexTest.regular.continuous
    κ.complexTest.compact (C i) hak
  have hu' : ‖cutScalar κ (C i)‖ ≤ ak*L := hu.trans (mul_le_mul_of_nonneg_left hL hak0)
  have hg := localized_gradient_derivatives V hV u C hC i D hD κ hκV ak bk hak hbk
  have hg' (j : Fin 3) : ‖localizedGradient κ (C i) D j‖ ≤ ak*P+bk*L :=
    (hg.2 j).trans (add_le_add (mul_le_mul_of_nonneg_left (hP j) hak0)
      (mul_le_mul_of_nonneg_left hL hbk0))
  let G := localizedGradient κ (C i) D
  let H : Fin 3 → Fin 3 → L2Scalar := ![H0,H1,0]
  have hH : ∀ j : Fin 2, ∀ k, ‖H j.castSucc k‖ ≤ Q := by
    intro j k
    fin_cases j
    · exact hQ0 k
    · exact hQ1 k
  have hM : ∀ j : Fin 2, ∀ k, ‖mixedArray θ G H j.castSucc k‖ ≤ a*Q+b*(ak*P+bk*L) := by
    intro j k
    have hm := Packet05DifferentiatedSourceBounds.cutoff_product_norm θ (G j.castSucc) (H j.castSucc k) k a b ha (hb k)
    exact hm.trans (add_le_add (mul_le_mul_of_nonneg_left (hH j k) ha0)
      (mul_le_mul_of_nonneg_left (hg' j.castSucc) hb0))
  have hsumG : (∑ j : Fin 3, ‖G j‖) ≤ 3*(ak*P+bk*L) := by
    simp only [Fin.sum_univ_three]
    linarith [hg' 0,hg' 1,hg' 2]
  have hsumM : (∑ j : Fin 2, ∑ k : Fin 3, ‖mixedArray θ G H j.castSucc k‖) ≤
      6*(a*Q+b*(ak*P+bk*L)) := by
    simp only [Fin.sum_univ_two,Fin.sum_univ_three]
    linarith [hM 0 0,hM 0 1,hM 0 2,hM 1 0,hM 1 1,hM 1 2]
  apply mul_le_mul_of_nonneg_left _ (by unfold Packet05ExplicitAnisotropicBound.universalConstant; positivity)
  have h1 := mul_le_mul_of_nonneg_left hu' (by linarith : 0 ≤ a+3*b+6*c)
  have h2 := mul_le_mul_of_nonneg_left hsumG (by linarith : 0 ≤ a+2*b)
  nlinarith only [h1,h2,hsumM]

end OQ14.Packet05NestedTangentialUniform
#print axioms OQ14.Packet05NestedTangentialUniform.nested_tangential_uniform
