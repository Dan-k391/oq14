import Packet05QuantitativeCutoffRepresentative
import WeakPoynting.InteriorTestDensity

/-! Cutoff commutator norms in terms of the original derivative arrays. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05QuantitativeCutoffNorms
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.MaxwellCutoffCommutator
  OQ14.Packet05QuantitativeCutoffRepresentative

theorem first_array_norm (u : L2Scalar) (D : Fin 3 → L2Scalar) (χ : Test)
    (a b : ℝ) (ha : ∀ x, ‖χ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b) (i : Fin 3) :
    ‖firstArray u D χ i‖ ≤ a*‖D i‖ + b*‖u‖ := by
  exact (norm_add_le _ _).trans (add_le_add
    (InteriorTestDensity.scaleL2_norm_le χ.function χ.regular.continuous χ.compact (D i) ha)
    (InteriorTestDensity.scaleL2_norm_le (fun x => dcoord χ.function x i)
      (partial_continuous χ.regular i) (χ.compact.fderiv_apply ℝ (basis i)) u (hb i)))

theorem second_array_norm (u : L2Scalar) (D : Fin 3 → L2Scalar) (χ : Test)
    (hχ2 : ContDiff ℝ 2 χ.function) (V : Fin 3 → Fin 3 → L2Scalar)
    (b c : ℝ) (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ c)
    (i j : Fin 3) :
    ‖secondArray u D χ hχ2 V i j‖ ≤ ‖V i j‖ + b*‖D j‖ + c*‖u‖ := by
  let dχ := derivativeCutoff χ hχ2 i
  have h1 := InteriorTestDensity.scaleL2_norm_le dχ.function dχ.regular.continuous dχ.compact (D j) (hb i)
  have h2 := InteriorTestDensity.scaleL2_norm_le (fun x => dcoord dχ.function x j)
    (partial_continuous dχ.regular j) (dχ.compact.fderiv_apply ℝ (basis j)) u (hc i j)
  change ‖V i j + (scaleL2 dχ.function dχ.regular.continuous dχ.compact (D j) +
    scaleL2 (fun x => dcoord dχ.function x j) (partial_continuous dχ.regular j)
      (dχ.compact.fderiv_apply ℝ (basis j)) u)‖ ≤ _
  have h3 := norm_add_le
    (scaleL2 dχ.function dχ.regular.continuous dχ.compact (D j))
    (scaleL2 (fun x => dcoord dχ.function x j) (partial_continuous dχ.regular j)
      (dχ.compact.fderiv_apply ℝ (basis j)) u)
  exact (norm_add_le _ _).trans (by linarith)



theorem cutoff_original_derivatives (u : L2Scalar) (D : Fin 3 → L2Scalar)
    (hD : ∀ i, HasWeakPartial u (D i) i) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (V : Fin 3 → Fin 3 → L2Scalar)
    (hV : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (D i)) (V i j) j)
    (a b c : ℝ) (ha : ∀ x, ‖χ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord χ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (derivativeCutoff χ hχ2 i).function x j‖ ≤ c) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact u x) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ OQ14.Packet05ExplicitAnisotropicBound.universalConstant *
        ((a+3*b+6*c)*‖u‖ + (a+2*b)*(∑ i : Fin 3, ‖D i‖) +
          ∑ i : Fin 2, ∑ j : Fin 3, ‖V i.castSucc j‖) := by
  obtain ⟨f,hf,hae,hbound⟩ := cutoff_tangential_sup_bound u D hD χ hχ2 V hV
  refine ⟨f,hf,hae,?_⟩
  intro x
  apply (hbound x).trans
  apply mul_le_mul_of_nonneg_left _ (by
    unfold OQ14.Packet05ExplicitAnisotropicBound.universalConstant
    positivity)
  have hu := InteriorTestDensity.scaleL2_norm_le χ.function χ.regular.continuous χ.compact u ha
  have hD0 := first_array_norm u D χ a b ha hb 0
  have hD1 := first_array_norm u D χ a b ha hb 1
  have hD2 := first_array_norm u D χ a b ha hb 2
  have hV00 := second_array_norm u D χ hχ2 V b c hb hc 0 0
  have hV01 := second_array_norm u D χ hχ2 V b c hb hc 0 1
  have hV02 := second_array_norm u D χ hχ2 V b c hb hc 0 2
  have hV10 := second_array_norm u D χ hχ2 V b c hb hc 1 0
  have hV11 := second_array_norm u D χ hχ2 V b c hb hc 1 1
  have hV12 := second_array_norm u D χ hχ2 V b c hb hc 1 2
  simp only [Fin.sum_univ_three, Fin.sum_univ_two, Fin.castSucc_zero, Fin.castSucc_one]
  linarith

end OQ14.Packet05QuantitativeCutoffNorms
#print axioms OQ14.Packet05QuantitativeCutoffNorms.first_array_norm
#print axioms OQ14.Packet05QuantitativeCutoffNorms.second_array_norm

#print axioms OQ14.Packet05QuantitativeCutoffNorms.cutoff_original_derivatives
