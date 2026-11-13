import Packet06ComplexConePotential
import Packet06KernelMaxwell
import ComplexInterfaceWeak
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ComplexGauss
open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource
open scoped SchwartzMap
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev V := VectorFourier.VectorL2

theorem dielectric_gauss (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    (∑ i : Fin 3, ∫ x : Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
      ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i *
        (testPartial i f).val x) = 0 := by
  have h := ComplexInterfaceWeak.displacement_divergence_zero c z hz S T hplus u hc f hf
  have he (i : Fin 3) := Packet06KernelMaxwell.kernel_displacement c z S T hST u hc hu i (testPartial i f)
  simp only [ComplexInterfaceWeak.displacementPair, ComplexInterfaceWeak.pair,
    ComplexResponseTests.testPair_integral] at h
  simpa only [he] using h
theorem electric_gauss (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    (∑ i : Fin 3, ∫ x : Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
      Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i *
        (testPartial i f).val x) = 0 := by
  have h := dielectric_gauss c z hz S T hST hplus u hc hu f hf
  have he (i : Fin 3) :
      (∫ x : Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
        Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i *
          (testPartial i f).val x) =
      ∫ x : Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
        ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i * (testPartial i f).val x := by
    have ha := Packet06ComplexElectric.electric_ae_on_ball z S T (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
      (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u) i
    have ha := (ae_restrict_iff' measurableSet_closedBall).mp ha
    apply integral_congr_ae
    filter_upwards [ha] with x hx
    by_cases hmem : x ∈ closedBall (0 : Space) T
    · change (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*_ * _ = _
      rw [← hx hmem]
      rfl
    · have hn : x ∉ tsupport (f.val : Space → ℂ) := fun hh => hmem (hf hh)
      have hz' : (testPartial i f).val x = 0 := by
        change dcoord f.val x i = 0
        simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]
      simp [hz']
  simpa only [he] using h
theorem centered_gauss (c : Coefficient) (z : ℂ) (hz : z ≠ 0) (S T : ℝ)
    (hST : S ≤ T) (hplus : 0 ≤ T+S) (u : V)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0)
    (p : ConicalStaticVolume.Data) (b : ℝ) (center : Space) (α : ℝ) (hα : α ≠ 0)
    (hball : closedBall center b ⊆ closedBall 0 T)
    (hmatch : ∀ y ∈ ball (0 : Space) b, 1+c.value (VectorFourier.coordinateMap (y+center)) =
      α * ConicalLocalGauss.epsilon p y)
    (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ i : Fin 3, ∫ y : Space, (ConicalLocalGauss.epsilon p y : ℂ)*
      Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (y+center) i * dcoord f y i) = 0 := by
  let g := NewtonConvolution.translate (-center) f
  have hgsub : tsupport (g : Space → ℂ) ⊆ closedBall center b := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hxb
    have hx0 : f (x + -center) = 0 := by
      apply image_eq_zero_of_nmem_tsupport
      intro hh
      have hm := hf hh
      apply hxb
      have hn : ‖x-center‖ < b := by simpa [sub_eq_add_neg] using hm
      simpa only [mem_closedBall,dist_eq_norm] using hn.le
    exact hx (by simpa [g, NewtonConvolution.translate_apply] using hx0)
  have hg : HasCompactSupport (g : Space → ℂ) := (isCompact_closedBall center b).of_isClosed_subset (isClosed_tsupport _) hgsub
  have h := electric_gauss c z hz S T hST hplus u hc hu ⟨g,hg⟩ (hgsub.trans hball)
  have he (i : Fin 3) : (∫ x : Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
      Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i *
        (testPartial i ⟨g,hg⟩).val x) =
      (α : ℂ) * ∫ y : Space, (ConicalLocalGauss.epsilon p y : ℂ)*
        Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) (y+center) i * dcoord f y i := by
    have ht := integral_add_right_eq_self (μ := (volume : Measure Space))
      (fun x => (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
        Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) x i *
          (testPartial i ⟨g,hg⟩).val x) center
    rw [← ht, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have hd : (testPartial i ⟨g,hg⟩).val (y+center) = dcoord f y i := by
      change GradientProjection.pderivative i g (y+center) = _
      rw [show g = NewtonConvolution.translate (-center) f from rfl, NewtonConvolution.translate_pderivative]
      simp only [NewtonConvolution.translate_apply, add_neg_cancel_right]
      rfl
    rw [hd]
    by_cases hy : y ∈ ball (0 : Space) b
    · have hm := hmatch y hy
      have hmc : (1+(c.value (VectorFourier.coordinateMap (y+center)) : ℂ)) =
          (α : ℂ) * (ConicalLocalGauss.epsilon p y : ℂ) := by exact_mod_cast hm
      rw [hmc]
      ring
    · have hn : y ∉ tsupport (f : Space → ℂ) := fun hh => hy (hf hh)
      simp [dcoord, fderiv_of_not_mem_tsupport ℝ hn]
  simp_rw [he, ← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left (Complex.ofReal_ne_zero.mpr hα)
#print axioms OQ14.Packet06ComplexGauss.dielectric_gauss
#print axioms OQ14.Packet06ComplexGauss.electric_gauss
#print axioms OQ14.Packet06ComplexGauss.centered_gauss
end OQ14.Packet06ComplexGauss
