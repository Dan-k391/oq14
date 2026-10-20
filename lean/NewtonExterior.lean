import FieldResponse

/-! # Actual Newton Hessian action away from its source

The full distributional Newton Hessian was retained in the earlier modules.
Here ordinary integration by parts is justified for compact tests whose
support avoids the source point.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.NewtonExterior

open MeasureTheory OQ14.Maxwell OQ14.GreenKernel
open scoped SchwartzMap Topology

theorem hessian_continuousAt (k : ℝ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y => phiHessian k y i j) x := by
  have hr : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hr2 : (‖x‖ : ℂ)^2 ≠ 0 := pow_ne_zero 2 hr
  have hr3 : (‖x‖ : ℂ)^3 ≠ 0 := pow_ne_zero 3 hr
  have hp : (4 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hn : ContinuousAt (fun y : Space => (‖y‖ : ℂ)) x :=
    Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt
  have hi : ContinuousAt (fun y : Space => (y i : ℂ)) x := (coordinate i).continuous.continuousAt
  have hj : ContinuousAt (fun y : Space => (y j : ℂ)) x := (coordinate j).continuous.continuousAt
  unfold phiHessian radialDD radialD
  fun_prop (disch := assumption)

theorem test_product_integrable_away (q φ : Space → ℂ)
    (hq : ∀ x, x ≠ 0 → ContinuousAt q x)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : 0 ∉ tsupport φ) :
    Integrable (fun x => q x * φ x) volume := by
  have hqK : ContinuousOn q (tsupport φ) := by
    intro x hx
    exact (hq x (by intro he; subst x; exact h0 hx)).continuousWithinAt
  have hi : IntegrableOn (fun x => q x * φ x) (tsupport φ) volume :=
    (hqK.mul hφ.continuousOn).integrableOn_compact hc
  have he : (tsupport φ).indicator (fun x => q x * φ x) = (fun x => q x * φ x) := by
    apply Set.indicator_eq_self.mpr
    intro x hx
    by_contra hn
    have hz := image_eq_zero_of_nmem_tsupport hn
    exact hx (by simp [hz])
  rw [← he]
  exact (integrable_indicator_iff hc.measurableSet).mpr hi

theorem hessian_test_integrable (k : ℝ) (i j : Fin 3) (φ : Space → ℂ)
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (h0 : 0 ∉ tsupport φ) :
    Integrable (fun x => phiHessian k x i j * φ x) volume :=
  test_product_integrable_away _ φ (hessian_continuousAt k i j) hφ hc h0

theorem hessian_weak_away (k : ℝ) (i j : Fin 3) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (h0 : 0 ∉ tsupport φ) :
    (∫ x, phiHessian k x i j * φ x) =
      ∫ x, phi k x * dcoord (fun y => dcoord φ y i) x j := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have he : (fun x => phiHessian k x i j * φ x) =ᵐ[volume]
      fun x => dcoord (fun y => phiGradient k y j) x i * φ x := by
    filter_upwards [show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx
    rw [phiGradient_partial k x hx]
  have hl := (hessian_test_integrable k i j φ hφ.continuous hc h0).congr he
  have hr := PointSingularity.test_product_integrable
    (fun x => phiGradient k x j) (fun x => dcoord φ x i)
    (KernelGradient.gradient_locallyIntegrable k j)
    (partial_continuous hφ1 i) (hc.fderiv_apply ℝ (basis i))
  have hp := PointSingularity.test_product_integrable
    (fun x => phiGradient k x j) φ (KernelGradient.gradient_locallyIntegrable k j)
    hφ.continuous hc
  have hb := PointSingularity.integration_by_parts i (fun x => phiGradient k x j) φ
    (KernelGradient.gradient_differentiableAt k j)
    (fun x _ => hφ1.differentiable le_rfl x) hl hr hp
  rw [← integral_congr_ae he] at hb
  have hf := KernelGradient.phi_weak_partial k j (fun x => dcoord φ x i)
    (KernelSource.partial_contDiff hφ i) (hc.fderiv_apply ℝ (basis i))
  linear_combination hb - hf

theorem weakHessian_away (i j : Fin 3) (f : 𝓢(Space, ℂ))
    (hc : HasCompactSupport (f : Space → ℂ)) (h0 : 0 ∉ tsupport (f : Space → ℂ)) :
    NewtonHessian.weakHessian j i f = ∫ x, phiHessian 0 x i j * f x :=
  (hessian_weak_away 0 i j f (f.smooth 2) hc h0).symm

theorem translate_avoids_origin (f : 𝓢(Space, ℂ)) (y : Space)
    (hy : y ∉ tsupport (f : Space → ℂ)) :
    0 ∉ tsupport (NewtonConvolution.translate y f : Space → ℂ) := by
  apply not_mem_tsupport_iff_eventuallyEq.mpr
  have ht : Filter.Tendsto (fun x : Space => x+y) (nhds 0) (nhds y) := by
    simpa only [zero_add] using (continuous_add_right y).continuousAt.tendsto (x := (0 : Space))
  have he := (not_mem_tsupport_iff_eventuallyEq.mp hy).comp_tendsto ht
  exact he

theorem translated_weakHessian_away (i j : Fin 3) (f : DynamicSource.Test) (y : Space)
    (hy : y ∉ tsupport (f.val : Space → ℂ)) :
    NewtonHessian.weakHessian j i (NewtonConvolution.translate y f.val) =
      ∫ x, phiHessian 0 (x-y) i j * f.val x := by
  rw [weakHessian_away i j (NewtonConvolution.translate y f.val)
    (KernelConvolution.translate y f).property (translate_avoids_origin f.val y hy)]
  exact KernelConvolution.translated_pairing (fun x => phiHessian 0 x i j) y f

end OQ14.NewtonExterior

#print axioms OQ14.NewtonExterior.hessian_continuousAt
#print axioms OQ14.NewtonExterior.test_product_integrable_away
#print axioms OQ14.NewtonExterior.hessian_test_integrable
#print axioms OQ14.NewtonExterior.hessian_weak_away
#print axioms OQ14.NewtonExterior.weakHessian_away
#print axioms OQ14.NewtonExterior.translate_avoids_origin
#print axioms OQ14.NewtonExterior.translated_weakHessian_away
