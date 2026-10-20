import DynamicSource
import NewtonConvolution

/-! # Actual compact-source convolution pairings for locally integrable kernels -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.KernelConvolution

open MeasureTheory Metric OQ14.Maxwell
open scoped SchwartzMap

/-- Compact source and test supports turn a locally integrable kernel into
an absolutely integrable two-variable pairing. -/
theorem product_integrable (q ρ : Space → ℂ) (hq : LocallyIntegrable q)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ)
    (f : DynamicSource.Test) :
    Integrable (fun p : Space × Space => ρ p.2 * q (p.1-p.2) * f.val p.1)
      (volume.prod volume) := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : Space)
  obtain ⟨S, hS⟩ := f.property.isBounded.subset_closedBall (0 : Space)
  let Q : Space → ℂ := (closedBall 0 (R+S)).indicator q
  have hQ : Integrable Q :=
    (integrable_indicator_iff isClosed_closedBall.measurableSet).mpr
      (hq.integrableOn_isCompact (isCompact_closedBall 0 (R+S)))
  have hi := hρ.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hQ
  have hb := hi.bdd_mul'
    (f.val.continuous.comp continuous_fst).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p : Space × Space =>
      SchwartzMap.norm_le_seminorm ℂ f.val p.1))
  apply hb.congr
  filter_upwards with p
  change f.val p.1 * (ρ p.2 * Q (p.1-p.2)) = _
  by_cases hr : ρ p.2 = 0
  · simp [hr]
  by_cases hf : f.val p.1 = 0
  · simp [hf]
  have hpR := hR (subset_tsupport ρ hr)
  have hpS := hS (subset_tsupport (f.val : Space → ℂ) hf)
  have hp : p.1-p.2 ∈ closedBall (0 : Space) (R+S) := by
    simp only [mem_closedBall, dist_zero_right] at hpR hpS ⊢
    exact (norm_sub_le _ _).trans (by linarith)
  simp only [Q, Set.indicator_of_mem hp]
  ring

theorem source_pairing_integrable (q ρ : Space → ℂ) (hq : LocallyIntegrable q)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : DynamicSource.Test) :
    Integrable (fun y => ρ y * ∫ x, q (x-y) * f.val x) := by
  apply (product_integrable q ρ hq hρ hc f).swap.integral_prod_left.congr
  filter_upwards with y
  simp only [Function.comp_def, Prod.swap_prod_mk]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

def response (q ρ : Space → ℂ) (x : Space) : ℂ :=
  ∫ y, ρ y * q (x-y)

theorem response_pairing (q ρ : Space → ℂ) (hq : LocallyIntegrable q)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : DynamicSource.Test) :
    (∫ x, response q ρ x * f.val x) =
      ∫ y, ρ y * ∫ x, q (x-y) * f.val x := by
  simp only [response, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (product_integrable q ρ hq hρ hc f)]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  ring

def translate (y : Space) (f : DynamicSource.Test) : DynamicSource.Test :=
  ⟨NewtonConvolution.translate y f.val, f.property.comp_homeomorph (Homeomorph.addRight y)⟩

theorem translate_partial (y : Space) (i : Fin 3) (f : DynamicSource.Test) :
    translate y (DynamicSource.testPartial i f) =
      DynamicSource.testPartial i (translate y f) := by
  apply Subtype.ext
  exact (NewtonConvolution.translate_pderivative y i f.val).symm

theorem translated_pairing (q : Space → ℂ) (y : Space) (f : DynamicSource.Test) :
    (∫ x, q x * (translate y f).val x) = ∫ x, q (x-y) * f.val x := by
  have h := integral_add_right_eq_self (μ := (volume : Measure Space))
    (fun x : Space => q (x-y) * f.val x) y
  simpa only [translate, NewtonConvolution.translate_apply, add_sub_cancel_right] using h

theorem translated_source_integrable (q ρ : Space → ℂ) (hq : LocallyIntegrable q)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (f : DynamicSource.Test) :
    Integrable (fun y => ρ y * ∫ x, q x * (translate y f).val x) := by
  simp only [translated_pairing]
  exact source_pairing_integrable q ρ hq hρ hc f

end OQ14.KernelConvolution

#print axioms OQ14.KernelConvolution.product_integrable
#print axioms OQ14.KernelConvolution.source_pairing_integrable
#print axioms OQ14.KernelConvolution.response_pairing
#print axioms OQ14.KernelConvolution.translate_partial
#print axioms OQ14.KernelConvolution.translated_pairing
#print axioms OQ14.KernelConvolution.translated_source_integrable
