import KernelConvolution

/-! # Exact weak Maxwell source equation for actual compact-source convolution -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.WaveResponse

open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.KernelConvolution

theorem dyadic_source_integrable (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    Integrable (fun y => ρ y * dyadicPair k i j (translate y f)) := by
  have h0 := translated_source_integrable (GreenKernel.phi k) ρ
    (KernelIntegrability.phi_locallyIntegrable k) hρ hc f
  have h2 := translated_source_integrable (GreenKernel.phi k) ρ
    (KernelIntegrability.phi_locallyIntegrable k) hρ hc (testPartial j (testPartial i f))
  simp only [translate_partial] at h2
  convert (h0.const_mul ((k : ℂ)^2 * (if i = j then 1 else 0))).add h2 using 1
  funext y
  simp only [Pi.add_apply, dyadicPair, scalarPair]
  ring

def columnPair (k : ℝ) (ρ : Space → ℂ) (i j : Fin 3) (f : Test) : ℂ :=
  ∫ y, ρ y * dyadicPair k i j (translate y f)

/-- The source equation for one column of the actual dyadic convolution.
The displayed coordinate expression is grad div minus Laplacian minus k². -/
theorem column_maxwell_source (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    (∑ l : Fin 3, columnPair k ρ l j (testPartial l (testPartial i f))) -
      (∑ l : Fin 3, columnPair k ρ i j (testPartial l (testPartial l f))) -
        (k : ℂ)^2 * columnPair k ρ i j f =
          (k : ℂ)^2 * (if i = j then 1 else 0) * (∫ y, ρ y * f.val y) := by
  have hA (l : Fin 3) := dyadic_source_integrable k ρ hρ hc l j
    (testPartial l (testPartial i f))
  have hB (l : Fin 3) := dyadic_source_integrable k ρ hρ hc i j
    (testPartial l (testPartial l f))
  have hC := dyadic_source_integrable k ρ hρ hc i j f
  have ha := integrable_finset_sum Finset.univ (fun l _ => hA l)
  have hb := integrable_finset_sum Finset.univ (fun l _ => hB l)
  unfold columnPair
  rw [← integral_finset_sum _ (fun l _ => hA l),
    ← integral_finset_sum _ (fun l _ => hB l),
    ← integral_const_mul, ← integral_sub ha hb]
  have hab : Integrable (fun y =>
      (∑ l : Fin 3, ρ y * dyadicPair k l j (translate y (testPartial l (testPartial i f)))) -
      (∑ l : Fin 3, ρ y * dyadicPair k i j (translate y (testPartial l (testPartial l f))))) :=
    ha.sub hb
  rw [← integral_sub hab (hC.const_mul ((k : ℂ)^2)), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [← Finset.mul_sum, translate_partial]
  have h := dyadic_maxwell_source k i j (translate y f)
  have hz : (translate y f).val 0 = f.val y := by
    change f.val (0+y) = _
    rw [zero_add]
  rw [hz] at h
  linear_combination ρ y * h

/-- The complete static distribution plus the ordinary dynamic convolution
acts on the same genuine compact test, with all source integrals justified. -/
theorem column_decomposition (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (hc : HasCompactSupport ρ) (i j : Fin 3) (f : Test) :
    columnPair k ρ i j f =
      NewtonConvolution.weakConvolution ρ j i f.val +
        ∫ x, response (fun z => DyadicKernel.remainder k z i j) ρ x * f.val x := by
  have hn := NewtonConvolution.source_weak_pairing_integrable hρ j i f.val
  change Integrable (fun y => ρ y * NewtonHessian.weakHessian j i (translate y f).val) at hn
  have hd := translated_source_integrable (fun z => DyadicKernel.remainder k z i j) ρ
    (RealKernelBounds.remainder_locallyIntegrable k i j) hρ hc f
  unfold columnPair
  simp only [dyadic_decomposition, mul_add]
  rw [integral_add hn hd]
  congr 1
  rw [response_pairing _ ρ (RealKernelBounds.remainder_locallyIntegrable k i j) hρ hc f]
  apply integral_congr_ae
  filter_upwards with y
  rw [translated_pairing]

end OQ14.WaveResponse

#print axioms OQ14.WaveResponse.dyadic_source_integrable
#print axioms OQ14.WaveResponse.column_maxwell_source
#print axioms OQ14.WaveResponse.column_decomposition
