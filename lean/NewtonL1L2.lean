import NewtonL2

/-!
# Actual spatial Newton response for integrable square-integrable sources

Ordinary Fourier integrals are first identified with the constructed L2
Fourier transform by testing and the fundamental lemma. This supplies the
spatial weak-convolution identity for actual L1 intersection L2 sources.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.NewtonL1L2

open MeasureTheory
open scoped SchwartzMap FourierTransform InnerProductSpace ComplexConjugate ContDiff

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2

theorem ordinary_fourier_continuous {f : Space → ℂ} (hf : Integrable f) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

/-- Agreement with the ordinary integral is proved for every genuine L1-L2
function, by actual Schwartz pairings and separation of locally integrable
functions. No Plancherel compatibility is assumed. -/
theorem fourierEquiv_ae_integral (F : ScalarL2) (hF : Integrable (F : Space → ℂ)) :
    FourierL2.fourierEquiv F =ᵐ[volume] 𝓕 (F : Space → ℂ) := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (FourierL2.fourierEquiv F)).locallyIntegrable
      (by norm_num : (1 : ENNReal) ≤ 2))
    (ordinary_fourier_continuous hF).locallyIntegrable
  intro φ hφ hc
  let ψ : 𝓢(Space, ℂ) := FourierL2.compactSmoothSchwartz (fun x => (φ x : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  have hp := NewtonL2.scalar_bilinear_parseval F (SchwartzMap.fourierTransformCLE ℂ ψ)
  rw [ContinuousLinearEquiv.symm_apply_apply] at hp
  have hf := FourierL2.fourier_mul_integral_flip (F : Space → ℂ) ψ hF ψ.integrable
  have he := hp.symm.trans hf.symm
  change (∫ ξ, FourierL2.fourierEquiv F ξ * (φ ξ : ℂ)) =
    ∫ ξ, 𝓕 (F : Space → ℂ) ξ * (φ ξ : ℂ) at he
  simpa only [Complex.real_smul, mul_comm] using he

theorem hessian_pairing_integrable (F : ScalarL2) (hF : Integrable (F : Space → ℂ))
    (g : 𝓢(Space, ℂ)) (i j : Fin 3) :
    Integrable (fun ξ => NewtonHessian.hessianSymbol ξ i j *
      𝓕 (F : Space → ℂ) ξ * ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
  have hi : Integrable (fun ξ => 𝓕 (F : Space → ℂ) ξ *
      ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
    apply (NewtonL2.scalar_pairing_integrable (FourierL2.fourierEquiv F)
      ((SchwartzMap.fourierTransformCLE ℂ).symm g)).congr
    filter_upwards [fourierEquiv_ae_integral F hF] with ξ hξ
    rw [hξ]
  have hm : Measurable (fun ξ : Space => NewtonHessian.hessianSymbol ξ i j) := by
    unfold NewtonHessian.hessianSymbol
    fun_prop
  apply hi.norm.mono' ((hm.mul (ordinary_fourier_continuous hF).measurable).mul
    ((SchwartzMap.fourierTransformCLE ℂ).symm g).continuous.measurable).aestronglyMeasurable
  filter_upwards with ξ
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) (NewtonHessian.hessianSymbol_norm_le ξ i j))
    (norm_nonneg _)

theorem vector_fourier_ae_integral (F : VectorL2)
    (hF : ∀ j, Integrable (NewtonL2.physicalCoordinate F j : Space → ℂ)) (j : Fin 3) :
    (fun ξ => VectorFourier.fourier F (VectorFourier.coordinateMap ξ) j) =ᵐ[volume]
      𝓕 (NewtonL2.physicalCoordinate F j : Space → ℂ) := by
  have h := fourierEquiv_ae_integral (NewtonL2.physicalCoordinate F j) (hF j)
  rw [← NewtonL2.physicalCoordinate_fourier] at h
  exact (NewtonL2.physicalCoordinate_ae (VectorFourier.fourier F) j).symm.trans h

theorem projected_fourier_ae (F : VectorL2)
    (hF : ∀ j, Integrable (NewtonL2.physicalCoordinate F j : Space → ℂ)) (i : Fin 3) :
    NewtonL2.physicalCoordinate (VectorFourier.fourier (VectorFourier.physicalProjection F)) i
      =ᵐ[volume] fun ξ => -(∑ j, NewtonHessian.hessianSymbol ξ i j *
        𝓕 (NewtonL2.physicalCoordinate F j : Space → ℂ) ξ) := by
  have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (NewtonHessian.physicalProjection_hessianSymbol F i)
  have hf := ae_all_iff.mpr (vector_fourier_ae_integral F hF)
  filter_upwards [NewtonL2.physicalCoordinate_ae
    (VectorFourier.fourier (VectorFourier.physicalProjection F)) i, hp, hf] with ξ hx hp hf
  rw [hx, hp, MeasurableEquiv.symm_apply_apply]
  simp only [hf]

theorem physicalProjection_spatial_pairing (F : VectorL2)
    (hF : ∀ j, Integrable (NewtonL2.physicalCoordinate F j : Space → ℂ))
    (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, NewtonL2.physicalCoordinate (VectorFourier.physicalProjection F) i x * g x) =
      -(∑ j, NewtonConvolution.weakConvolution (NewtonL2.physicalCoordinate F j) i j g) := by
  rw [NewtonL2.scalar_bilinear_parseval, ← NewtonL2.physicalCoordinate_fourier]
  calc
    _ = ∫ ξ, -(∑ j, NewtonHessian.hessianSymbol ξ i j *
        𝓕 (NewtonL2.physicalCoordinate F j : Space → ℂ) ξ *
        ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
      apply integral_congr_ae
      filter_upwards [projected_fourier_ae F hF i] with ξ hξ
      rw [hξ, neg_mul, Finset.sum_mul]
    _ = -(∑ j, ∫ ξ, NewtonHessian.hessianSymbol ξ i j *
        𝓕 (NewtonL2.physicalCoordinate F j : Space → ℂ) ξ *
        ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
      rw [integral_neg, integral_finset_sum _ (fun j _ =>
        hessian_pairing_integrable (NewtonL2.physicalCoordinate F j) (hF j) g i j)]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      exact (NewtonConvolution.weakConvolution_fourier (hF j) i j g).symm

theorem newtonOperator_spatial_pairing (F : VectorL2)
    (hF : ∀ j, Integrable (NewtonL2.physicalCoordinate F j : Space → ℂ))
    (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * g x) =
      ∑ j, NewtonConvolution.weakConvolution (NewtonL2.physicalCoordinate F j) i j g := by
  change (∫ x, NewtonL2.physicalCoordinate (-VectorFourier.physicalProjection F) i x * g x) = _
  rw [NewtonL2.physicalCoordinate_neg, NewtonL2.scalar_pairing_inner, inner_neg_right,
    ← NewtonL2.scalar_pairing_inner, physicalProjection_spatial_pairing F hF, neg_neg]

/-- Literal spatial source and response components, for every actual
integrable square-integrable vector source. The response has the already
proved operator bound one. -/
theorem newtonOperator_actual_spatial_pairing (F : VectorL2)
    (hF : ∀ j : Fin 3, Integrable (fun x : Space => F (VectorFourier.coordinateMap x) j))
    (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, NewtonL2.newtonOperator F (VectorFourier.coordinateMap x) i * g x) =
      ∑ j, ∫ y, F (VectorFourier.coordinateMap y) j *
        ∫ x, GreenKernel.phi 0 (x - y) *
          (GradientProjection.pderivative i (GradientProjection.pderivative j g)) x := by
  have hc : ∀ j, Integrable (NewtonL2.physicalCoordinate F j : Space → ℂ) :=
    fun j => (hF j).congr (NewtonL2.physicalCoordinate_ae F j).symm
  have h := newtonOperator_spatial_pairing F hc g i
  simp_rw [NewtonConvolution.weakConvolution_spatial] at h
  calc
    _ = ∫ x, NewtonL2.physicalCoordinate (NewtonL2.newtonOperator F) i x * g x := by
      apply integral_congr_ae
      filter_upwards [NewtonL2.physicalCoordinate_ae (NewtonL2.newtonOperator F) i] with x hx
      rw [hx]
    _ = _ := h.trans (by
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards [NewtonL2.physicalCoordinate_ae F j] with y hy
      rw [hy])

theorem compact_supported_integrable (F : ScalarL2) (K : Set Space) (hK : IsCompact K)
    (hF : ∀ᵐ x ∂(volume : Measure Space), x ∉ K → F x = 0) :
    Integrable (F : Space → ℂ) := by
  have hi := ((Lp.memLp F).locallyIntegrable
    (by norm_num : (1 : ENNReal) ≤ 2)).integrableOn_isCompact hK
  apply ((integrable_indicator_iff hK.measurableSet).mpr hi).congr
  filter_upwards [hF] with x hx
  by_cases h : x ∈ K
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_not_mem h, hx h]

theorem source_test_integrable {ρ : Space → ℂ} (hρ : Integrable ρ) (g : 𝓢(Space, ℂ)) :
    Integrable (fun y => ρ y * g y) := by
  have h := hρ.bdd_mul' g.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall (SchwartzMap.norm_le_seminorm ℂ g))
  simpa only [mul_comm] using h

/-- The trace of the actual weak Hessian convolution retains the exact source
term; it is the negative source distribution. -/
theorem weakConvolution_trace {ρ : Space → ℂ} (hρ : Integrable ρ) (g : 𝓢(Space, ℂ)) :
    (∑ i : Fin 3, NewtonConvolution.weakConvolution ρ i i g) = -(∫ y, ρ y * g y) := by
  unfold NewtonConvolution.weakConvolution
  rw [← integral_finset_sum _ (fun i _ =>
    NewtonConvolution.source_weak_pairing_integrable hρ i i g), ← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [← Finset.mul_sum, NewtonHessian.weakHessian_trace]
  simp only [NewtonConvolution.translate_apply, zero_add, mul_neg]

end OQ14.NewtonL1L2

#print axioms OQ14.NewtonL1L2.ordinary_fourier_continuous
#print axioms OQ14.NewtonL1L2.fourierEquiv_ae_integral
#print axioms OQ14.NewtonL1L2.hessian_pairing_integrable
#print axioms OQ14.NewtonL1L2.vector_fourier_ae_integral
#print axioms OQ14.NewtonL1L2.projected_fourier_ae
#print axioms OQ14.NewtonL1L2.physicalProjection_spatial_pairing
#print axioms OQ14.NewtonL1L2.newtonOperator_spatial_pairing
#print axioms OQ14.NewtonL1L2.newtonOperator_actual_spatial_pairing
#print axioms OQ14.NewtonL1L2.compact_supported_integrable
#print axioms OQ14.NewtonL1L2.source_test_integrable
#print axioms OQ14.NewtonL1L2.weakConvolution_trace
