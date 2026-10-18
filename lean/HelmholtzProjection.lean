import GradientProjection

/-!
# Closed-gradient-space characterization of the physical projection

The annihilator of actual Schwartz gradients is identified by testing against
inverse Fourier transforms of compact smooth functions. No closed-span
identification or distributional Fourier theorem is a premise.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.HelmholtzProjection

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate FourierTransform SchwartzMap ContDiff

abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

def spectralCoordinate (F : VectorL2) (i : Fin 3) : FourierL2.ScalarL2 :=
  VectorFourier.scalarCoordinates (VectorFourier.coordinate i (VectorFourier.fourier F))

def spectralDivergence (F : VectorL2) (ξ : Space) : ℂ :=
  ∑ i : Fin 3, (ξ i : ℂ) * spectralCoordinate F i ξ

theorem spectralDivergence_locallyIntegrable (F : VectorL2) :
    LocallyIntegrable (spectralDivergence F) (volume : Measure Space) := by
  apply locallyIntegrable_finset_sum
  intro i _
  apply locallyIntegrable_iff.mpr
  intro K hK
  apply IntegrableOn.continuousOn_mul
  · exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous).continuousOn
  · exact ((Lp.memLp (spectralCoordinate F i)).locallyIntegrable
      (by norm_num : (1 : ENNReal) ≤ 2)).integrableOn_isCompact hK
  · exact hK

theorem spectralCoordinate_gradient (f : 𝓢(Space, ℂ)) (i : Fin 3) :
    spectralCoordinate (GradientProjection.gradient f) i =
      FourierL2.embed (SchwartzMap.fourierTransformCLE ℂ (GradientProjection.pderivative i f)) := by
  unfold spectralCoordinate
  rw [VectorFourier.fourier_coordinate]
  change VectorFourier.scalarCoordinates
    (VectorFourier.scalarFourier (VectorFourier.coordinate i
      (VectorFourier.schwartzVector (fun j => GradientProjection.pderivative j f)))) = _
  rw [VectorFourier.coordinate_schwartzVector, VectorFourier.scalarFourier_embed]
  exact VectorFourier.scalarCoordinates.apply_symm_apply _

theorem spectral_inner (F G : VectorL2) :
    ⟪F, G⟫_ℂ = ∑ i : Fin 3, ⟪spectralCoordinate F i, spectralCoordinate G i⟫_ℂ := by
  rw [← VectorFourier.fourier_inner F G, ← VectorFourier.components_inner]
  simp only [PiLp.inner_apply, VectorFourier.components_apply, spectralCoordinate,
    LinearIsometryEquiv.inner_map_map]

theorem inverse_gradient_inner (ψ : 𝓢(Space, ℂ)) (F : VectorL2) :
    ⟪GradientProjection.gradient ((SchwartzMap.fourierTransformCLE ℂ).symm ψ), F⟫_ℂ =
      ∫ ξ, conj (2 * Real.pi * Complex.I : ℂ) * conj (ψ ξ) * spectralDivergence F ξ := by
  rw [spectral_inner]
  simp only [spectralCoordinate_gradient, L2.inner_def]
  rw [← integral_finset_sum _ (fun i _ => L2.integrable_inner
    (FourierL2.embed (SchwartzMap.fourierTransformCLE ℂ
      (GradientProjection.pderivative i ((SchwartzMap.fourierTransformCLE ℂ).symm ψ))))
    (spectralCoordinate F i))]
  apply integral_congr_ae
  have h : ∀ᵐ ξ ∂(volume : Measure Space), ∀ i : Fin 3,
      FourierL2.embed (SchwartzMap.fourierTransformCLE ℂ
        (GradientProjection.pderivative i ((SchwartzMap.fourierTransformCLE ℂ).symm ψ))) ξ =
        (2 * Real.pi * Complex.I) * (ξ i : ℂ) * ψ ξ := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [FourierL2.embed_ae (SchwartzMap.fourierTransformCLE ℂ
      (GradientProjection.pderivative i ((SchwartzMap.fourierTransformCLE ℂ).symm ψ)))] with ξ hξ
    rw [hξ]
    change 𝓕 (GradientProjection.pderivative i ((SchwartzMap.fourierTransformCLE ℂ).symm ψ)) ξ = _
    rw [GradientProjection.fourier_pderivative]
    have hi : 𝓕 ((SchwartzMap.fourierTransformCLE ℂ).symm ψ) ξ = ψ ξ :=
      congrArg (fun g : 𝓢(Space, ℂ) => g ξ) ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply ψ)
    rw [hi]
  filter_upwards [h] with ξ hξ
  simp only [hξ, RCLike.inner_apply, map_mul, Complex.conj_ofReal, spectralDivergence,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gradient_annihilator_spectral (F : VectorL2)
    (hF : ∀ f : 𝓢(Space, ℂ), ⟪GradientProjection.gradient f, F⟫_ℂ = 0) :
    ∀ᵐ ξ ∂(volume : Measure Space), spectralDivergence F ξ = 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (spectralDivergence_locallyIntegrable F)
  intro φ hφ hc
  let ψ : 𝓢(Space, ℂ) := FourierL2.compactSmoothSchwartz (fun ξ => (φ ξ : ℂ))
    (Complex.ofRealCLM.contDiff.comp hφ)
    (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
  have hi := hF ((SchwartzMap.fourierTransformCLE ℂ).symm ψ)
  rw [inverse_gradient_inner] at hi
  have he : (∫ ξ, conj (2 * Real.pi * Complex.I : ℂ) * conj (ψ ξ) * spectralDivergence F ξ) =
      conj (2 * Real.pi * Complex.I : ℂ) * ∫ ξ, φ ξ • spectralDivergence F ξ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    change conj (2 * Real.pi * Complex.I : ℂ) * conj (φ ξ : ℂ) * spectralDivergence F ξ = _
    simp only [Complex.conj_ofReal, Complex.real_smul, mul_assoc]
  rw [he] at hi
  have hn : conj (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact (map_ne_zero (starRingEnd ℂ)).mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)
  exact (mul_eq_zero.mp hi).resolve_left hn

theorem spectralCoordinate_ae (F : VectorL2) (i : Fin 3) :
    spectralCoordinate F i =ᵐ[volume]
      fun ξ => VectorFourier.fourier F (VectorFourier.coordinateMap ξ) i := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (VectorFourier.coordinate_ae i (VectorFourier.fourier F))
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (VectorFourier.coordinate i (VectorFourier.fourier F))
    VectorFourier.coordinateMap_preserving, h] with ξ hx hy
  exact hx.trans hy

theorem spectral_zero_projection (F : VectorL2)
    (hF : ∀ᵐ ξ ∂(volume : Measure Space), spectralDivergence F ξ = 0) :
    VectorFourier.physicalProjection F = 0 := by
  have hc : ∀ᵐ ξ ∂(volume : Measure Space), ∀ i : Fin 3,
      spectralCoordinate F i ξ = VectorFourier.fourier F (VectorFourier.coordinateMap ξ) i :=
    ae_all_iff.mpr (fun i => spectralCoordinate_ae F i)
  have hd : ∀ᵐ ξ ∂(volume : Measure Space),
      (∑ i : Fin 3, (ξ i : ℂ) * VectorFourier.fourier F (VectorFourier.coordinateMap ξ) i) = 0 := by
    filter_upwards [hc, hF] with ξ hξ hf
    simpa only [spectralDivergence, hξ] using hf
  have hp := (MeasurePreserving.symm VectorFourier.coordinateMap
    VectorFourier.coordinateMap_preserving).quasiMeasurePreserving.ae hd
  apply VectorFourier.fourier.injective
  rw [VectorFourier.physicalProjection_intertwine, map_zero]
  apply Lp.ext
  filter_upwards [LongitudinalProjection.multiplier_ae (VectorFourier.fourier F), hp,
    Lp.coeFn_zero VectorFourier.Vector 2 (volume : Measure VectorFourier.Frequency)] with ξ hm hξ hz
  have hdot : (∑ i : Fin 3, (ξ i : ℂ) * VectorFourier.fourier F ξ i) = 0 := by
    simpa only [MeasurableEquiv.apply_symm_apply] using hξ
  rw [hm, hz]
  apply PiLp.ext
  intro i
  rw [LongitudinalProjection.symbol_coordinate, hdot, zero_div, zero_mul]
  rfl

theorem gradient_annihilator_iff (F : VectorL2) :
    (∀ f : 𝓢(Space, ℂ), ⟪GradientProjection.gradient f, F⟫_ℂ = 0) ↔
      VectorFourier.physicalProjection F = 0 := by
  constructor
  · intro hF
    exact spectral_zero_projection F (gradient_annihilator_spectral F hF)
  · intro hF f
    rw [← GradientProjection.physicalProjection_gradient f,
      VectorFourier.physicalProjection_symmetric, hF, inner_zero_right]

def gradientSpan : Submodule ℂ VectorL2 :=
  Submodule.span ℂ (Set.range GradientProjection.gradient)

def closedGradients : Submodule ℂ VectorL2 := gradientSpan.topologicalClosure

theorem gradientSpan_orthogonal_iff (F : VectorL2) :
    F ∈ gradientSpanᗮ ↔ ∀ f : 𝓢(Space, ℂ), ⟪GradientProjection.gradient f, F⟫_ℂ = 0 := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro h f
    exact h _ (Submodule.subset_span ⟨f, rfl⟩)
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨f, rfl⟩ := hx; exact h f
    | zero => exact inner_zero_left F
    | add x y hx hy hxi hyi => simp only [inner_add_left, hxi, hyi, add_zero]
    | smul c x hx hxi => simp only [inner_smul_left, hxi, mul_zero]

theorem gradientSpan_orthogonal_kernel :
    gradientSpanᗮ = LinearMap.ker VectorFourier.physicalProjection.toLinearMap := by
  apply Submodule.ext
  intro F
  rw [gradientSpan_orthogonal_iff, gradient_annihilator_iff]
  rfl

theorem closedGradients_eq_kernel_orthogonal :
    closedGradients = (LinearMap.ker VectorFourier.physicalProjection.toLinearMap)ᗮ := by
  rw [closedGradients, ← Submodule.orthogonal_orthogonal_eq_closure,
    gradientSpan_orthogonal_kernel]

theorem physicalProjection_mem_closedGradients (F : VectorL2) :
    VectorFourier.physicalProjection F ∈ closedGradients := by
  rw [closedGradients_eq_kernel_orthogonal, Submodule.mem_orthogonal]
  intro u hu
  have hu0 : VectorFourier.physicalProjection u = 0 := hu
  rw [← VectorFourier.physicalProjection_symmetric, hu0, inner_zero_left]

theorem residual_mem_closedGradients_orthogonal (F : VectorL2) :
    F - VectorFourier.physicalProjection F ∈ closedGradientsᗮ := by
  rw [closedGradients_eq_kernel_orthogonal, Submodule.mem_orthogonal']
  intro u hu
  exact (Submodule.mem_orthogonal _ u).mp hu _ (by
    change VectorFourier.physicalProjection (F - VectorFourier.physicalProjection F) = 0
    rw [map_sub, VectorFourier.physicalProjection_idempotent_apply, sub_self])

instance closedGradients_complete : CompleteSpace closedGradients :=
  gradientSpan.isClosed_topologicalClosure.completeSpace_coe

theorem physicalProjection_eq_orthogonalProjection (F : VectorL2) :
    VectorFourier.physicalProjection F = (closedGradients.orthogonalProjection F : VectorL2) :=
  (Submodule.eq_orthogonalProjection_of_mem_orthogonal
    (physicalProjection_mem_closedGradients F) (residual_mem_closedGradients_orthogonal F)).symm

theorem physicalProjection_range :
    LinearMap.range VectorFourier.physicalProjection.toLinearMap = closedGradients := by
  apply le_antisymm
  · rintro F ⟨u, rfl⟩
    exact physicalProjection_mem_closedGradients u
  · intro F hF
    refine ⟨F, ?_⟩
    change VectorFourier.physicalProjection F = F
    rw [physicalProjection_eq_orthogonalProjection]
    exact Submodule.orthogonalProjection_eq_self_iff.mpr hF

theorem physicalProjection_variational_unique (F G : VectorL2)
    (hG : G ∈ closedGradients)
    (hres : ∀ f : 𝓢(Space, ℂ), ⟪GradientProjection.gradient f, F - G⟫_ℂ = 0) :
    VectorFourier.physicalProjection F = G := by
  have hz := (gradient_annihilator_iff (F - G)).mp hres
  have hg : VectorFourier.physicalProjection G = G := by
    rw [physicalProjection_eq_orthogonalProjection]
    exact Submodule.orthogonalProjection_eq_self_iff.mpr hG
  rw [map_sub, hg] at hz
  exact sub_eq_zero.mp hz

end OQ14.HelmholtzProjection

#print axioms OQ14.HelmholtzProjection.spectralDivergence_locallyIntegrable
#print axioms OQ14.HelmholtzProjection.spectralCoordinate_gradient
#print axioms OQ14.HelmholtzProjection.spectral_inner
#print axioms OQ14.HelmholtzProjection.inverse_gradient_inner
#print axioms OQ14.HelmholtzProjection.gradient_annihilator_spectral
#print axioms OQ14.HelmholtzProjection.spectralCoordinate_ae
#print axioms OQ14.HelmholtzProjection.spectral_zero_projection
#print axioms OQ14.HelmholtzProjection.gradient_annihilator_iff
#print axioms OQ14.HelmholtzProjection.gradientSpan_orthogonal_iff
#print axioms OQ14.HelmholtzProjection.gradientSpan_orthogonal_kernel
#print axioms OQ14.HelmholtzProjection.closedGradients_eq_kernel_orthogonal
#print axioms OQ14.HelmholtzProjection.physicalProjection_mem_closedGradients
#print axioms OQ14.HelmholtzProjection.residual_mem_closedGradients_orthogonal
#print axioms OQ14.HelmholtzProjection.physicalProjection_eq_orthogonalProjection
#print axioms OQ14.HelmholtzProjection.physicalProjection_range
#print axioms OQ14.HelmholtzProjection.physicalProjection_variational_unique
