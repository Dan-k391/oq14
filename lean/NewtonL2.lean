import NewtonConvolution

/-!
# Spatial Newton-Hessian action and its actual L2 extension

The bilinear test pairing is obtained from the actual Plancherel equivalence.
The spatial convolution identity is then used to identify its unique bounded
extension, rather than define the spatial response by a Fourier symbol.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.NewtonL2

open MeasureTheory
open scoped SchwartzMap FourierTransform InnerProductSpace ComplexConjugate

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2

def conjugate (f : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  SchwartzMap.bilinLeftCLM
    ((ContinuousLinearMap.mul ℝ ℂ).comp Complex.conjCLE.toContinuousLinearMap)
    (Function.HasTemperateGrowth.const (1 : ℂ)) f

theorem conjugate_apply (f : 𝓢(Space, ℂ)) (x : Space) :
    conjugate f x = conj (f x) := by
  change conj (f x) * 1 = _
  simp

theorem fourier_conjugate (f : 𝓢(Space, ℂ)) (ξ : Space) :
    (SchwartzMap.fourierTransformCLE ℂ (conjugate f)) ξ =
      conj (((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ) := by
  change 𝓕 (conjugate f) ξ = conj (𝓕 f (-ξ))
  have he : (conjugate f : Space → ℂ) = (fun x => conj (f x)) :=
    funext (conjugate_apply f)
  rw [he, FourierL2.fourier_conj]

theorem scalar_pairing_inner (F : ScalarL2) (f : 𝓢(Space, ℂ)) :
    (∫ x, F x * f x) = ⟪FourierL2.embed (conjugate f), F⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [FourierL2.embed_ae (conjugate f)] with x hx
  rw [hx, conjugate_apply]
  simp [mul_comm]

theorem scalar_pairing_integrable (F : ScalarL2) (f : 𝓢(Space, ℂ)) :
    Integrable (fun x => F x * f x) := by
  apply (L2.integrable_inner (FourierL2.embed (conjugate f)) F).congr
  filter_upwards [FourierL2.embed_ae (conjugate f)] with x hx
  rw [hx, conjugate_apply]
  simp [mul_comm]

theorem scalar_bilinear_parseval (F : ScalarL2) (f : 𝓢(Space, ℂ)) :
    (∫ x, F x * f x) =
      ∫ ξ, FourierL2.fourierEquiv F ξ *
        ((SchwartzMap.fourierTransformCLE ℂ).symm f) ξ := by
  rw [scalar_pairing_inner, ← FourierL2.fourierEquiv_inner,
    FourierL2.fourierEquiv_embed, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [FourierL2.embed_ae (SchwartzMap.fourierTransformCLE ℂ (conjugate f))]
    with ξ hξ
  rw [hξ, fourier_conjugate]
  simp [mul_comm]

def physicalCoordinate (F : VectorL2) (i : Fin 3) : ScalarL2 :=
  VectorFourier.scalarCoordinates (VectorFourier.coordinate i F)

theorem physicalCoordinate_ae (F : VectorL2) (i : Fin 3) :
    physicalCoordinate F i =ᵐ[volume]
      fun x => F (VectorFourier.coordinateMap x) i := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (VectorFourier.coordinate_ae i F)
  filter_upwards [Lp.coeFn_compMeasurePreserving (VectorFourier.coordinate i F)
    VectorFourier.coordinateMap_preserving, h] with x hx hy
  exact hx.trans hy

theorem physicalCoordinate_schwartz (f : Fin 3 → 𝓢(Space, ℂ)) (i : Fin 3) :
    physicalCoordinate (VectorFourier.schwartzVector f) i = FourierL2.embed (f i) := by
  unfold physicalCoordinate
  rw [VectorFourier.coordinate_schwartzVector]
  exact VectorFourier.scalarCoordinates.apply_symm_apply _

theorem physicalCoordinate_fourier (F : VectorL2) (i : Fin 3) :
    physicalCoordinate (VectorFourier.fourier F) i =
      FourierL2.fourierEquiv (physicalCoordinate F i) := by
  unfold physicalCoordinate
  rw [VectorFourier.fourier_coordinate]
  simp only [VectorFourier.scalarFourier, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem schwartz_fourier_hessian_integrable (f g : 𝓢(Space, ℂ)) (i j : Fin 3) :
    Integrable (fun ξ => NewtonHessian.hessianSymbol ξ i j * 𝓕 f ξ *
      ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
  have hi : Integrable (fun ξ => 𝓕 f ξ *
      ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
    apply (scalar_pairing_integrable
      (FourierL2.embed (SchwartzMap.fourierTransformCLE ℂ f))
      ((SchwartzMap.fourierTransformCLE ℂ).symm g)).congr
    filter_upwards [FourierL2.embed_ae (SchwartzMap.fourierTransformCLE ℂ f)] with ξ hξ
    rw [hξ]
    rfl
  have hm : Measurable (fun ξ : Space => NewtonHessian.hessianSymbol ξ i j) := by
    unfold NewtonHessian.hessianSymbol
    fun_prop
  apply hi.norm.mono' ((hm.mul
    (SchwartzMap.fourierTransformCLE ℂ f).continuous.measurable).mul
    ((SchwartzMap.fourierTransformCLE ℂ).symm g).continuous.measurable).aestronglyMeasurable
  filter_upwards with ξ
  simp only [norm_mul]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _) (NewtonHessian.hessianSymbol_norm_le ξ i j))
    (norm_nonneg _)

theorem projected_schwartz_fourier_ae (f : Fin 3 → 𝓢(Space, ℂ)) (i : Fin 3) :
    physicalCoordinate
      (VectorFourier.fourier (VectorFourier.physicalProjection (VectorFourier.schwartzVector f))) i
      =ᵐ[volume] fun ξ => -(∑ j, NewtonHessian.hessianSymbol ξ i j * 𝓕 (f j) ξ) := by
  have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (NewtonHessian.physicalProjection_hessianSymbol (VectorFourier.schwartzVector f) i)
  have hf : ∀ᵐ ξ ∂(volume : Measure Space), ∀ j : Fin 3,
      VectorFourier.fourier (VectorFourier.schwartzVector f) (VectorFourier.coordinateMap ξ) j =
        𝓕 (f j) ξ := by
    apply ae_all_iff.mpr
    intro j
    have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (VectorFourier.fourier_ae_integral f j)
    simpa only [MeasurableEquiv.symm_apply_apply] using h
  filter_upwards [physicalCoordinate_ae
    (VectorFourier.fourier (VectorFourier.physicalProjection (VectorFourier.schwartzVector f))) i,
    hp, hf] with ξ hx hp hf
  rw [hx, hp, MeasurableEquiv.symm_apply_apply]
  simp only [hf]

/-- Each physical component of the actual projection has the spatial
Newton-Hessian test action, with its required negative sign. -/
theorem physicalProjection_spatial_pairing
    (f : Fin 3 → 𝓢(Space, ℂ)) (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, physicalCoordinate
      (VectorFourier.physicalProjection (VectorFourier.schwartzVector f)) i x * g x) =
        -(∑ j, NewtonConvolution.weakConvolution (f j) i j g) := by
  rw [scalar_bilinear_parseval, ← physicalCoordinate_fourier]
  calc
    _ = ∫ ξ, -(∑ j, NewtonHessian.hessianSymbol ξ i j * 𝓕 (f j) ξ *
        ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
      apply integral_congr_ae
      filter_upwards [projected_schwartz_fourier_ae f i] with ξ hξ
      rw [hξ, neg_mul, Finset.sum_mul]
    _ = -(∑ j, ∫ ξ, NewtonHessian.hessianSymbol ξ i j * 𝓕 (f j) ξ *
        ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ) := by
      rw [integral_neg, integral_finset_sum _ (fun j _ =>
        schwartz_fourier_hessian_integrable (f j) g i j)]
    _ = _ := by
      simp_rw [NewtonConvolution.weakConvolution_fourier (SchwartzMap.integrable _)]

theorem physicalProjection_actual_spatial_pairing
    (f : Fin 3 → 𝓢(Space, ℂ)) (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, VectorFourier.physicalProjection (VectorFourier.schwartzVector f)
      (VectorFourier.coordinateMap x) i * g x) =
        -(∑ j, ∫ y, f j y * ∫ x, GreenKernel.phi 0 (x - y) *
          (GradientProjection.pderivative i (GradientProjection.pderivative j g)) x) := by
  have h := physicalProjection_spatial_pairing f g i
  simp_rw [NewtonConvolution.weakConvolution_spatial] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [physicalCoordinate_ae
    (VectorFourier.physicalProjection (VectorFourier.schwartzVector f)) i] with x hx
  rw [hx]

theorem scalar_pairing_ext (F G : ScalarL2)
    (h : ∀ f : 𝓢(Space, ℂ), (∫ x, F x * f x) = ∫ x, G x * f x) : F = G := by
  apply ext_inner_left ℂ
  intro v
  refine FourierL2.embed_denseRange.induction_on v
    (isClosed_eq (continuous_id.inner continuous_const)
      (continuous_id.inner continuous_const)) ?_
  intro f
  have hf : conjugate (conjugate f) = f := by
    ext x
    simp only [conjugate_apply, starRingEnd_self_apply]
  have hi := h (conjugate f)
  rw [scalar_pairing_inner, scalar_pairing_inner, hf] at hi
  exact hi

theorem scalarEmbed_denseRange : DenseRange VectorFourier.scalarEmbed :=
  VectorFourier.scalarCoordinates.symm.surjective.denseRange.comp
    FourierL2.embed_denseRange VectorFourier.scalarCoordinates.symm.continuous

theorem schwartzVector_denseRange : DenseRange VectorFourier.schwartzVector := by
  have hp := DenseRange.piMap (fun _ : Fin 3 => scalarEmbed_denseRange)
  have hq := (PiLp.continuousLinearEquiv (𝕜 := ℂ) (p := 2)
    (β := fun _ : Fin 3 => VectorFourier.ScalarL2)).symm.surjective.denseRange.comp hp
      (PiLp.continuousLinearEquiv (𝕜 := ℂ) (p := 2)
        (β := fun _ : Fin 3 => VectorFourier.ScalarL2)).symm.continuous
  exact VectorFourier.components.symm.surjective.denseRange.comp hq
    VectorFourier.components.symm.continuous

theorem vector_pairing_ext (F G : VectorL2)
    (h : ∀ (i : Fin 3) (g : 𝓢(Space, ℂ)),
      (∫ x, physicalCoordinate F i x * g x) =
        ∫ x, physicalCoordinate G i x * g x) : F = G := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro i
  change VectorFourier.coordinate i F = VectorFourier.coordinate i G
  apply VectorFourier.scalarCoordinates.injective
  exact scalar_pairing_ext (physicalCoordinate F i) (physicalCoordinate G i) (h i)

theorem physicalCoordinate_neg (F : VectorL2) (i : Fin 3) :
    physicalCoordinate (-F) i = -physicalCoordinate F i := by
  simp only [physicalCoordinate, map_neg]

/-- The bounded extension of the actual full distributional Newton-Hessian
matrix convolution. Its identification is certified by the spatial pairing
and uniqueness theorems below. -/
def newtonOperator : VectorL2 →L[ℂ] VectorL2 :=
  -VectorFourier.physicalProjection

theorem newtonOperator_norm_le : ‖newtonOperator‖ ≤ 1 := by
  simpa only [newtonOperator, norm_neg] using VectorFourier.physicalProjection_norm_le

theorem newtonOperator_spatial_pairing
    (f : Fin 3 → 𝓢(Space, ℂ)) (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, physicalCoordinate (newtonOperator (VectorFourier.schwartzVector f)) i x * g x) =
      ∑ j, NewtonConvolution.weakConvolution (f j) i j g := by
  change (∫ x, physicalCoordinate
    (-VectorFourier.physicalProjection (VectorFourier.schwartzVector f)) i x * g x) = _
  rw [physicalCoordinate_neg, scalar_pairing_inner, inner_neg_right,
    ← scalar_pairing_inner, physicalProjection_spatial_pairing, neg_neg]

theorem newtonOperator_actual_spatial_pairing
    (f : Fin 3 → 𝓢(Space, ℂ)) (g : 𝓢(Space, ℂ)) (i : Fin 3) :
    (∫ x, newtonOperator (VectorFourier.schwartzVector f)
      (VectorFourier.coordinateMap x) i * g x) =
        ∑ j, ∫ y, f j y * ∫ x, GreenKernel.phi 0 (x - y) *
          (GradientProjection.pderivative i (GradientProjection.pderivative j g)) x := by
  have h := newtonOperator_spatial_pairing f g i
  simp_rw [NewtonConvolution.weakConvolution_spatial] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [physicalCoordinate_ae
    (newtonOperator (VectorFourier.schwartzVector f)) i] with x hx
  rw [hx]

/-- The spatial test action on genuine Schwartz sources uniquely determines a
bounded operator on all vector L2; density is proved, not a premise. -/
theorem newtonOperator_unique (U : VectorL2 →L[ℂ] VectorL2)
    (hU : ∀ (f : Fin 3 → 𝓢(Space, ℂ)) (g : 𝓢(Space, ℂ)) (i : Fin 3),
      (∫ x, physicalCoordinate (U (VectorFourier.schwartzVector f)) i x * g x) =
        ∑ j, NewtonConvolution.weakConvolution (f j) i j g) :
    U = newtonOperator := by
  apply ContinuousLinearMap.ext
  intro F
  refine schwartzVector_denseRange.induction_on F
    (isClosed_eq U.continuous newtonOperator.continuous) ?_
  intro f
  apply vector_pairing_ext
  intro i g
  rw [hU, newtonOperator_spatial_pairing]

end OQ14.NewtonL2

#print axioms OQ14.NewtonL2.conjugate_apply
#print axioms OQ14.NewtonL2.fourier_conjugate
#print axioms OQ14.NewtonL2.scalar_pairing_inner
#print axioms OQ14.NewtonL2.scalar_pairing_integrable
#print axioms OQ14.NewtonL2.scalar_bilinear_parseval
#print axioms OQ14.NewtonL2.physicalCoordinate_ae
#print axioms OQ14.NewtonL2.physicalCoordinate_schwartz
#print axioms OQ14.NewtonL2.physicalCoordinate_fourier
#print axioms OQ14.NewtonL2.schwartz_fourier_hessian_integrable
#print axioms OQ14.NewtonL2.projected_schwartz_fourier_ae
#print axioms OQ14.NewtonL2.physicalProjection_spatial_pairing
#print axioms OQ14.NewtonL2.physicalProjection_actual_spatial_pairing
#print axioms OQ14.NewtonL2.scalar_pairing_ext
#print axioms OQ14.NewtonL2.scalarEmbed_denseRange
#print axioms OQ14.NewtonL2.schwartzVector_denseRange
#print axioms OQ14.NewtonL2.vector_pairing_ext
#print axioms OQ14.NewtonL2.physicalCoordinate_neg
#print axioms OQ14.NewtonL2.newtonOperator_norm_le
#print axioms OQ14.NewtonL2.newtonOperator_spatial_pairing
#print axioms OQ14.NewtonL2.newtonOperator_actual_spatial_pairing
#print axioms OQ14.NewtonL2.newtonOperator_unique
