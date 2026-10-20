import KernelReciprocity
import DynamicVolume
import LocalVolumeResponse

/-!
Bilinear reciprocity of the actual real-frequency dyadic volume response.
The Newton contribution is the full distributional Hessian, including its
source term. Compact-source electric fields and the existing weighted volume
block are covered. Reciprocal resonance normalization is outside this module.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace OQ14.NewtonReciprocity
open MeasureTheory KernelReciprocity
open scoped SchwartzMap FourierTransform InnerProductSpace
abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2

theorem hessian_even_transpose (ξ : Space) (i j : Fin 3) :
    NewtonHessian.hessianSymbol (-ξ) i j = NewtonHessian.hessianSymbol ξ j i := by
  simp only [NewtonHessian.hessianSymbol, norm_neg, PiLp.neg_apply, Complex.ofReal_neg]
  ring

theorem weakConvolution_reciprocity (f g : 𝓢(Space, ℂ)) (i j : Fin 3) :
    NewtonConvolution.weakConvolution f i j g =
      NewtonConvolution.weakConvolution g j i f := by
  rw [NewtonConvolution.weakConvolution_fourier f.integrable,
    NewtonConvolution.weakConvolution_fourier g.integrable]
  rw [← integral_neg_eq_self (fun ξ : Space => NewtonHessian.hessianSymbol ξ i j *
    𝓕 (f : Space → ℂ) ξ * ((SchwartzMap.fourierTransformCLE ℂ).symm g) ξ)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [hessian_even_transpose]
  change NewtonHessian.hessianSymbol ξ j i * 𝓕 f (-ξ) * 𝓕 g (- -ξ) =
    NewtonHessian.hessianSymbol ξ j i * 𝓕 g ξ * 𝓕 f (-ξ)
  rw [neg_neg]
  ring

theorem scalarPair_embed_right (F : FourierL2.ScalarL2) (g : 𝓢(Space, ℂ)) :
    scalarPair F (FourierL2.embed g) = ∫ x, F x * g x := by
  apply integral_congr_ae
  filter_upwards [FourierL2.embed_ae g] with x hx
  rw [hx]

theorem vectorPair_schwartz_right (F : VectorL2) (g : Fin 3 → 𝓢(Space, ℂ)) :
    vectorPair F (VectorFourier.schwartzVector g) =
      ∑ i, ∫ x, NewtonL2.physicalCoordinate F i x * g i x := by
  simp only [vectorPair, DynamicConvolution.component_apply,
    NewtonL2.physicalCoordinate_schwartz, scalarPair_embed_right]

theorem newton_schwartz_reciprocity (f g : Fin 3 → 𝓢(Space, ℂ)) :
    vectorPair (NewtonL2.newtonOperator (VectorFourier.schwartzVector f))
      (VectorFourier.schwartzVector g) =
    vectorPair (VectorFourier.schwartzVector f)
      (NewtonL2.newtonOperator (VectorFourier.schwartzVector g)) := by
  rw [vectorPair_comm (VectorFourier.schwartzVector f),
    vectorPair_schwartz_right, vectorPair_schwartz_right]
  simp_rw [NewtonL2.newtonOperator_spatial_pairing]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact weakConvolution_reciprocity (f i) (g j) j i

theorem newton_operator_reciprocity (F G : VectorL2) :
    vectorPair (NewtonL2.newtonOperator F) G = vectorPair F (NewtonL2.newtonOperator G) := by
  exact vector_operator_reciprocity_of_schwartz NewtonL2.newtonOperator
    newton_schwartz_reciprocity F G

theorem sqrtMultiplier_reciprocity (c : StaticCoefficient.Coefficient) (F G : VectorL2) :
    vectorPair (StaticCoefficient.sqrtMultiplier c F) G =
      vectorPair F (StaticCoefficient.sqrtMultiplier c G) := by
  simp only [vectorPair_actual]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  have hF := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c F)
  have hG := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c G)
  filter_upwards [hF, hG] with x hx hy
  rw [hx, hy]
  change ((Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
    F (VectorFourier.coordinateMap x) i) * G (VectorFourier.coordinateMap x) i =
    F (VectorFourier.coordinateMap x) i *
      ((Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        G (VectorFourier.coordinateMap x) i)
  ring

theorem weightedRemainder_reciprocity (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (F G : VectorL2) :
    vectorPair (DynamicVolume.weightedRemainder c k R F) G =
      vectorPair F (DynamicVolume.weightedRemainder c k R G) := by
  change vectorPair (StaticCoefficient.sqrtMultiplier c
    (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c F))) G =
    vectorPair F (StaticCoefficient.sqrtMultiplier c
      (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c G)))
  rw [sqrtMultiplier_reciprocity, dynamic_operator_reciprocity, sqrtMultiplier_reciprocity]

theorem static_volumeBlock_reciprocity (c : StaticCoefficient.Coefficient) (F G : VectorL2) :
    vectorPair (StaticNewton.volumeBlock c F) G =
      vectorPair F (StaticNewton.volumeBlock c G) := by
  change vectorPair (F - StaticCoefficient.sqrtMultiplier c
    (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c F))) G =
    vectorPair F (G - StaticCoefficient.sqrtMultiplier c
      (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier c G)))
  rw [vectorPair_sub_left, vectorPair_sub_right, sqrtMultiplier_reciprocity,
    newton_operator_reciprocity, sqrtMultiplier_reciprocity]

theorem volumeBlock_reciprocity (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (F G : VectorL2) :
    vectorPair (DynamicVolume.volumeBlock c k R F) G =
      vectorPair F (DynamicVolume.volumeBlock c k R G) := by
  change vectorPair (StaticNewton.volumeBlock c F - DynamicVolume.weightedRemainder c k R F) G =
    vectorPair F (StaticNewton.volumeBlock c G - DynamicVolume.weightedRemainder c k R G)
  rw [vectorPair_sub_left, vectorPair_sub_right,
    static_volumeBlock_reciprocity, weightedRemainder_reciprocity]

theorem localRepresentative_reciprocity (k R S : ℝ) (F G : VectorL2) :
    vectorPair (LocalVolumeResponse.localRepresentative k R S F) G =
      vectorPair F (LocalVolumeResponse.localRepresentative k R S G) := by
  change vectorPair (NewtonL2.newtonOperator F + DynamicConvolution.operator k (R+S) F) G =
    vectorPair F (NewtonL2.newtonOperator G + DynamicConvolution.operator k (R+S) G)
  rw [vectorPair_add_left, vectorPair_add_right,
    newton_operator_reciprocity, dynamic_operator_reciprocity]

theorem electric_source_product_ae (k R : ℝ) (F G : VectorL2)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hcρ : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ Metric.closedBall 0 R → σ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (i : Fin 3) :
    (fun x => FieldResponse.electric k F ρ x i * σ i x) =ᵐ[volume]
      fun x => NewtonL2.physicalCoordinate (LocalVolumeResponse.localRepresentative k R R F) i x *
        NewtonL2.physicalCoordinate G i x := by
  have he := (ae_restrict_iff' measurableSet_closedBall).mp
    (LocalVolumeResponse.electric_ae_on_ball k R R F ρ hρ hcρ hF i)
  filter_upwards [he, hG i] with x hx hg
  rw [hg]
  by_cases hb : x ∈ Metric.closedBall (0 : Space) R
  · rw [hx hb]
  · rw [hcσ i x hb]
    simp

theorem electric_source_product_integrable (k R : ℝ) (F G : VectorL2)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hcρ : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ Metric.closedBall 0 R → σ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (i : Fin 3) : Integrable (fun x => FieldResponse.electric k F ρ x i * σ i x) :=
  (scalar_product_integrable
    (NewtonL2.physicalCoordinate (LocalVolumeResponse.localRepresentative k R R F) i)
    (NewtonL2.physicalCoordinate G i)).congr
      (electric_source_product_ae k R F G ρ σ hρ hcρ hcσ hF hG i).symm

theorem electric_compact_reciprocity (k R : ℝ) (F G : VectorL2)
    (ρ σ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hσ : ∀ j, Integrable (σ j))
    (hcρ : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ Metric.closedBall 0 R → σ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) :
    (∑ i : Fin 3, ∫ x, FieldResponse.electric k F ρ x i * σ i x) =
      ∑ i : Fin 3, ∫ x, ρ i x * FieldResponse.electric k G σ x i := by
  have hp (A B : VectorL2) (a b : Fin 3 → Space → ℂ)
      (ha : ∀ j, Integrable (a j))
      (hca : ∀ j y, y ∉ Metric.closedBall 0 R → a j y = 0)
      (hcb : ∀ j y, y ∉ Metric.closedBall 0 R → b j y = 0)
      (hA : ∀ j, (NewtonL2.physicalCoordinate A j : Space → ℂ) =ᵐ[volume] a j)
      (hB : ∀ j, (NewtonL2.physicalCoordinate B j : Space → ℂ) =ᵐ[volume] b j) :
      (∑ i : Fin 3, ∫ x, FieldResponse.electric k A a x i * b i x) =
        vectorPair (LocalVolumeResponse.localRepresentative k R R A) B := by
    unfold vectorPair scalarPair
    apply Finset.sum_congr rfl
    intro i _
    exact integral_congr_ae (electric_source_product_ae k R A B a b ha hca hcb hA hB i)
  rw [hp F G ρ σ hρ hcρ hcσ hF hG,
    localRepresentative_reciprocity, vectorPair_comm,
    ← hp G F σ ρ hσ hcσ hcρ hG hF]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem compact_source_integrable (R : ℝ) (F : VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) : Integrable (ρ i) := by
  have hi : Integrable (NewtonL2.physicalCoordinate F i : Space → ℂ) := by
    apply NewtonL1L2.compact_supported_integrable _ (Metric.closedBall 0 R)
      (isCompact_closedBall 0 R)
    filter_upwards [hF i] with x hx hn
    rw [hx, hc i x hn]
  exact hi.congr (hF i)

theorem electric_compact_L2_reciprocity (k R : ℝ) (F G : VectorL2)
    (ρ σ : Fin 3 → Space → ℂ)
    (hcρ : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (hcσ : ∀ j y, y ∉ Metric.closedBall 0 R → σ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) :
    (∑ i : Fin 3, ∫ x, FieldResponse.electric k F ρ x i * σ i x) =
      ∑ i : Fin 3, ∫ x, ρ i x * FieldResponse.electric k G σ x i :=
  electric_compact_reciprocity k R F G ρ σ
    (compact_source_integrable R F ρ hcρ hF)
    (compact_source_integrable R G σ hcσ hG) hcρ hcσ hF hG

end OQ14.NewtonReciprocity





#print axioms OQ14.NewtonReciprocity.hessian_even_transpose
#print axioms OQ14.NewtonReciprocity.weakConvolution_reciprocity
#print axioms OQ14.NewtonReciprocity.scalarPair_embed_right
#print axioms OQ14.NewtonReciprocity.vectorPair_schwartz_right
#print axioms OQ14.NewtonReciprocity.newton_schwartz_reciprocity
#print axioms OQ14.NewtonReciprocity.newton_operator_reciprocity
#print axioms OQ14.NewtonReciprocity.sqrtMultiplier_reciprocity
#print axioms OQ14.NewtonReciprocity.weightedRemainder_reciprocity
#print axioms OQ14.NewtonReciprocity.static_volumeBlock_reciprocity
#print axioms OQ14.NewtonReciprocity.volumeBlock_reciprocity
#print axioms OQ14.NewtonReciprocity.localRepresentative_reciprocity
#print axioms OQ14.NewtonReciprocity.electric_source_product_ae
#print axioms OQ14.NewtonReciprocity.electric_source_product_integrable
#print axioms OQ14.NewtonReciprocity.electric_compact_reciprocity
#print axioms OQ14.NewtonReciprocity.compact_source_integrable
#print axioms OQ14.NewtonReciprocity.electric_compact_L2_reciprocity
