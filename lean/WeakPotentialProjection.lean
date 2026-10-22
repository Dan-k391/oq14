import StaticBallFourier
import HelmholtzProjection

/-! Actual weak scalar potentials and divergence-free L2 fields determine
the longitudinal projection and the static annular-source identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.WeakPotentialProjection
open MeasureTheory OQ14.Maxwell OQ14.NewtonL2
open scoped SchwartzMap ComplexConjugate InnerProductSpace

abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2

theorem weak_gradient_projection (U : ScalarL2) (E : VectorL2)
    (h : ∀ (i : Fin 3) (φ : 𝓢(Space, ℂ)),
      (∫ x, physicalCoordinate E i x*φ x)=-(∫ x, U x*GradientProjection.pderivative i φ x)) :
    VectorFourier.physicalProjection E=E := by
  have hf : ∀ᵐ ξ : Space, ∀ i : Fin 3,
      VectorFourier.fourier E (VectorFourier.coordinateMap ξ) i=
        (2*Real.pi*Complex.I)*(ξ i : ℂ)*FourierL2.fourierEquiv U ξ := by
    apply ae_all_iff.mpr
    intro i
    have hd := StaticBallFourier.weak_derivative_fourier U (physicalCoordinate E i) i (h i)
    rw [← physicalCoordinate_fourier] at hd
    filter_upwards [physicalCoordinate_ae (VectorFourier.fourier E) i,hd] with ξ hc hd
    exact hc.symm.trans hd
  have ht := (MeasurePreserving.symm VectorFourier.coordinateMap
    VectorFourier.coordinateMap_preserving).quasiMeasurePreserving.ae hf
  apply VectorFourier.fourier.injective
  rw [VectorFourier.physicalProjection_intertwine]
  apply Lp.ext
  filter_upwards [LongitudinalProjection.multiplier_ae (VectorFourier.fourier E),ht] with ξ hm ht
  have he : VectorFourier.fourier E ξ=
      ((2*Real.pi*Complex.I)*FourierL2.fourierEquiv U (VectorFourier.coordinateMap.symm ξ)) •
        LongitudinalProjection.complexify ξ := by
    apply PiLp.ext
    intro i
    have hi := ht i
    simp only [MeasurableEquiv.apply_symm_apply] at hi
    rw [hi]
    change (2*Real.pi*Complex.I)*(ξ i : ℂ)*FourierL2.fourierEquiv U (VectorFourier.coordinateMap.symm ξ)=
      ((2*Real.pi*Complex.I)*FourierL2.fourierEquiv U (VectorFourier.coordinateMap.symm ξ))*(ξ i : ℂ)
    ring
  rw [hm,he]
  exact GradientProjection.symbol_longitudinal ξ _

theorem physical_inner (F G : VectorL2) :
    ⟪F,G⟫_ℂ=∑ i : Fin 3, ⟪physicalCoordinate F i,physicalCoordinate G i⟫_ℂ := by
  rw [← VectorFourier.components_inner]
  simp only [PiLp.inner_apply,VectorFourier.components_apply,physicalCoordinate,
    LinearIsometryEquiv.inner_map_map]

theorem conjugate_partial (f : 𝓢(Space, ℂ)) (i : Fin 3) (x : Space) :
    GradientProjection.pderivative i (NewtonL2.conjugate f) x=
      conj (GradientProjection.pderivative i f x) := by
  change dcoord (NewtonL2.conjugate f) x i=conj (dcoord f x i)
  have he : (NewtonL2.conjugate f : Space → ℂ)=fun y => conj (f y) :=
    funext (NewtonL2.conjugate_apply f)
  rw [he,partial_conj f.differentiable.differentiableAt i]

theorem gradient_inner_pairing (D : VectorL2) (f : 𝓢(Space, ℂ)) :
    ⟪GradientProjection.gradient f,D⟫_ℂ=
      ∑ i : Fin 3, ∫ x, physicalCoordinate D i x*
        GradientProjection.pderivative i (NewtonL2.conjugate f) x := by
  rw [physical_inner]
  apply Finset.sum_congr rfl
  intro i _
  change ⟪physicalCoordinate (VectorFourier.schwartzVector _) i,physicalCoordinate D i⟫_ℂ=_
  rw [physicalCoordinate_schwartz,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [FourierL2.embed_ae (GradientProjection.pderivative i f)] with x hx
  rw [hx,conjugate_partial]
  rfl

theorem weak_divergence_projection (D : VectorL2)
    (h : ∀ φ : 𝓢(Space, ℂ), (∑ i : Fin 3, ∫ x,
      physicalCoordinate D i x*GradientProjection.pderivative i φ x)=0) :
    VectorFourier.physicalProjection D=0 := by
  apply (HelmholtzProjection.gradient_annihilator_iff D).mp
  intro f
  rw [gradient_inner_pairing]
  exact h (NewtonL2.conjugate f)

theorem static_forcing_identity (U : ScalarL2) (E M D : VectorL2)
    (hE : ∀ (i : Fin 3) (φ : 𝓢(Space, ℂ)),
      (∫ x, physicalCoordinate E i x*φ x)=-(∫ x, U x*GradientProjection.pderivative i φ x))
    (hD : ∀ φ : 𝓢(Space, ℂ), (∑ i : Fin 3, ∫ x,
      physicalCoordinate D i x*GradientProjection.pderivative i φ x)=0) :
    E-newtonOperator M= -newtonOperator (E+M-D) := by
  have he := weak_gradient_projection U E hE
  have hd := weak_divergence_projection D hD
  change E-(-VectorFourier.physicalProjection M)= -(-VectorFourier.physicalProjection (E+M-D))
  rw [map_sub,map_add,he,hd]
  simp only [sub_neg_eq_add,neg_neg,sub_zero]

end OQ14.WeakPotentialProjection

#print axioms OQ14.WeakPotentialProjection.weak_gradient_projection
#print axioms OQ14.WeakPotentialProjection.physical_inner
#print axioms OQ14.WeakPotentialProjection.conjugate_partial
#print axioms OQ14.WeakPotentialProjection.gradient_inner_pairing
#print axioms OQ14.WeakPotentialProjection.weak_divergence_projection
#print axioms OQ14.WeakPotentialProjection.static_forcing_identity
