import ModalMeridionalReflection
import HalfTurnParityEquivariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalMeridionalStatic
open MeasureTheory OQ14.Maxwell OQ14.DynamicConvolution OQ14.ModalMeridionalReflection
  OQ14.HalfTurnVectorAction
open scoped FourierTransform SchwartzMap

theorem ae_reflect {p : Maxwell.Space → Prop} (h : ∀ᵐ x ∂(volume : Measure Maxwell.Space), p x) :
    ∀ᵐ x ∂(volume : Measure Maxwell.Space), p (reflection x) :=
  reflection.measurePreserving.quasiMeasurePreserving.ae h
def schwartzRot : 𝓢(FourierL2.Space, ℂ) →L[ℂ] 𝓢(FourierL2.Space, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ reflection.toContinuousLinearEquiv

theorem schwartzRot_apply (f : 𝓢(FourierL2.Space, ℂ)) (x : FourierL2.Space) : schwartzRot f x=f (reflection x) := rfl

theorem pullback_embed (f : 𝓢(FourierL2.Space, ℂ)) : pullback (FourierL2.embed f)=FourierL2.embed (schwartzRot f) := by
  apply Lp.ext
  filter_upwards [pullback_ae (FourierL2.embed f),ae_reflect (FourierL2.embed_ae f),
    FourierL2.embed_ae (schwartzRot f)] with x h1 h2 h3
  rw [h1,h2,h3,schwartzRot_apply]

theorem fourier_schwartzRot (f : 𝓢(FourierL2.Space, ℂ)) :
    SchwartzMap.fourierTransformCLE ℂ (schwartzRot f)=schwartzRot (SchwartzMap.fourierTransformCLE ℂ f) := by
  ext x
  change 𝓕 (fun y => f (reflection y)) x=𝓕 (fun y => f y) (reflection x)
  exact Real.fourierIntegral_comp_linearIsometry reflection (fun y => f y) x

/-- The scalar Fourier equivalence commutes with the half-turn pullback. -/
theorem fourierEquiv_pullback (g : FourierL2.ScalarL2) :
    FourierL2.fourierEquiv (pullback g)=pullback (FourierL2.fourierEquiv g) := by
  have hA : Continuous (fun g : FourierL2.ScalarL2 => FourierL2.fourierEquiv (pullback g)) :=
    FourierL2.fourierEquiv.continuous.comp pullback.continuous
  have hB : Continuous (fun g : FourierL2.ScalarL2 => pullback (FourierL2.fourierEquiv g)) :=
    pullback.continuous.comp FourierL2.fourierEquiv.continuous
  refine FourierL2.embed_denseRange.induction_on g (isClosed_eq hA hB) ?_
  intro f
  rw [pullback_embed,FourierL2.fourierEquiv_embed,FourierL2.fourierEquiv_embed,pullback_embed,fourier_schwartzRot]

theorem component_fourier (F : VectorFourier.VectorL2) (i : Fin 3) :
    component i (VectorFourier.fourier F)=FourierL2.fourierEquiv (component i F) := by
  change VectorFourier.scalarCoordinates (VectorFourier.coordinate i (VectorFourier.fourier F))=
    FourierL2.fourierEquiv (VectorFourier.scalarCoordinates (VectorFourier.coordinate i F))
  rw [VectorFourier.fourier_coordinate]
  simp [VectorFourier.scalarFourier]

/-- The vector Fourier transform commutes with the half-turn action. -/
theorem action_fourier (F : VectorFourier.VectorL2) :
    action (VectorFourier.fourier F)=VectorFourier.fourier (action F) := by
  apply vector_eq_of_component
  intro j
  calc component j (action (VectorFourier.fourier F))
      =(sign j : ℂ) • pullback (component j (VectorFourier.fourier F)) := component_action _ _
    _ =(sign j : ℂ) • pullback (FourierL2.fourierEquiv (component j F)) := by rw [component_fourier]
    _ =(sign j : ℂ) • FourierL2.fourierEquiv (pullback (component j F)) := by rw [fourierEquiv_pullback]
    _ =FourierL2.fourierEquiv ((sign j : ℂ) • pullback (component j F)) :=
      (map_smul FourierL2.fourierEquiv _ _).symm
    _ =FourierL2.fourierEquiv (component j (action F)) := by rw [component_action]
    _ =component j (VectorFourier.fourier (action F)) := (component_fourier _ _).symm

theorem action_fourier_symm (G : VectorFourier.VectorL2) :
    action (VectorFourier.fourier.symm G)=VectorFourier.fourier.symm (action G) := by
  apply VectorFourier.fourier.injective
  rw [LinearIsometryEquiv.apply_symm_apply,←action_fourier,LinearIsometryEquiv.apply_symm_apply]


theorem symbol_cov (ξ ξ' : LongitudinalProjection.Frequency) (hξ : ∀ l,ξ' l=sign l * ξ l)
    (z : LongitudinalProjection.Vector) (i : Fin 3) :
    (sign i : ℂ) * LongitudinalProjection.symbol ξ' z i=
      LongitudinalProjection.symbol ξ ((WithLp.equiv 2 (Fin 3 → ℂ)).symm (fun l => (sign l : ℂ) * z l)) i := by
  rw [LongitudinalProjection.symbol_coordinate,LongitudinalProjection.symbol_coordinate]
  have hden : ∑ j : Fin 3,(ξ' j : ℂ)^2=∑ j : Fin 3,(ξ j : ℂ)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hξ j]
    push_cast
    have h := sign_sq j
    calc ((sign j : ℂ)*(ξ j : ℂ))^2=((sign j : ℂ)*(sign j : ℂ))*(ξ j : ℂ)^2 := by ring
      _=_ := by rw [h,one_mul]
  have hnum : ∑ j : Fin 3,(ξ' j : ℂ)*z j=∑ j : Fin 3,(ξ j : ℂ)*((sign j : ℂ)*z j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hξ j]
    push_cast
    ring
  simp only [WithLp.equiv_symm_pi_apply]
  rw [hden,hnum,hξ i]
  push_cast
  linear_combination ((∑ j : Fin 3,(ξ j : ℂ)*((sign j : ℂ)*z j))/(∑ j : Fin 3,(ξ j : ℂ)^2)*(ξ i : ℂ))*sign_sq i

/-- The longitudinal Fourier multiplier commutes with the half-turn action. -/
theorem action_multiplier (G : VectorFourier.VectorL2) :
    action (LongitudinalProjection.multiplier G)=LongitudinalProjection.multiplier (action G) := by
  apply vector_ext_pt
  intro i
  have hM := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae G)
  have hM' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae (action G))
  have hUl : ∀ᵐ x ∂(volume : Measure FourierL2.Space),∀ l : Fin 3,
      action G (VectorFourier.coordinateMap x) l=(sign l : ℂ)*G (VectorFourier.coordinateMap (reflection x)) l :=
    ae_all_iff.mpr (fun l => ModalMeridionalReflection.action_ae G l)
  filter_upwards [ModalMeridionalReflection.action_ae (LongitudinalProjection.multiplier G) i,ae_reflect hM,hM',hUl] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  have hv : action G (VectorFourier.coordinateMap x)=
      (WithLp.equiv 2 (Fin 3 → ℂ)).symm (fun l => (sign l : ℂ)*G (VectorFourier.coordinateMap (reflection x)) l) := by
    ext l
    rw [h4 l]
    simp
  rw [hv]
  exact symbol_cov (VectorFourier.coordinateMap x) (VectorFourier.coordinateMap (reflection x))
    (fun l => reflection_coordinate x l) _ i

/-- The physical longitudinal projection commutes with the half-turn action. -/
theorem action_physicalProjection (F : VectorFourier.VectorL2) :
    action (VectorFourier.physicalProjection F)=VectorFourier.physicalProjection (action F) := by
  unfold VectorFourier.physicalProjection
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [action_fourier_symm,action_multiplier,action_fourier]


theorem source_action (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) (j : Fin 3) :
    (fun y => DynamicVolume.source (ModalWeightedMode.coefficient n hn) (action u) j y) =ᵐ[volume]
      fun y => (sign j : ℂ) * DynamicVolume.source (ModalWeightedMode.coefficient n hn) u j (reflection y) := by
  filter_upwards [ModalMeridionalReflection.action_ae u j] with y hy
  unfold DynamicVolume.source
  rw [hy, ModalMeridionalReflection.sphere_symmetric n hn y]
  ring

theorem sqrtMultiplier_comm (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) :
    action (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) u) =
      StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) (action u) := by
  apply vector_ext_pt
  intro i
  filter_upwards [ModalMeridionalReflection.action_ae (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) u) i,
    ae_reflect (sqrt_pt (ModalWeightedMode.coefficient n hn) u i),
    sqrt_pt (ModalWeightedMode.coefficient n hn) (action u) i, source_action n hn u i] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

theorem static_volume_comm (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) :
    action (StaticNewton.volumeBlock (ModalWeightedMode.coefficient n hn) u) =
      StaticNewton.volumeBlock (ModalWeightedMode.coefficient n hn) (action u) := by
  rw [StaticNewton.volumeBlock_eq]
  unfold StaticCoefficient.weightedBlock
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [sqrtMultiplier_comm n hn, action_physicalProjection, sqrtMultiplier_comm n hn]

#print axioms OQ14.ModalMeridionalStatic.static_volume_comm
#print axioms OQ14.ModalMeridionalStatic.action_physicalProjection
end OQ14.ModalMeridionalStatic


