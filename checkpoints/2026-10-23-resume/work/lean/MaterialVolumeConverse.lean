import MaterialField
import RadiatingSourceRepresentation

/-! The actual spatial weighted equation implies the literal material volume equation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.MaterialVolumeConverse
open MeasureTheory Metric OQ14.Maxwell
open scoped SchwartzMap
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem vector_ext (F G : VectorL2)
    (h : ∀ i, (NewtonL2.physicalCoordinate F i : Space → ℂ) =ᵐ[volume] NewtonL2.physicalCoordinate G i) : F=G := by
  apply NewtonL2.vector_pairing_ext
  intro i g
  apply integral_congr_ae
  filter_upwards [h i] with x hx
  rw [hx]

theorem source_from_weighted (c : Coefficient) (u : VectorL2) (E : Field)
    (hu : ∀ i, (fun x => u (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*E x i) (i : Fin 3) :
    DynamicVolume.source c u i=ᵐ[volume] fun x => (c.value (VectorFourier.coordinateMap x) : ℂ)*E x i := by
  filter_upwards [hu i] with x hx
  have hs : (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)^2=
      (c.value (VectorFourier.coordinateMap x) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (c.nonnegative (VectorFourier.coordinateMap x))
  change (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*u (VectorFourier.coordinateMap x) i=_
  rw [hx,←mul_assoc,←pow_two,hs]

theorem response_source_congr (k : ℝ) (F : VectorL2) (ρ τ : Fin 3 → Space → ℂ)
    (h : ∀ j, ρ j=ᵐ[volume] τ j) : FieldResponse.electric k F ρ=FieldResponse.electric k F τ := by
  funext x i
  unfold FieldResponse.electric
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold KernelConvolution.response
  apply integral_congr_ae
  filter_upwards [h j] with y hy
  rw [hy]

theorem volume_equation (c : Coefficient) (k R : ℝ) (u f : VectorL2) (E I : Field)
    (hc : ∀ x : Space, x∉closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (hu : ∀ i, (fun x => u (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*E x i)
    (hf : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*I x i)
    (he : ∀ i, (fun x => MaterialField.scattered c k u x i)=ᵐ[volume] fun x => E x i-I x i) :
    DynamicVolume.volumeBlock c k R u=f := by
  apply vector_ext
  intro i
  filter_upwards [NewtonL2.physicalCoordinate_ae (DynamicVolume.volumeBlock c k R u) i,
    NewtonL2.physicalCoordinate_ae f i,DynamicVolume.volumeBlock_actual c u k R hc i,
    MaterialField.scattered_actual c k u i,hu i,hf i,he i] with x hb hp hv hs hu hf he
  rw [hb,hp,hv,←hs,hu,hf,he]
  ring

theorem inverse_solution (c : Coefficient) (k R : ℝ) (u f : VectorL2)
    (hunit : IsUnit (DynamicVolume.volumeBlock c k R)) (he : DynamicVolume.volumeBlock c k R u=f) :
    u=MaterialField.solution c k R f := by
  have h := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L u)
    (Ring.inverse_mul_cancel (DynamicVolume.volumeBlock c k R) hunit)
  change Ring.inverse (DynamicVolume.volumeBlock c k R) (DynamicVolume.volumeBlock c k R u)=u at h
  rw [he] at h
  exact h.symm

end OQ14.MaterialVolumeConverse
#print axioms OQ14.MaterialVolumeConverse.vector_ext
#print axioms OQ14.MaterialVolumeConverse.source_from_weighted
#print axioms OQ14.MaterialVolumeConverse.response_source_congr
#print axioms OQ14.MaterialVolumeConverse.volume_equation
#print axioms OQ14.MaterialVolumeConverse.inverse_solution
