import MaterialVolumeConverse

/-! Literal weighted field identities determine material L2 vectors and their combinations. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.WeightedFieldEquality
open MeasureTheory OQ14.Maxwell
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem ext (u v : VectorL2)
    (h : ∀ i : Fin 3, (fun x : Space => u (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => v (VectorFourier.coordinateMap x) i) : u=v := by
  apply MaterialVolumeConverse.vector_ext
  intro i
  exact (NewtonL2.physicalCoordinate_ae u i).trans ((h i).trans (NewtonL2.physicalCoordinate_ae v i).symm)

theorem combination (c : Coefficient) (u v w : VectorL2) (E F G : Field) (z t : ℂ)
    (hu : ∀ i, (fun x => u (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*E x i)
    (hv : ∀ i, (fun x => v (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*F x i)
    (hw : ∀ i, (fun x => w (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*G x i)
    (he : ∀ x i, E x i=z*F x i+t*G x i) : u=z • v+t • w := by
  apply ext
  intro i
  have ha := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (z • v) (t • w))
  have hz := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul z v)
  have ht := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul t w)
  filter_upwards [hu i,hv i,hw i,ha,hz,ht] with x hu hv hw ha hz ht
  rw [ha]
  simp only [Pi.add_apply]
  rw [hz,ht]
  change u (VectorFourier.coordinateMap x) i=z*v (VectorFourier.coordinateMap x) i+t*w (VectorFourier.coordinateMap x) i
  rw [hu,hv,hw,he]
  ring

end OQ14.WeightedFieldEquality
#print axioms OQ14.WeightedFieldEquality.ext
#print axioms OQ14.WeightedFieldEquality.combination
