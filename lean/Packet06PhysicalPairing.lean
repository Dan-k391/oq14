import ComplexVolumeReciprocity

/-! Exact coefficient-one dictionary between the source pairing and the
physical unconjugated volume integral. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06PhysicalPairing
open MeasureTheory KernelReciprocity

theorem component_product_integrable (F G : VectorFourier.VectorL2) (i : Fin 3) :
    Integrable (fun x : Maxwell.Space =>
      F (VectorFourier.coordinateMap x) i * G (VectorFourier.coordinateMap x) i) := by
  apply (scalar_product_integrable (DynamicConvolution.component i F)
    (DynamicConvolution.component i G)).congr
  filter_upwards [NewtonL2.physicalCoordinate_ae F i,NewtonL2.physicalCoordinate_ae G i] with x hf hg
  simp only [DynamicConvolution.component_apply,hf,hg]

theorem physical_product_integrable (F G : VectorFourier.VectorL2) :
    Integrable (fun x : Maxwell.Space => ∑ i : Fin 3,
      F (VectorFourier.coordinateMap x) i * G (VectorFourier.coordinateMap x) i) :=
  integrable_finset_sum _ (fun i _ => component_product_integrable F G i)

theorem vectorPair_physical (F G : VectorFourier.VectorL2) :
    KernelReciprocity.vectorPair F G = ∫ x : Maxwell.Space, ∑ i : Fin 3,
      F (VectorFourier.coordinateMap x) i * G (VectorFourier.coordinateMap x) i := by
  unfold vectorPair scalarPair
  rw [integral_finset_sum _ (fun i _ => component_product_integrable F G i)]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [NewtonL2.physicalCoordinate_ae F i,NewtonL2.physicalCoordinate_ae G i] with x hf hg
  simp only [DynamicConvolution.component_apply,hf,hg]

end OQ14.Packet06PhysicalPairing
#print axioms OQ14.Packet06PhysicalPairing.component_product_integrable
#print axioms OQ14.Packet06PhysicalPairing.physical_product_integrable
#print axioms OQ14.Packet06PhysicalPairing.vectorPair_physical
