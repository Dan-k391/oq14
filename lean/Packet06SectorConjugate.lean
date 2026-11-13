import Packet06ExternalCanonical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06SectorConjugate
open MeasureTheory KernelReciprocity
open scoped ComplexConjugate InnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2
abbrev ScalarL2 := FourierL2.ScalarL2

def conjugate (F : VectorL2) : VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i (scalarConjugate (DynamicConvolution.component i F))

theorem component_conjugate (F : VectorL2) (i : Fin 3) :
    DynamicConvolution.component i (conjugate F) = scalarConjugate (DynamicConvolution.component i F) := by
  simp only [conjugate,map_sum,DynamicConvolution.component_insert]
  simp

theorem vectorPair_inner (F G : VectorL2) :
    vectorPair F G = ⟪conjugate G,F⟫_ℂ := by
  rw [← VectorFourier.components_inner]
  simp only [PiLp.inner_apply, VectorFourier.components_apply]
  unfold vectorPair
  apply Finset.sum_congr rfl
  intro i hi
  rw [scalarPair_comm,scalarPair_inner]
  change ⟪scalarConjugate (DynamicConvolution.component i G), DynamicConvolution.component i F⟫_ℂ = _
  rw [← component_conjugate G i]
  change ⟪VectorFourier.scalarCoordinates (VectorFourier.coordinate i (conjugate G)),
    VectorFourier.scalarCoordinates (VectorFourier.coordinate i F)⟫_ℂ = _
  exact VectorFourier.scalarCoordinates.inner_map_map _ _

theorem conjugate_ae (F : VectorL2) (i : Fin 3) :
    (fun x : Maxwell.Space => conjugate F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => conj (F (VectorFourier.coordinateMap x) i) := by
  have h1 := (NewtonL2.physicalCoordinate_ae (conjugate F) i).symm
  have h2 := scalarConjugate_ae (DynamicConvolution.component i F)
  have h3 := NewtonL2.physicalCoordinate_ae F i
  change (fun x : Maxwell.Space => conjugate F (VectorFourier.coordinateMap x) i) =ᵐ[volume] _
  filter_upwards [h1,h2,h3] with x h1 h2 h3
  change conjugate F (VectorFourier.coordinateMap x) i = _
  rw [h1]
  change (DynamicConvolution.component i (conjugate F)) x = _
  rw [component_conjugate,h2]
  change (DynamicConvolution.component i F) x = _ at h3
  rw [h3]

theorem conjugate_rotation (θ : ℝ) (F : VectorL2) :
    conjugate (ModalAxialRotation.action θ F) = ModalAxialRotation.action θ (conjugate F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hrs := ae_all_iff.mpr (fun j => (ModalAxialRotation.rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
    (conjugate_ae F j))
  filter_upwards [conjugate_ae (ModalAxialRotation.action θ F) i,
    ModalAxialRotation.action_ae θ F i,ModalAxialRotation.action_ae θ (conjugate F) i,hrs] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  simp only [map_sum,map_mul,h4]
  apply Finset.sum_congr rfl
  intro j hj
  have hm : conj (ModalAxialRotation.matrix θ i j) = ModalAxialRotation.matrix θ i j := by
    fin_cases i <;> fin_cases j <;> simp [ModalAxialRotation.matrix, -Complex.ofReal_cos, -Complex.ofReal_sin]
  rw [hm]

theorem conjugate_reflection (F : VectorL2) :
    conjugate (ModalMeridionalReflection.action F) = ModalMeridionalReflection.action (conjugate F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hr := ModalMeridionalReflection.reflection.measurePreserving.quasiMeasurePreserving.ae (conjugate_ae F i)
  filter_upwards [conjugate_ae (ModalMeridionalReflection.action F) i,
    ModalMeridionalReflection.action_ae F i,ModalMeridionalReflection.action_ae (conjugate F) i,hr] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]
  simp
theorem conjugate_mem_sector (F : VectorL2) (hF : F ∈ Packet06SectorOperator.Sector) :
    conjugate F ∈ Packet06SectorOperator.Sector := by
  refine ⟨?_,?_⟩
  · change conjugate F ∈ ModalAxialRotation.axialSector
    have hax : F ∈ ModalAxialRotation.axialSector := hF.1
    simp only [ModalAxialRotation.axialSector, Submodule.mem_iInf, LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at hax ⊢
    intro θ
    rw [← conjugate_rotation, hax θ]
  · have hr : ModalMeridionalReflection.action F = F := by
      have h := hF.2
      change (ModalMeridionalReflection.action - 1) F = 0 at h
      simpa using sub_eq_zero.mp h
    change (ModalMeridionalReflection.action - 1) (conjugate F) = 0
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero]
    rw [← conjugate_reflection,hr]

/-- The actual orthogonal sector projection is self-transpose for the
physical unconjugated volume pairing. -/
theorem projection_pair_right (F G : VectorL2) (hG : G ∈ Packet06SectorOperator.Sector) :
    vectorPair (Packet06SectorOperator.Sector.orthogonalProjection F : VectorL2) G = vectorPair F G := by
  rw [vectorPair_inner,vectorPair_inner]
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left (K := Packet06SectorOperator.Sector)
    (⟨conjugate G,conjugate_mem_sector G hG⟩ : Packet06SectorOperator.Sector) F
#print axioms OQ14.Packet06SectorConjugate.conjugate_mem_sector
#print axioms OQ14.Packet06SectorConjugate.projection_pair_right
#print axioms OQ14.Packet06SectorConjugate.conjugate_ae
#print axioms OQ14.Packet06SectorConjugate.conjugate_rotation
#print axioms OQ14.Packet06SectorConjugate.conjugate_reflection
#print axioms OQ14.Packet06SectorConjugate.component_conjugate
#print axioms OQ14.Packet06SectorConjugate.vectorPair_inner
end OQ14.Packet06SectorConjugate
