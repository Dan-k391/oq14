import Packet06GenericObservedPole
import Packet06CyclicSectorConjugate
import Packet06AxialPencilTransport

/-! The actual simple observed pole survives an arbitrary axial rotation
followed by the inverse cyclic leg, in the same transported sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06CyclicAxialPencil
open Filter Metric Maxwell ModalAxialRotation Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
  Packet06PlacedKernel Packet06PlacedEquivalence Packet06GenericSectorConjugate Packet06CyclicSectorConjugate
  Packet06AxialMaterialTransport
open scoped Topology

def material (θ : ℝ) (c : StaticCoefficient.Coefficient) (s : ℝ) (a : Space) :=
  placedCoefficient 1 0 (placedCoefficient 1 0 (coefficient θ (placedCoefficient s a c)))

def embedding (θ s : ℝ) (hs : 0 < s) (a : Space) : Sector →L[ℂ] VectorL2 :=
  cy.toContinuousLinearMap.comp (cy.toContinuousLinearMap.comp
    ((Packet06AxialEquivalence.equivalence θ).toContinuousLinearMap.comp
      ((placed s hs a).toContinuousLinearMap.comp Sector.subtypeL)))

def pencil (θ : ℝ) (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    Sector →L[ℂ] Sector :=
  Packet06SectorFamily.compression (conjugate (placed s hs a) (conjugate (Packet06AxialEquivalence.equivalence θ)
    (conjugate cy (conjugate cy (ComplexConvolutionAnalytic.pencil (material θ c s a) z (R/s+‖a‖))))))

theorem pencil_eq (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    pencil θ c R s hs a z = Packet06PlacedSector.pencil c R s hs a z := by
  let L := R/s+‖a‖
  have hL : 0 ≤ L := add_nonneg (div_nonneg hR hs.le) (norm_nonneg a)
  have hp := Packet06PlacedPole.coefficient_support c R hc s hs a
  have hr : ∀ x : Space, x ∉ closedBall 0 L →
      (coefficient θ (placedCoefficient s a c)).value (VectorFourier.coordinateMap x)=0 := by
    intro x hx
    rw [Packet06AxialMaterialTransport.coefficient_value]
    apply hp
    simpa [L,mem_closedBall,dist_zero_right,(rotation (-θ)).norm_map] using hx
  unfold pencil material
  rw [cyclic_pencil_conjugate (placedCoefficient 1 0 (coefficient θ (placedCoefficient s a c))) L hL
      (one_support _ L hr) z,
    cyclic_pencil_conjugate (coefficient θ (placedCoefficient s a c)) L hL hr z,
    axial_pencil_conjugate θ (placedCoefficient s a c) L hL hp z]
  rfl

end OQ14.Packet06CyclicAxialPencil
#print axioms OQ14.Packet06CyclicAxialPencil.pencil_eq
