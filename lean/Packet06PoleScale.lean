import Packet06ModePolePersistence
import Packet06OutgoingMode

/-! Physical unit normalization preserves the same selected-sector pole and
its residue operator, while rescaling the mode appearing in its formula. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06PoleScale
open Filter Packet06SectorOperator Packet06ModePolePersistence
open Packet06MaterialSector (pencil)
open scoped Topology

theorem observed_pole_scale (c : StaticCoefficient.Coefficient) (S : ℝ) (z : ℂ)
    (u : Sector) (a : ℂ) (ha : a ≠ 0) (hp : SimpleObservedPole c S z u) :
    SimpleObservedPole c S z (a • u) := by
  obtain ⟨φ,hd,hpole⟩ := hp
  have hdscale : φ (deriv (pencil c S) z (a • u)) = a*φ (deriv (pencil c S) z u) := by
    simp only [map_smul,smul_eq_mul]
  refine ⟨φ,?_,?_⟩
  · rw [hdscale]
    exact mul_ne_zero ha hd
  · intro T hT
    obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := hpole T hT
    refine ⟨R,B,hR,hB,?_,hlim,hexp⟩
    intro x
    rw [hform,hdscale]
    change (φ x / φ (deriv (pencil c S) z u)) • Packet06LocalPencil.response c z S T u =
      (φ x / (a*φ (deriv (pencil c S) z u))) • Packet06LocalPencil.response c z S T (a • (u : VectorL2))
    rw [map_smul,smul_smul]
    congr 1
    field_simp
    ring

theorem physically_normalized_pole (c : StaticCoefficient.Coefficient) (S : ℝ) (hS : 0 ≤ S)
    (z : ℂ) (u : Sector)
    (hc : ∀ x : Maxwell.Space, x ∉ Metric.closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hne : u ≠ 0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c S z u ≠ 0)
    (hp : SimpleObservedPole c S z u) :
    ∃ a : ℂ, a ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock c z S (a • (u : VectorL2)) = 0 ∧
      Packet06PhysicalNormalization.reciprocalNorm c S z (a • (u : VectorL2)) = 1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode c z S (a • (u : VectorL2)) ∧
      SimpleObservedPole c S z (a • u) := by
  have hv : (u : VectorL2) ≠ 0 := fun h => hne (Subtype.ext h)
  obtain ⟨a,ha,hk,hunit,hmode⟩ := Packet06OutgoingMode.physically_normalized_mode c z S hS u hc hu hv hN
  exact ⟨a,ha,hk,hunit,hmode,observed_pole_scale c S z u a ha hp⟩

end OQ14.Packet06PoleScale
#print axioms OQ14.Packet06PoleScale.observed_pole_scale
#print axioms OQ14.Packet06PoleScale.physically_normalized_pole
