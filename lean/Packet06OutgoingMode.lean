import Packet06PhysicalMode
import Packet06ComplexAffine
import Packet06PhysicalScale

/-! One actual outgoing, locally L² Maxwell mode, with true physical reciprocal
unit normalization obtained by a nonzero scaling of its material kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06OutgoingMode
open MeasureTheory Metric Filter DynamicSource Packet06GlobalField
open StaticCoefficient (Coefficient)
open scoped Topology

structure IsActualOutgoingMode (c : Coefficient) (z : ℂ) (S : ℝ) (u : V) : Prop where
  nonzero : ¬ ∀ i : Fin 3, (fun x : Maxwell.Space => electric c z S u x i) =ᵐ[volume] 0
  electric_L2 : ∀ T : ℝ, ∀ i : Fin 3,
    MemLp (fun x => electric c z S u x i) 2 (volume.restrict (closedBall 0 T))
  magnetic_L2 : ∀ T : ℝ, ∀ i : Fin 3,
    MemLp (fun x => ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i)
      2 (volume.restrict (closedBall 0 T))
  maxwell : Packet06ComplexAffine.TestMaxwellC z (MaterialMaxwell.dielectric c)
    (electric c z S u) (ComplexMagneticLocal.magnetic z (DynamicVolume.source c u))
  electric_far : ∀ n : Maxwell.Space, ‖n‖ = 1 → ∀ i : Fin 3,
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-Complex.I*z*r)*electric c z S u (r • n) i)
      atTop (𝓝 (ComplexDyadicOutgoing.amplitude c z u n i))
  magnetic_far : ∀ n : Maxwell.Space, ‖n‖ = 1 → ∀ i : Fin 3,
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-Complex.I*z*r)*
      ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) (r • n) i)
      atTop (𝓝 (Packet06MagneticOutgoing.amplitude c z u n i))

theorem actual_outgoing_mode (c : Coefficient) (z : ℂ) (S : ℝ) (hS : 0 ≤ S) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hne : u ≠ 0) :
    IsActualOutgoingMode c z S u :=
  ⟨Packet06PhysicalMode.electric_nonzero c z S u hc hu hne,
    fun T i => electric_memLp_ball c z S T u hc i,
    fun T i => Packet06GlobalMaxwell.magnetic_memLp_ball c z S T u hc i,
    Packet06ComplexAffine.global_actual_test c z S hS u hc hu,
    fun n hn i => electric_outgoing c z S hS u hc n hn i,
    fun n hn i => Packet06MagneticOutgoing.magnetic_outgoing c z S hS u hc n hn i⟩

theorem physically_normalized_mode (c : Coefficient) (z : ℂ) (S : ℝ) (hS : 0 ≤ S) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hne : u ≠ 0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c S z u ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧
      ComplexConvolutionAnalytic.volumeBlock c z S (a • u) = 0 ∧
      Packet06PhysicalNormalization.reciprocalNorm c S z (a • u) = 1 ∧
      IsActualOutgoingMode c z S (a • u) := by
  obtain ⟨a,ha,_,hunit⟩ := Packet06PhysicalScale.physical_unit_scale c S hS z u hN
  have hk : ComplexConvolutionAnalytic.volumeBlock c z S (a • u) = 0 := by
    rw [map_smul,hu,smul_zero]
  exact ⟨a,ha,hk,hunit,actual_outgoing_mode c z S hS (a • u) hc hk (smul_ne_zero ha hne)⟩

end OQ14.Packet06OutgoingMode
#print axioms OQ14.Packet06OutgoingMode.actual_outgoing_mode
#print axioms OQ14.Packet06OutgoingMode.physically_normalized_mode
