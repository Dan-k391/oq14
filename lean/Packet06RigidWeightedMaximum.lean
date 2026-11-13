import Packet06AffineTraceGeneral
import Packet06AxialTraceCollar
import Packet06PhaseWeightedMaximum

/-! A genuine actual-field one-sided weighted maximum and its invariance
under the rigid motions used by the arbitrary-plane frame. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06RigidWeightedMaximum
open MeasureTheory Set Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06PhaseWeightedMaximum Packet06PlacedKernel
open scoped Topology
abbrev Space := Maxwell.Space

def HasWeightedMaximum (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (body K : Set Space) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space) : Prop :=
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
  (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
  (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
  (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
  (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) ∧
  x ∈ K ∩ phaseDomain body b ∧
  ∀ b' y, y ∈ K ∩ phaseDomain body b' →
    phasePermittivity n η b' * (physicalAmplitude (phaseField inside outside b') y)^2 ≤
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2
end OQ14.Packet06RigidWeightedMaximum
