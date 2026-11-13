import Packet06NeighborhoodWeighted
import Packet06InteriorTraceUnique

/-! Neighborhood-certified one-sided maxima are independent of the chosen actual traces. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06NeighborhoodTraceIntrinsic
open MeasureTheory Set Metric Maxwell Packet06RigidHotspotState Packet06NeighborhoodWeighted
  Packet06RigidWeightedMaximum Packet06PhaseWeightedMaximum Packet05ActualMaximum Packet05BinaryPhaseMaximum
abbrev Space := Maxwell.Space

theorem intrinsic {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B) (i : Fin N)
    (R n η : ℝ) (hr : r < R) (inside outside inside' outside' : Fin 3 → Space → ℂ)
    (b : Bool) (x : Space)
    (h : Certificate d i (closedBall (d.center i) R) n η inside outside b x)
    (h' : Trace d.material z d.unknown d.body (closedBall (d.center i) R) inside' outside') :
    (∀ p j y, y ∈ closedBall (d.center i) r ∩ phaseDomain d.body p →
      phaseField inside outside p j y = phaseField inside' outside' p j y) ∧
    (∀ p y, y ∈ closedBall (d.center i) r ∩ phaseDomain d.body p →
      phasePermittivity n η p * (physicalAmplitude (phaseField inside outside p) y)^2 =
        phasePermittivity n η p * (physicalAmplitude (phaseField inside' outside' p) y)^2) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside' outside' b) x)^2 ∧
    (∀ p y, y ∈ closedBall (d.center i) r ∩ phaseDomain d.body p →
      phasePermittivity n η p * (physicalAmplitude (phaseField inside' outside' p) y)^2 ≤
        phasePermittivity n η b * (physicalAmplitude (phaseField inside' outside' b) x)^2) := by
  obtain ⟨_,_,_,_,⟨hi,ho,hiae,hoae⟩,hmax⟩ := h
  obtain ⟨hi',ho',hiae',hoae'⟩ := h'
  have heq : ∀ p j y, y ∈ closedBall (d.center i) r ∩ phaseDomain d.body p →
      phaseField inside outside p j y = phaseField inside' outside' p j y := by
    intro p j y hy
    cases p with
    | true =>
      exact Packet06InteriorTraceUnique.unique d.body d.body_open (d.center i) r R hr _ _ _
        (hi j) (hi' j) (hiae j).symm (hiae' j).symm hy
    | false =>
      exact Packet06InteriorTraceUnique.unique (closure d.body)ᶜ isClosed_closure.isOpen_compl
        (d.center i) r R hr _ _ _ (ho j) (ho' j) (hoae j).symm (hoae' j).symm hy
  have hdens : ∀ p y, y ∈ closedBall (d.center i) r ∩ phaseDomain d.body p →
      phasePermittivity n η p * (physicalAmplitude (phaseField inside outside p) y)^2 =
        phasePermittivity n η p * (physicalAmplitude (phaseField inside' outside' p) y)^2 := by
    intro p y hy
    unfold physicalAmplitude
    simp_rw [heq p _ y hy]
  have hx := hmax.2.2.2.2.1
  have hbound := hmax.2.2.2.2.2
  refine ⟨heq,hdens,hdens b x hx,?_⟩
  intro p y hy
  rw [←hdens p y hy,←hdens b x hx]
  exact hbound p y hy
end OQ14.Packet06NeighborhoodTraceIntrinsic
#print axioms OQ14.Packet06NeighborhoodTraceIntrinsic.intrinsic
