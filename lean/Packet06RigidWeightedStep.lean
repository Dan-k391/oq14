import Packet06AxialWeightedMaximum
import Packet06AffineWeightedMaximum
import Packet06RigidHotspotFrame

/-! One-step covariance of the actual weighted maximum on each observation
ball in a normalized rigid hotspot state. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06RigidWeightedStep
open MeasureTheory Set Metric Maxwell ModalAxialRotation Packet05ActualMaximum Packet05BinaryPhaseMaximum
  Packet06RigidHotspotState Packet06RigidWeightedMaximum Packet06PhaseWeightedMaximum
abbrev Space := Maxwell.Space

theorem axial_step {N : ℕ} {z : ℂ} {r M B : ℝ} (θ : ℝ) (d : State N z r M B)
    (i : Fin N) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hm : HasWeightedMaximum d.material z d.unknown d.body (closedBall (d.center i) r) n η inside outside b x) :
    HasWeightedMaximum (axial θ d).material z (axial θ d).unknown (axial θ d).body
      (closedBall ((axial θ d).center i) r) n η
      (Packet06AxialPhaseField.transport θ inside) (Packet06AxialPhaseField.transport θ outside) b (rotation θ x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (Packet06AxialPhaseField.transport θ inside)
      (Packet06AxialPhaseField.transport θ outside) b) (rotation θ x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  have h := Packet06AxialWeightedMaximum.axial_weighted θ d.material d.supportRadius d.supportRadius
    d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization d.body (closedBall (d.center i) r)
    d.body_open measurableSet_closedBall (d.ball_support i) (d.ball_positive i) n η inside outside b x hm
  have hball := Packet06AxialHotspotGeometry.image_closedBall θ (d.center i) r
  simpa only [hball] using h

theorem affine_step {N : ℕ} {z : ℂ} {r M B : ℝ} (a : Space) (d : State N z r M B)
    (i : Fin N) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hm : HasWeightedMaximum d.material z d.unknown d.body (closedBall (d.center i) r) n η inside outside b x) :
    HasWeightedMaximum (affine a d).material z (affine a d).unknown (affine a d).body
      (closedBall ((affine a d).center i) r) n η
      (Packet06PlacedPhaseField.transport 1 (by norm_num) a inside)
      (Packet06PlacedPhaseField.transport 1 (by norm_num) a outside) b
      (Packet06PlacementHomeomorph.placement 1 (by norm_num) a x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (Packet06PlacedPhaseField.transport 1 (by norm_num) a inside)
      (Packet06PlacedPhaseField.transport 1 (by norm_num) a outside) b)
      (Packet06PlacementHomeomorph.placement 1 (by norm_num) a x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  have h := Packet06AffineWeightedMaximum.affine_weighted d.material d.supportRadius d.supportRadius
    d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization a d.body (closedBall (d.center i) r)
    d.body_open measurableSet_closedBall (d.ball_support i) (d.ball_positive i) n η inside outside b x hm
  have hball := Packet06PlacementHomeomorph.image_closedBall 1 (by norm_num) a (d.center i) r
  simp only [div_one] at hball
  simpa only [hball] using h

theorem cyclic_step {N : ℕ} {z : ℂ} {r M B : ℝ} (d : State N z r M B)
    (i : Fin N) (n η : ℝ) (inside outside : Fin 3 → Space → ℂ) (b : Bool) (x : Space)
    (hm : HasWeightedMaximum d.material z d.unknown d.body (closedBall (d.center i) r) n η inside outside b x) :
    HasWeightedMaximum (cyclic d).material z (cyclic d).unknown (cyclic d).body
      (closedBall ((cyclic d).center i) r) n η
      (Packet06PlacedPhaseField.transport 1 (by norm_num) 0 inside)
      (Packet06PlacedPhaseField.transport 1 (by norm_num) 0 outside) b
      (Packet06PlacementHomeomorph.placement 1 (by norm_num) 0 x) ∧
    phasePermittivity n η b * (physicalAmplitude (phaseField (Packet06PlacedPhaseField.transport 1 (by norm_num) 0 inside)
      (Packet06PlacedPhaseField.transport 1 (by norm_num) 0 outside) b)
      (Packet06PlacementHomeomorph.placement 1 (by norm_num) 0 x))^2 =
      phasePermittivity n η b * (physicalAmplitude (phaseField inside outside b) x)^2 := by
  have h := Packet06AffineWeightedMaximum.affine_weighted d.material d.supportRadius d.supportRadius
    d.support_nonnegative le_rfl d.support z d.unknown d.kernel d.normalization 0 d.body (closedBall (d.center i) r)
    d.body_open measurableSet_closedBall (d.ball_support i) (d.ball_positive i) n η inside outside b x hm
  have hball := Packet06PlacementHomeomorph.image_closedBall 1 (by norm_num) 0 (d.center i) r
  simp only [div_one] at hball
  simpa only [hball] using h
end OQ14.Packet06RigidWeightedStep
#print axioms OQ14.Packet06RigidWeightedStep.axial_step
#print axioms OQ14.Packet06RigidWeightedStep.affine_step
#print axioms OQ14.Packet06RigidWeightedStep.cyclic_step
