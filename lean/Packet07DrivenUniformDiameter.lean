import Packet07DrivenUniformFixedTarget

/-! The explicit numerical ball bound is a strict closed-ball diameter bound. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07DrivenUniformDiameter
open Metric Maxwell

theorem closed_ball_diameter_lt (c : Space) (r ell : ℝ) (hr : 0 ≤ r) (h : 2*r < ell) :
    Metric.diam (closedBall c r) < ell :=
  (Metric.diam_closedBall hr).trans_lt h
end OQ14.Packet07DrivenUniformDiameter
#print axioms OQ14.Packet07DrivenUniformDiameter.closed_ball_diameter_lt
