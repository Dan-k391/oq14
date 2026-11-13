import Packet05GraphMetricUniformBounds
import Packet05GraphSlopeBounds

/-! Construct the metric and slope bounds used by an actual compact graph chart. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet05ChartMetricData
open Metric Maxwell WeakCurl Packet05GraphMetricCompact Packet05GraphSlopeMultiplier
abbrev Plane := ConicalSmoothJunction.Plane

theorem actual_metric_data (g : Plane → ℝ) (hg : ContDiff ℝ 4 g) (hc : HasCompactSupport g)
    (c : Space) (R : ℝ) (hR : 0 ≤ R) :
    ∃ (A : Fin 3 → Fin 3 → Test) (a b M : ℝ) (B : Fin 2 → ℝ),
      (∀ j k, ContDiff ℝ 3 (A j k).function) ∧
      (∀ x ∈ closedBall c R, ∀ j k, (A j k).function x =
        (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
          (Packet05GraphSlope.slope g 1 x) j k : ℂ)) ∧
      0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ M ∧
      (∀ j k x, ‖(A j k).function x‖ ≤ a) ∧
      (∀ j k l x, ‖dcoord (A j k).function x l‖ ≤ b) ∧
      (∀ x, |Packet05GraphSlope.slope g 0 x| ≤ M ∧ |Packet05GraphSlope.slope g 1 x| ≤ M) ∧
      (∀ l x, ‖slopeC g l.castSucc x‖ ≤ B l) := by
  let χ : ContDiffBump (0 : Space) := ⟨‖c‖+R+1,‖c‖+R+2,by positivity,by linarith⟩
  obtain ⟨a,b,ha,hb⟩ := Packet05GraphMetricUniformBounds.metric_uniform_bounds g hg χ
  obtain ⟨⟨B,hB⟩,_,_⟩ := Packet05GraphSlopeBounds.slope_bounds g (hg.of_le (by decide)) hc
  let M := max (max (B 0) (B 1)) 0
  refine ⟨metricTest g hg χ,max a 0,max b 0,M,(fun l => B l.castSucc),
    metric_test_c3 g hg χ,?_,le_max_right _ _,le_max_right _ _,le_max_right _ _,
    (fun j k x => (ha j k x).trans (le_max_left _ _)),
    (fun j k l x => (hb j k l x).trans (le_max_left _ _)),?_,fun l x => hB l.castSucc x⟩
  · intro x hx j k
    apply metric_test_agrees
    have hxR : dist x c ≤ R := hx
    have htri := dist_triangle x c 0
    simp only [dist_zero_right] at htri
    rw [mem_closedBall,dist_zero_right]
    change ‖x‖ ≤ ‖c‖+R+1
    linarith
  · intro x
    have h0 : |Packet05GraphSlope.slope g 0 x| ≤ B 0 := by
      simpa only [slopeC,Complex.norm_real,Real.norm_eq_abs] using hB 0 x
    have h1 : |Packet05GraphSlope.slope g 1 x| ≤ B 1 := by
      simpa only [slopeC,Complex.norm_real,Real.norm_eq_abs] using hB 1 x
    exact ⟨h0.trans ((le_max_left _ _).trans (le_max_left _ _)),
      h1.trans ((le_max_right _ _).trans (le_max_left _ _))⟩

end OQ14.Packet05ChartMetricData
#print axioms OQ14.Packet05ChartMetricData.actual_metric_data
