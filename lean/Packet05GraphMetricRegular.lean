import Packet05ActualGraphExtensionC4
import Packet05GraphSlopeBounds

/-! A compact C⁴ graph gives a C³ graph metric, as required by the second
transmission iteration. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphMetricRegular
open OQ14.Maxwell OQ14.WeakCurl OQ14.ConicalJunctionPhysical
  OQ14.Packet05GraphSlope OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphSmooth
  OQ14.Packet05GraphChartMatrix
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem slope_c3 (g : Plane → ℝ) (hg : ContDiff ℝ 4 g) (i : Fin 3) :
    ContDiff ℝ 3 (Packet05GraphSlope.slope g i) := by
  exact ((liftedHeight_contDiff g hg).contDiff_fderiv_apply (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

theorem graph_metric_c3 (g : Plane → ℝ) (hg : ContDiff ℝ 4 g) (i j : Fin 3) :
    ContDiff ℝ 3 (fun x => (metric (Packet05GraphSlope.slope g 0 x)
      (Packet05GraphSlope.slope g 1 x) i j : ℂ)) := by
  have h0 : ContDiff ℝ 3 (fun x => (Packet05GraphSlope.slope g 0 x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (slope_c3 g hg 0)
  have h1 : ContDiff ℝ 3 (fun x => (Packet05GraphSlope.slope g 1 x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (slope_c3 g hg 1)
  fin_cases i <;> fin_cases j <;> simp [metric] <;>
    first | exact contDiff_const | exact h0.neg | exact h1.neg |
      exact (contDiff_const.add (h0.pow 2)).add (h1.pow 2)

end OQ14.Packet05GraphMetricRegular
#print axioms OQ14.Packet05GraphMetricRegular.slope_c3
#print axioms OQ14.Packet05GraphMetricRegular.graph_metric_c3
