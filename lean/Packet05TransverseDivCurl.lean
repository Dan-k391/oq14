import Packet05LongitudinalCurl

/-! Actual whole-space transverse/longitudinal div-curl decomposition. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TransverseDivCurl
open OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05TransverseDivergence
  OQ14.Packet05LongitudinalCurl

theorem transverse_divcurl (F : VectorFourier.VectorL2) (C : L2Vector)
    (hF : HasWeakCurl (coordinateVector F) C) :
    HasWeakDivergence (coordinateVector (transverse F)) 0 ∧
    HasWeakCurl (coordinateVector (transverse F)) C ∧
    HasWeakCurl (coordinateVector (VectorFourier.physicalProjection F)) 0 := by
  have hlong := longitudinal_weak_curl_zero F
  have hFgraph : ((coordinateVector F, C) : WeakCurl.Ambient) ∈ WeakCurl.graph := hF
  have hLgraph : ((coordinateVector (VectorFourier.physicalProjection F), 0) : WeakCurl.Ambient) ∈ WeakCurl.graph := hlong
  have hsub := WeakCurl.graph.sub_mem hFgraph hLgraph
  change HasWeakCurl (coordinateVector F - coordinateVector (VectorFourier.physicalProjection F)) (C - 0) at hsub
  have hcurl : HasWeakCurl (coordinateVector (transverse F)) C := by
    simpa only [transverse, map_sub, sub_zero] using hsub
  refine ⟨?_,hcurl,hlong⟩
  exact transverse_weak_divergence F

end OQ14.Packet05TransverseDivCurl
#print axioms OQ14.Packet05TransverseDivCurl.transverse_divcurl
