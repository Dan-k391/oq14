import Packet05TransverseDivergence

/-! The actual longitudinal L² projection has zero distributional curl. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05LongitudinalCurl
open MeasureTheory Set Filter OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.HelmholtzProjection OQ14.NewtonL2
open scoped Topology SchwartzMap

def coordinateMap (i : Fin 3) : VectorFourier.VectorL2 →L[ℂ] L2Scalar :=
  VectorFourier.scalarCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp (VectorFourier.coordinate i)

def coordinateVector : VectorFourier.VectorL2 →L[ℂ] L2Vector :=
  ContinuousLinearMap.pi coordinateMap

def curlFree : Submodule ℂ VectorFourier.VectorL2 :=
  WeakCurl.graph.comap (coordinateVector.prod 0).toLinearMap

theorem curlFree_closed : IsClosed (curlFree : Set VectorFourier.VectorL2) := by
  exact WeakCurl.graph_closed.preimage (coordinateVector.prod 0).continuous

theorem gradient_curl_free (f : 𝓢(Maxwell.Space, ℂ)) : GradientProjection.gradient f ∈ curlFree := by
  change HasWeakCurl (coordinateVector (GradientProjection.gradient f)) 0
  intro φ j
  change weakCurl φ j (coordinateVector (GradientProjection.gradient f)) - valuePair φ (0 : L2Scalar) = 0
  simp only [map_zero, sub_zero, weakCurl, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  have hc (i : Fin 3) : coordinateVector (GradientProjection.gradient f) i =
      FourierL2.embed (GradientProjection.pderivative i f) := by
    change physicalCoordinate (GradientProjection.gradient f) i = _
    exact physicalCoordinate_schwartz (fun i => GradientProjection.pderivative i f) i
  rw [hc, hc]
  have h1 := schwartz_hasWeakPartial (GradientProjection.pderivative (next j) f) (previous j) φ
  have h2 := schwartz_hasWeakPartial (GradientProjection.pderivative (previous j) f) (next j) φ
  have he : GradientProjection.pderivative (previous j) (GradientProjection.pderivative (next j) f) =
      GradientProjection.pderivative (next j) (GradientProjection.pderivative (previous j) f) := by
    ext x
    simp only [GradientProjection.pderivative_apply]
    exact Maxwell.partial_comm (f.smooth 2) x (previous j) (next j)
  rw [he] at h1
  linear_combination h1 - h2

theorem longitudinal_weak_curl_zero (F : VectorFourier.VectorL2) :
    HasWeakCurl (coordinateVector (VectorFourier.physicalProjection F)) 0 := by
  have hspan : (gradientSpan : Set VectorFourier.VectorL2) ⊆ curlFree := by
    apply Submodule.span_le.mpr
    rintro _ ⟨f,rfl⟩
    exact gradient_curl_free f
  have hp := physicalProjection_mem_closedGradients F
  change VectorFourier.physicalProjection F ∈ closure (gradientSpan : Set VectorFourier.VectorL2) at hp
  exact (closure_minimal hspan curlFree_closed) hp

end OQ14.Packet05LongitudinalCurl
#print axioms OQ14.Packet05LongitudinalCurl.curlFree_closed
#print axioms OQ14.Packet05LongitudinalCurl.gradient_curl_free
#print axioms OQ14.Packet05LongitudinalCurl.longitudinal_weak_curl_zero
