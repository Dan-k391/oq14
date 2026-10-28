import ModalAngularPairing
import ModalVectorAngularSlices

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace OQ14.ModalAngularSlicePairing
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower
  OQ14.ModalVolumeAngularCoefficients
open scoped Topology ComplexInnerProductSpace
abbrev VectorL2 := VectorFourier.VectorL2

theorem component_vector_ae (u : VectorL2) : ∀ᵐ x : Space ∂volume, ∀ i : Fin 3,
    DynamicConvolution.component i u x = u (VectorFourier.coordinateMap x) i :=
  ae_all_iff.mpr (HalfTurnVectorAction.component_ae u)

theorem coefficient_slice_inner (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), coefficient u m r =
      @inner ℂ ComplexVectorSphere.Ambient _ (ContinuousMap.toLp 2 angularMeasure ℂ m)
        (ModalVectorAngularSlices.slice u r) := by
  have hp := PolarMomentAE.polar_ae (component_vector_ae u)
  filter_upwards [ModalAngularPairing.coefficient_integral u m,
    ModalVectorAngularSlices.slice_actual_ae u, hp] with r hc hs hp
  rw [hc, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hs,hp,m.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with ω hs hp hm
  have hm' : (ContinuousMap.toLp 2 angularMeasure ℂ m : ComplexVectorSphere.Ambient) ω = m ω := hm
  rw [hs, hm']
  simp only [PiLp.inner_apply, RCLike.inner_apply, weight]
  apply Finset.sum_congr rfl
  intro i _
  rw [hp i]
  simp [mul_comm]

#print axioms OQ14.ModalAngularSlicePairing.component_vector_ae
#print axioms OQ14.ModalAngularSlicePairing.coefficient_slice_inner
end OQ14.ModalAngularSlicePairing

