import ComplexInterfaceWeak
import ComplexResponseAnalytic

noncomputable section
set_option autoImplicit false
namespace OQ14.ComplexSphereInterface
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicSource
open scoped SchwartzMap Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem source_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) :
    DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i =ᵐ[volume] fun x =>
      (ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x) *
        ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
          (VectorFourier.coordinateMap x) i := by
  have hsource := ComplexResponseAnalytic.kernel_source_relation
    (ModalWeightedMode.coefficient n hn) z 1 u hker i
  have hover := ComplexResponseOverlap.response_overlap (ModalWeightedMode.coefficient n hn)
    z 1 1 T hT u (ModalWeightedMode.coefficient_support n hn) i
  have hover' := (ae_restrict_iff' measurableSet_closedBall).mp hover
  filter_upwards [hsource, hover'] with x hs ho
  by_cases hi : x ∈ closedBall (0 : Space) 1
  · rw [hs]
    have he := ho hi
    have hr : ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 1 u =
        ComplexKernelResponse.response (ModalWeightedMode.coefficient n hn) z 1 u := by
      simp [ComplexExteriorResponse.response, ComplexKernelResponse.response, show (1:ℝ) + 1 = 2 by norm_num]
    rw [hr] at he
    rw [he]
  · rw [hs, ModalWeightedMode.coefficient_support n hn x hi]
    simp

theorem displacement_pair_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (i : Fin 3) (f : Test) :
    ComplexInterfaceWeak.displacementPair (ModalWeightedMode.coefficient n hn) z 1 T u i f =
      ∫ x, (1 + ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x) : ℂ)) *
        ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
          (VectorFourier.coordinateMap x) i * f.val x := by
  unfold ComplexInterfaceWeak.displacementPair ComplexInterfaceWeak.pair
  rw [ComplexResponseTests.testPair_integral]
  have hi : Integrable (fun x : Space =>
      ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
        (VectorFourier.coordinateMap x) i * f.val x) := by
    have h := NewtonL2.scalar_pairing_integrable (NewtonL2.physicalCoordinate
      (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i) f.val
    apply h.congr
    filter_upwards [NewtonL2.physicalCoordinate_ae _ i] with x hx
    rw [hx]
  have hs : Integrable (fun x : Space => DynamicVolume.source (ModalWeightedMode.coefficient n hn) u i x * f.val x) :=
    PointSingularity.test_product_integrable _ _
      ((DynamicVolume.source_integrable _ u 1 (ModalWeightedMode.coefficient_support n hn) i).locallyIntegrable)
      f.val.continuous f.property
  rw [← integral_add hi hs]
  apply integral_congr_ae
  filter_upwards [source_actual n hn z T hT u hker i] with x hx
  rw [hx]
  ring

theorem weak_normal_transmission (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 ≤ T) (u : VectorL2)
    (hker : ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1 u = 0)
    (f : Test) (hf : tsupport (f.val : Space → ℂ) ⊆ closedBall 0 T) :
    (∑ j : Fin 3, ∫ x, (1 + ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x) : ℂ)) *
      ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
        (VectorFourier.coordinateMap x) j * (testPartial j f).val x) = 0 := by
  have h := ComplexInterfaceWeak.displacement_divergence_zero (ModalWeightedMode.coefficient n hn)
    z hz 1 T (by linarith) u (ModalWeightedMode.coefficient_support n hn) f hf
  simpa only [displacement_pair_actual n hn z T hT u hker] using h

#print axioms OQ14.ComplexSphereInterface.displacement_pair_actual
#print axioms OQ14.ComplexSphereInterface.weak_normal_transmission
#print axioms OQ14.ComplexSphereInterface.source_actual
end OQ14.ComplexSphereInterface



