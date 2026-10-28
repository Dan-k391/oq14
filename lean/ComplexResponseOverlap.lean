import ComplexExteriorHelmholtz

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ComplexResponseOverlap
open Complex MeasureTheory Metric Set OQ14.Maxwell OQ14.DynamicConvolution
  OQ14.ComplexExteriorResponse
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

theorem component_operator (z : ℂ) (R : ℝ) (F : VectorL2) (i : Fin 3) :
    component i (ComplexConvolutionAnalytic.operator z R F) = ComplexConvolutionAnalytic.row z R i F := by
  change component i (∑ j : Fin 3, insert j (ComplexConvolutionAnalytic.row z R j F)) = _
  simp only [map_sum, component_insert]
  simp

theorem operator_ae_convolution (z : ℂ) (R : ℝ) (F : VectorL2)
    (hF : ∀ j, Integrable (component j F : Maxwell.Space → ℂ)) (i : Fin 3) :
    (fun x => ComplexConvolutionAnalytic.operator z R F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => ∑ j : Fin 3, HeatFourier.convolution (ComplexKernelAnalytic.kernel z R i j) (component j F) x := by
  have hcoord := (NewtonL2.physicalCoordinate_ae (ComplexConvolutionAnalytic.operator z R F) i).symm
  change (fun x => ComplexConvolutionAnalytic.operator z R F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
    (component i (ComplexConvolutionAnalytic.operator z R F) : Maxwell.Space → ℂ) at hcoord
  rw [component_operator] at hcoord
  apply hcoord.trans
  have hs := scalar_sum_ae (fun j => ComplexConvolutionAnalytic.entry z R i j (component j F))
  have hc := ae_all_iff.mpr (fun j => ComplexConvolutionAnalytic.entry_spatial_ae z R i j (component j F) (hF j))
  filter_upwards [hs, hc] with x hx hy
  change (∑ j : Fin 3, ComplexConvolutionAnalytic.entry z R i j (component j F)) x = _
  rw [hx]
  simp only [hy]

theorem truncated_convolution (z : ℂ) (T : ℝ) (F : VectorL2) (ρ : Maxwell.Space → ℂ) (j : Fin 3)
    (hF : (NewtonL2.physicalCoordinate F j : Maxwell.Space → ℂ) =ᵐ[volume] ρ) (i : Fin 3) (x : Maxwell.Space) :
    HeatFourier.convolution (ComplexKernelAnalytic.kernel z T i j) (component j F) x =
      ∫ y, ComplexKernelAnalytic.kernel z T i j (x-y) * ρ y := by
  change MeasureTheory.convolution (ComplexKernelAnalytic.kernel z T i j) (component j F)
    (ContinuousLinearMap.mul ℂ ℂ) volume x = _
  rw [MeasureTheory.convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards [hF] with y hy
  rw [component_apply, hy]

theorem kernel_source_eq (z : ℂ) (S T : ℝ) (ρ : Maxwell.Space → ℂ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (i j : Fin 3)
    (x y : Maxwell.Space) (hx : x ∈ closedBall 0 T) :
    ComplexKernelAnalytic.kernel z (T+S) i j (x-y) * ρ y =
      ComplexDynamicKernel.remainder z (x-y) i j * ρ y := by
  by_cases hy : y ∈ closedBall (0 : Maxwell.Space) S
  · have hxy : x-y ∈ closedBall (0 : Maxwell.Space) (T+S) := by
      simp only [mem_closedBall, dist_zero_right] at hx hy ⊢
      exact (norm_sub_le _ _).trans (add_le_add hx hy)
    simp [ComplexKernelAnalytic.kernel, hxy]
  · simp [hc y hy]

theorem dynamic_ae_on_ball (z : ℂ) (S T : ℝ) (F : VectorL2)
    (ρ : Fin 3 → Maxwell.Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Maxwell.Space → ℂ) =ᵐ[volume] ρ j)
    (i : Fin 3) :
    (fun x => ComplexConvolutionAnalytic.operator z (T+S) F (VectorFourier.coordinateMap x) i)
      =ᵐ[volume.restrict (closedBall 0 T)]
      fun x => ∑ j, ∫ y, ComplexDynamicKernel.remainder z (x-y) i j * ρ j y := by
  have hd := OQ14.ComplexResponseOverlap.operator_ae_convolution z (T+S) F (fun j => (hρ j).congr (hF j).symm) i
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_closedBall] with x hx hxb
  rw [hx]
  apply Finset.sum_congr rfl
  intro j _
  rw [truncated_convolution z (T+S) F (ρ j) j (hF j) i x]
  apply integral_congr_ae
  filter_upwards with y
  exact kernel_source_eq z S T (ρ j) (hc j) i j x y hxb

theorem response_overlap (c : Coefficient) (z : ℂ) (S T U : ℝ) (hTU : T ≤ U) (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => response c z S T u (VectorFourier.coordinateMap x) i) =ᵐ[volume.restrict (closedBall 0 T)]
      fun x => response c z S U u (VectorFourier.coordinateMap x) i := by
  let F := StaticCoefficient.sqrtMultiplier c u
  let ρ := DynamicVolume.source c u
  have hρ := DynamicVolume.source_integrable c u S hc
  have hzero := DynamicVolume.source_zero c u S hc
  have hF := StaticNewton.material_source_ae c u
  have hsmall := dynamic_ae_on_ball z S T F ρ hρ hzero hF i
  have hlarge := dynamic_ae_on_ball z S U F ρ hρ hzero hF i
  have hm : volume.restrict (closedBall (0 : Maxwell.Space) T) ≤ volume.restrict (closedBall 0 U) :=
    Measure.restrict_mono (closedBall_subset_closedBall hTU) le_rfl
  have hadd (V : ℝ) := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (NewtonL2.newtonOperator F) (ComplexConvolutionAnalytic.operator z (V+S) F))
  filter_upwards [hsmall, ae_mono hm hlarge, ae_restrict_of_ae (hadd T),
    ae_restrict_of_ae (hadd U)] with x hs hl ha hb
  change (NewtonL2.newtonOperator F + ComplexConvolutionAnalytic.operator z (T+S) F)
      (VectorFourier.coordinateMap x) i =
    (NewtonL2.newtonOperator F + ComplexConvolutionAnalytic.operator z (U+S) F)
      (VectorFourier.coordinateMap x) i
  rw [ha, hb]
  change NewtonL2.newtonOperator F (VectorFourier.coordinateMap x) i +
      ComplexConvolutionAnalytic.operator z (T+S) F (VectorFourier.coordinateMap x) i =
    NewtonL2.newtonOperator F (VectorFourier.coordinateMap x) i +
      ComplexConvolutionAnalytic.operator z (U+S) F (VectorFourier.coordinateMap x) i
  rw [hs, hl]

#print axioms OQ14.ComplexResponseOverlap.response_overlap
#print axioms OQ14.ComplexResponseOverlap.operator_ae_convolution
#print axioms OQ14.ComplexResponseOverlap.dynamic_ae_on_ball
end OQ14.ComplexResponseOverlap


