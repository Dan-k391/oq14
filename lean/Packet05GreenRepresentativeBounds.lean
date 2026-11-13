import Packet05ActualCompactGreenH2
import WeakPoynting.InteriorTestDensity

/-! Quantitative bounds for the actual ball-restricted Green representatives,
including the static distributional Hessian. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GreenRepresentativeBounds
open MeasureTheory Set Metric Maxwell Packet05LocalGreenRepresentatives

theorem ball_norm_le (R : ℝ) (f : Space → ℂ)
    (hf : MemLp f 2 (volume.restrict (closedBall 0 R)))
    (U : NewtonL2.ScalarL2) (hU : ∀ᵐ x ∂volume, x ∈ closedBall 0 R → U x=f x) :
    ‖ballRepresentative R f hf‖ ≤ ‖U‖ := by
  apply Lp.norm_le_norm_of_ae_le
  have hrep : (ballRepresentative R f hf : Space → ℂ) =ᵐ[volume] (closedBall (0 : Space) R).indicator f :=
    ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr hf).coeFn_toLp
  filter_upwards [hrep,hU] with x hx hu
  rw [hx]
  by_cases h : x ∈ closedBall (0 : Space) R
  · rw [indicator_of_mem h,←hu h]
  · simp only [indicator_of_not_mem h,norm_zero]
    exact norm_nonneg _

theorem response_representative_norm (q ρ : Space → ℂ) (hq : LocallyIntegrable q volume)
    (R S : ℝ) (F : NewtonL2.ScalarL2) (hρ : Integrable ρ)
    (hF : (F : Space → ℂ) =ᵐ[volume] ρ)
    (hs : ∀ y, y ∉ closedBall 0 S → ρ y=0) :
    ‖ballRepresentative R (KernelConvolution.response q ρ)
      (LocalConvolution.response_memLp_ball q hq ρ hρ F hF R S hs)‖ ≤
      ‖LocalConvolution.operator q hq (R+S)‖*‖F‖ := by
  exact (ball_norm_le R _ _ (LocalConvolution.operator q hq (R+S) F)
    (LocalConvolution.operator_ae_on_ball q hq ρ hρ F hF R S hs)).trans
    (ContinuousLinearMap.le_opNorm _ _)

theorem scalarSource_eq_insert (F : NewtonL2.ScalarL2) (i : Fin 3) :
    Packet05ScalarNewtonEmbedding.scalarSource F i=DynamicConvolution.insert i F := by
  apply VectorFourier.components.injective
  apply PiLp.ext
  intro j
  apply VectorFourier.scalarCoordinates.injective
  change NewtonL2.physicalCoordinate (Packet05ScalarNewtonEmbedding.scalarSource F i) j=
    DynamicConvolution.component j (DynamicConvolution.insert i F)
  rw [Packet05ScalarNewtonEmbedding.scalarSource_coordinate,DynamicConvolution.component_insert]

theorem static_hessian_norm (F : NewtonL2.ScalarL2) (i j : Fin 3) :
    ‖NewtonL2.physicalCoordinate (NewtonL2.newtonOperator
      (Packet05ScalarNewtonEmbedding.scalarSource F i)) j‖ ≤ ‖F‖ := by
  rw [scalarSource_eq_insert]
  apply (DynamicConvolution.component_norm j _).trans
  apply (ContinuousLinearMap.le_opNorm _ _).trans
  exact (mul_le_mul_of_nonneg_right NewtonL2.newtonOperator_norm_le (norm_nonneg _)).trans
    (by simpa only [one_mul] using DynamicConvolution.insert_norm i F)

end OQ14.Packet05GreenRepresentativeBounds
#print axioms OQ14.Packet05GreenRepresentativeBounds.ball_norm_le
#print axioms OQ14.Packet05GreenRepresentativeBounds.response_representative_norm
#print axioms OQ14.Packet05GreenRepresentativeBounds.scalarSource_eq_insert
#print axioms OQ14.Packet05GreenRepresentativeBounds.static_hessian_norm
