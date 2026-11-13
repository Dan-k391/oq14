import Packet06Observation
import ConicalBallRestriction

/-! Actual bounded-ball L2 electric response and its nonzero rank-one pole. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06BallObservation
open MeasureTheory Metric Filter Packet06SectorOperator Packet06SectorCrossing
open Packet06Observation ConicalRungeBall
open scoped Topology

theorem weighted_zero_of_ball_zero (c : StaticCoefficient.Coefficient) (S T : ℝ)
    (hST : S ≤ T) (F : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hf : ConicalBallRestriction.vector T F = 0) : StaticCoefficient.sqrtMultiplier c F = 0 := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hz : (ConicalBallRestriction.vector T F i : ScalarBall T) = 0 := congrArg (fun v : BallL2 T => v i) hf
  have ha := ConicalBallRestriction.vector_ae T F i
  rw [hz] at ha
  have hb := ha.symm.trans (Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume.restrict (closedBall (0 : Maxwell.Space) T)))
  have hzero := (ae_restrict_iff' measurableSet_closedBall).mp hb
  have hout := StaticNewton.material_source_ae c F i
  have hg := NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c F) i
  have hFcoord := NewtonL2.physicalCoordinate_ae F i
  have h0 := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (show (0 : VectorL2) =ᵐ[volume] (fun _ => 0) from Lp.coeFn_zero VectorFourier.Vector 2 volume)
  filter_upwards [hzero,hout,hg,hFcoord,h0] with x hx hs hg hFcoord h0
  rw [←hg,hs,h0]
  change _ = 0
  by_cases hxs : x ∈ closedBall (0 : Maxwell.Space) S
  · have hxT := closedBall_subset_closedBall hST hxs
    have hp := hx hxT
    rw [hFcoord] at hp
    change F (VectorFourier.coordinateMap x) i = 0 at hp
    rw [hp,mul_zero]
  · rw [hc x hxs]
    simp

theorem kernel_ball_observation_nonzero (c : StaticCoefficient.Coefficient)
    (z : ℂ) (S T : ℝ) (hST : S ≤ T) (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hne : u ≠ 0) :
    ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u) ≠ 0 := by
  intro hz
  have h := weighted_zero_of_ball_zero c S T hST _ hc hz
  rw [weighted_observation_independent c z S T hST u hc,
    (Packet06LocalPencil.actual_kernel_transport c z S u hu).2] at h
  exact hne h

def physicalObservation (n : ℝ) (hn : 1 < n) (T : ℝ) (z : ℂ) : Sector →L[ℂ] BallL2 T :=
  (ConicalBallRestriction.vector T).comp (observation n hn T z)

theorem actual_ball_simple_pole (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T) :
    ∃ (R : Sector →L[ℂ] BallL2 T) (B : ℂ → Sector →L[ℂ] BallL2 T),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ v, R v = (leftFunctional n hn z v /
        leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))) •
          physicalObservation n hn T z (numerator n hn z)) ∧
      Tendsto (fun w => (w-z) • (physicalObservation n hn T w).comp (Ring.inverse (block n hn w)))
        (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ w in 𝓝[≠] z, (physicalObservation n hn T w).comp (Ring.inverse (block n hn w)) =
        (w-z)⁻¹ • R + B w) := by
  obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := actual_observed_simple_pole n hn hna z hz hd T hT
  let L : (Sector →L[ℂ] VectorL2) →L[ℂ] (Sector →L[ℂ] BallL2 T) :=
    ContinuousLinearMap.compL ℂ Sector VectorL2 (BallL2 T) (ConicalBallRestriction.vector T)
  have hcross := crossing_nonzero n hn z hz hd (Packet06SpherePole.determinant_simple n hn hna z hz hd)
  have hN := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd
  have hNball : physicalObservation n hn T z (numerator n hn z) ≠ 0 :=
    kernel_ball_observation_nonzero _ z 1 T hT _ (ModalWeightedMode.coefficient_support n hn) hN.2 hN.1
  have hform' (v : Sector) : (L R) v = (leftFunctional n hn z v /
      leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))) •
        physicalObservation n hn T z (numerator n hn z) := by
    change ConicalBallRestriction.vector T (R v) = _
    rw [hform,map_smul]
    rfl
  have hB' : AnalyticAt ℂ (fun w => L (B w)) z := by
    exact ((ContinuousLinearMap.compL ℂ Sector VectorL2 (BallL2 T)).analyticAt_bilinear
      (ConicalBallRestriction.vector T,B z)).comp
        (f := fun w : ℂ => (ConicalBallRestriction.vector T,B w)) (analyticAt_const.prod hB)
  refine ⟨L R,fun w => L (B w),?_,hB',hform',?_,?_⟩
  · intro hzero
    have hv := congrArg (fun F : Sector →L[ℂ] BallL2 T =>
      F (blockDerivative n hn z (numerator n hn z))) hzero
    change (L R) (blockDerivative n hn z (numerator n hn z)) = 0 at hv
    rw [hform',div_self hcross,one_smul] at hv
    exact hNball hv
  · have hl := L.continuous.continuousAt.tendsto.comp hlim
    simpa only [map_smul,L,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_assoc,
      physicalObservation,Function.comp_def] using hl
  · filter_upwards [hexp] with w hw
    have hh := congrArg L hw
    simpa only [map_smul,map_add,L,ContinuousLinearMap.compL_apply,ContinuousLinearMap.comp_assoc,
      physicalObservation] using hh

end OQ14.Packet06BallObservation
#print axioms OQ14.Packet06BallObservation.weighted_zero_of_ball_zero
#print axioms OQ14.Packet06BallObservation.kernel_ball_observation_nonzero
#print axioms OQ14.Packet06BallObservation.actual_ball_simple_pole
