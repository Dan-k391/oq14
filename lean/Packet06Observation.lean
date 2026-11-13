import Packet06LocalPencil
import Packet06LaurentTransport
import Packet06NormalizedMode
import RestrictedTEDatumLinear

/-! The actual sphere inverse pole transported to local physical electric
response representatives on every containing observation ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06Observation
open MeasureTheory Metric Filter Packet06SectorOperator Packet06SectorCrossing
open scoped Topology

theorem weighted_observation_independent (c : StaticCoefficient.Coefficient)
    (z : ℂ) (S T : ℝ) (hST : S ≤ T) (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0) :
    StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S T u) =
      StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S S u) := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have hov := (ae_restrict_iff' measurableSet_closedBall).mp
    (Packet06LocalPencil.response_overlap c z S S T hST u hc i)
  have ha := StaticNewton.material_source_ae c (Packet06LocalPencil.response c z S T u) i
  have hb := StaticNewton.material_source_ae c (Packet06LocalPencil.response c z S S u) i
  filter_upwards [hov,ha,hb,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S T u)) i,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S S u)) i]
    with x hov ha hb hpa hpb
  rw [← hpa,← hpb,ha,hb]
  by_cases hx : x ∈ closedBall (0 : Maxwell.Space) S
  · rw [hov hx]
  · rw [hc x hx]
    simp

theorem kernel_observation_nonzero (c : StaticCoefficient.Coefficient)
    (z : ℂ) (S T : ℝ) (hST : S ≤ T) (u : VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hne : u ≠ 0) :
    Packet06LocalPencil.response c z S T u ≠ 0 := by
  intro hz
  have h := weighted_observation_independent c z S T hST u hc
  rw [hz,map_zero,(Packet06LocalPencil.actual_kernel_transport c z S u hu).2] at h
  exact hne h.symm

def observation (n : ℝ) (hn : 1 < n) (T : ℝ) (z : ℂ) : Sector →L[ℂ] VectorL2 :=
  (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z 1 T).comp Sector.subtypeL

theorem observation_analyticAt (n : ℝ) (hn : 1 < n) (T : ℝ) (hT : 0 ≤ T+1) (z : ℂ) :
    AnalyticAt ℂ (observation n hn T) z := by
  exact (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip Sector.subtypeL).analyticAt
    (Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) z 1 T)).comp
      (f := fun w : ℂ => Packet06LocalPencil.response (ModalWeightedMode.coefficient n hn) w 1 T)
        (Packet06LocalPencil.response_analyticAt _ 1 T hT z)

theorem actual_observed_simple_pole (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T) :
    ∃ (R : Sector →L[ℂ] VectorL2) (B : ℂ → Sector →L[ℂ] VectorL2),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ v, R v = (leftFunctional n hn z v /
        leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))) •
          ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T (numerator n hn z)) ∧
      Tendsto (fun w => (w-z) • (observation n hn T w).comp (Ring.inverse (block n hn w)))
        (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ w in 𝓝[≠] z, (observation n hn T w).comp (Ring.inverse (block n hn w)) =
        (w-z)⁻¹ • R + B w) := by
  have hs := Packet06SpherePole.determinant_simple n hn hna z hz hd
  obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := Packet06SpherePole.inverse_simple_expansion n hn hna z hz hd hs
  have hC := observation_analyticAt n hn T (by linarith) z
  obtain ⟨D,hD,he⟩ := Packet06LaurentTransport.observation_expansion (H := Sector) (J := VectorL2)
    (fun w => Ring.inverse (block n hn w)) R B (observation n hn T) z hB hC hexp
  have hcross := crossing_nonzero n hn z hz hd hs
  have hN := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd
  have hnzero : observation n hn T z (numerator n hn z) ≠ 0 :=
    kernel_observation_nonzero _ z 1 T hT _ (ModalWeightedMode.coefficient_support n hn) hN.2 hN.1
  refine ⟨(observation n hn T z).comp R,D,?_,hD,?_,?_,he⟩
  · intro hzero
    have hv := congrArg (fun L : Sector →L[ℂ] VectorL2 =>
      L (blockDerivative n hn z (numerator n hn z))) hzero
    change observation n hn T z (R (blockDerivative n hn z (numerator n hn z))) = 0 at hv
    rw [hform,map_smul,div_self hcross,one_smul] at hv
    exact hnzero hv
  · intro v
    change observation n hn T z (R v) = _
    rw [hform,map_smul]
    rfl
  · exact Packet06LaurentTransport.observation_residue_limit (H := Sector) (J := VectorL2)
      (fun w => Ring.inverse (block n hn w)) R (observation n hn T) z hC.continuousAt hlim

end OQ14.Packet06Observation
#print axioms OQ14.Packet06Observation.weighted_observation_independent
#print axioms OQ14.Packet06Observation.kernel_observation_nonzero
#print axioms OQ14.Packet06Observation.observation_analyticAt
#print axioms OQ14.Packet06Observation.actual_observed_simple_pole
