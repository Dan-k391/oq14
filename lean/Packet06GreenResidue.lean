import Packet06GreenPhysical

/-! The direct electric Green residue on actual bounded physical observation
spaces, for material-supported sector sources J = sqrt(chi) g. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06GreenResidue
open MeasureTheory Metric Filter Packet06SectorOperator Packet06SectorCrossing
open Packet06Observation Packet06BallObservation ConicalRungeBall KernelReciprocity
open Packet06PhysicalNormalization
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def greenObservation (n : ℝ) (hn : 1 < n) (T : ℝ) (z : ℂ) : Sector →L[ℂ] BallL2 T :=
  (z^2)⁻¹ • physicalObservation n hn T z

theorem greenObservation_analyticAt (n : ℝ) (hn : 1 < n) (T : ℝ)
    (hT : 0 ≤ T+1) (z : ℂ) (hz : z ≠ 0) :
    AnalyticAt ℂ (greenObservation n hn T) z := by
  have hobs : AnalyticAt ℂ (physicalObservation n hn T) z :=
    ((ContinuousLinearMap.compL ℂ Sector VectorL2 (BallL2 T)).analyticAt_bilinear
      (ConicalBallRestriction.vector T,observation n hn T z)).comp
        (f := fun w : ℂ => (ConicalBallRestriction.vector T,observation n hn T w))
          (analyticAt_const.prod (observation_analyticAt n hn T hT z))
  exact ((analyticAt_id.pow 2).inv (pow_ne_zero 2 hz)).smul hobs

theorem source_pairing (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T) (g : Sector) :
    leftFunctional n hn z g = vectorPair
      (observation n hn T z (numerator n hn z))
      (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) g) := by
  have hN := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd
  have he : StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn)
      (observation n hn T z (numerator n hn z)) = (numerator n hn z : VectorL2) := by
    change StaticCoefficient.sqrtMultiplier _ (Packet06LocalPencil.response _ z 1 T _) = _
    rw [weighted_observation_independent _ z 1 T hT _ (ModalWeightedMode.coefficient_support n hn)]
    exact (Packet06LocalPencil.actual_kernel_transport _ z 1 _ hN.2).2
  change vectorPair (g : VectorL2) (numerator n hn z : VectorL2) = _
  rw [←he,←NewtonReciprocity.sqrtMultiplier_reciprocity,vectorPair_comm]

theorem source_pairing_physical (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T) (g : Sector) :
    leftFunctional n hn z g = ∫ x : Maxwell.Space, ∑ i : Fin 3,
      observation n hn T z (numerator n hn z) (VectorFourier.coordinateMap x) i *
        (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) g)
          (VectorFourier.coordinateMap x) i := by
  rw [source_pairing n hn z hz hd T hT g,Packet06PhysicalPairing.vectorPair_physical]

theorem norm_eq_sector_crossing (n : ℝ) (hn : 1 < n) (z : ℂ) :
    reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z (numerator n hn z) =
      -(z/2)*leftFunctional n hn z (blockDerivative n hn z (numerator n hn z)) := by
  rw [reciprocalNorm_eq_crossing _ 1 (by norm_num)]
  congr 1
  change _ = vectorPair ((blockDerivative n hn z (numerator n hn z) : Sector) : VectorL2)
    (numerator n hn z)
  rw [block_derivative_actual]

theorem actual_direct_green_pole (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (T : ℝ) (hT : 1 ≤ T) :
    ∃ (R : Sector →L[ℂ] BallL2 T) (B : ℂ → Sector →L[ℂ] BallL2 T),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z (numerator n hn z) ≠ 0 ∧
      (∀ g, R g =
        (-vectorPair (observation n hn T z (numerator n hn z))
          (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) g) /
          (2*z*reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z (numerator n hn z))) •
            physicalObservation n hn T z (numerator n hn z)) ∧
      Tendsto (fun w => (w-z) • (greenObservation n hn T w).comp (Ring.inverse (block n hn w)))
        (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ w in 𝓝[≠] z, (greenObservation n hn T w).comp (Ring.inverse (block n hn w)) =
        (w-z)⁻¹ • R + B w) := by
  have hs := Packet06SpherePole.determinant_simple n hn hna z hz hd
  obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := Packet06SpherePole.inverse_simple_expansion n hn hna z hz hd hs
  have hC := greenObservation_analyticAt n hn T (by linarith) z hz
  obtain ⟨D,hD,he⟩ := Packet06LaurentTransport.observation_expansion (H := Sector) (J := BallL2 T)
    (fun w => Ring.inverse (block n hn w)) R B (greenObservation n hn T) z hB hC hexp
  have hcross := crossing_nonzero n hn z hz hd hs
  have hN := ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd
  have hNball : physicalObservation n hn T z (numerator n hn z) ≠ 0 :=
    kernel_ball_observation_nonzero _ z 1 T hT _ (ModalWeightedMode.coefficient_support n hn) hN.2 hN.1
  have hnorm : reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z (numerator n hn z) ≠ 0 := by
    rw [norm_eq_sector_crossing]
    exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero hz (by norm_num))) hcross
  refine ⟨(greenObservation n hn T z).comp R,D,?_,hD,hnorm,?_,?_,he⟩
  · intro hzero
    have hv := congrArg (fun L : Sector →L[ℂ] BallL2 T =>
      L (blockDerivative n hn z (numerator n hn z))) hzero
    change greenObservation n hn T z (R (blockDerivative n hn z (numerator n hn z))) = 0 at hv
    rw [hform,map_smul,div_self hcross,one_smul] at hv
    exact smul_ne_zero (inv_ne_zero (pow_ne_zero 2 hz)) hNball hv
  · intro g
    change (z^2)⁻¹ • physicalObservation n hn T z (R g) = _
    rw [hform,map_smul,smul_smul,←source_pairing n hn z hz hd T hT g,norm_eq_sector_crossing]
    congr 1
    field_simp
    ring
  · exact Packet06LaurentTransport.observation_residue_limit (H := Sector) (J := BallL2 T)
      (fun w => Ring.inverse (block n hn w)) R (greenObservation n hn T) z hC.continuousAt hlim

end OQ14.Packet06GreenResidue
#print axioms OQ14.Packet06GreenResidue.greenObservation_analyticAt
#print axioms OQ14.Packet06GreenResidue.source_pairing
#print axioms OQ14.Packet06GreenResidue.source_pairing_physical
#print axioms OQ14.Packet06GreenResidue.norm_eq_sector_crossing
#print axioms OQ14.Packet06GreenResidue.actual_direct_green_pole
