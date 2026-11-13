import Packet06GreenResidue

/-! The sector Green operator is an actual local Maxwell source solution.
This bridges the physical PDE and the bounded-ball Laurent operator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06GreenSector
open MeasureTheory Metric Filter Packet06SectorOperator Packet06Observation
open Packet06BallObservation Packet06GreenResidue Packet06GreenSource ComplexResponseTests DynamicSource
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def greenField (n : ℝ) (hn : 1 < n) (T : ℝ) (z : ℂ) (g : Sector) : VectorL2 :=
  (z^2)⁻¹ • observation n hn T z (Ring.inverse (block n hn z) g)

theorem greenField_restriction (n : ℝ) (hn : 1 < n) (T : ℝ) (z : ℂ) (g : Sector) :
    ConicalBallRestriction.vector T (greenField n hn T z g) =
      ((greenObservation n hn T z).comp (Ring.inverse (block n hn z))) g := by
  change ConicalBallRestriction.vector T ((z^2)⁻¹ • observation n hn T z (Ring.inverse (block n hn z) g)) = _
  rw [map_smul]
  rfl

theorem sector_inverse_solves (n : ℝ) (hn : 1 < n) (z : ℂ)
    (hu : IsUnit (block n hn z)) (g : Sector) :
    ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1
      (Ring.inverse (block n hn z) g) = (g : VectorL2) := by
  have h := congrArg (fun L : Sector →L[ℂ] Sector => L g) (Ring.mul_inverse_cancel _ hu)
  have hh := congrArg (fun u : Sector => (u : VectorL2)) h
  exact hh

theorem greenField_maxwell_test (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hu : IsUnit (block n hn z)) (T : ℝ) (hT : 1 ≤ T)
    (g : Sector) (i : Fin 3) (f : Test)
    (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    maxwellTest (ModalWeightedMode.coefficient n hn) z i f (greenField n hn T z g) =
      testPair i f.val (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) g) := by
  have he := sector_inverse_solves n hn z hu g
  change maxwellTest _ z i f ((z^2)⁻¹ • Packet06LocalPencil.response _ z 1 T
    ((Ring.inverse (block n hn z) g : Sector) : VectorL2)) = _
  rw [map_smul,solved_maxwell_test _ z 1 T hT (by linarith) _ g
    (ModalWeightedMode.coefficient_support n hn) he i f hf,smul_eq_mul,
    ←mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hz),one_mul]

theorem greenField_physical (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hu : IsUnit (block n hn z)) (T : ℝ) (hT : 1 ≤ T)
    (g : Sector) (i : Fin 3) (f : Test)
    (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T) :
    (∑ l : Fin 3, ∫ x : Maxwell.Space,
      greenField n hn T z g (VectorFourier.coordinateMap x) l * (testPartial l (testPartial i f)).val x) -
    (∑ l : Fin 3, ∫ x : Maxwell.Space,
      greenField n hn T z g (VectorFourier.coordinateMap x) i * (testPartial l (testPartial l f)).val x) -
    z^2*(∫ x : Maxwell.Space, (1+((ModalWeightedMode.coefficient n hn).value
      (VectorFourier.coordinateMap x) : ℂ))*
      greenField n hn T z g (VectorFourier.coordinateMap x) i*f.val x) =
    ∫ x : Maxwell.Space, (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) g)
      (VectorFourier.coordinateMap x) i*f.val x := by
  rw [←Packet06GreenPhysical.maxwell_test_physical,greenField_maxwell_test n hn z hz hu T hT g i f hf,
    testPair_integral]

theorem punctured_actual_source (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 1 ≤ T) :
    ∀ᶠ w in 𝓝[≠] z, ∀ (g : Sector) (i : Fin 3) (f : Test),
      tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T →
        maxwellTest (ModalWeightedMode.coefficient n hn) w i f (greenField n hn T w g) =
          testPair i f.val (StaticCoefficient.sqrtMultiplier (ModalWeightedMode.coefficient n hn) g) := by
  have hnz : ∀ᶠ w in 𝓝[≠] z, w ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hz)
  filter_upwards [block_punctured_isUnit n hn z,hnz] with w hw hwz
  exact fun g i f hf => greenField_maxwell_test n hn w hwz hw T hT g i f hf

end OQ14.Packet06GreenSector
#print axioms OQ14.Packet06GreenSector.greenField_restriction
#print axioms OQ14.Packet06GreenSector.sector_inverse_solves
#print axioms OQ14.Packet06GreenSector.greenField_maxwell_test
#print axioms OQ14.Packet06GreenSector.greenField_physical
#print axioms OQ14.Packet06GreenSector.punctured_actual_source
