import Packet06ExternalGreen
import Packet06ExternalFreeMaxwell
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ExternalHybridEquation
open MeasureTheory Metric Maxwell Packet06SectorOperator Packet06MaterialSector
open Packet06ExternalResidue Packet06LocalPencil Packet06GreenSource ComplexResponseTests DynamicSource
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

def hybridField (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) (f : VectorL2) : VectorL2 :=
  (z^2)⁻¹ • (kernel z J T f + response c z S T
    (Ring.inverse (pencil c S z) (incidentDatum c S J z f)))

/-- Exact actual Maxwell equation of the hybrid residue representative. The
additional term is kept explicitly and need not vanish for arbitrary sources. -/
theorem hybrid_maxwell_test (c : StaticCoefficient.Coefficient) (S J T : ℝ)
    (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (φ : Test) (hφ : tsupport (φ.val : Space → ℂ) ⊆ closedBall 0 T) :
    maxwellTest c z i φ (hybridField c S J T z f) =
      testPair i φ.val f + testPair i φ.val (StaticCoefficient.sqrtMultiplier c
        (ComplexConvolutionAnalytic.volumeBlock c z S
          (Ring.inverse (pencil c S z) (incidentDatum c S J z f)) -
          StaticCoefficient.sqrtMultiplier c (kernel z J T f))) := by
  let q : VectorL2 := Ring.inverse (pencil c S z) (incidentDatum c S J z f)
  have hfree := Packet06ExternalFreeMaxwell.free_maxwell_test z hz J T (by linarith) f hf i φ hφ
  have hsc := solved_maxwell_test c z S T hST (by linarith) q
    (ComplexConvolutionAnalytic.volumeBlock c z S q) hc rfl i φ hφ
  have hz2 : z^2 ≠ 0 := pow_ne_zero 2 hz
  change maxwellTest c z i φ ((z^2)⁻¹ • (kernel z J T f + response c z S T q)) = _
  simp only [maxwellTest,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.mul_apply,map_smul,map_add,map_sub,smul_eq_mul] at hsc ⊢
  simp only [map_smul,smul_eq_mul] at hfree
  field_simp at hfree ⊢
  linear_combination hsc + hfree

/-- The bounded-ball residue representative is the restriction of the actual
L² hybrid field used in the explicit Maxwell identity. -/
theorem hybrid_restriction (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) (f : VectorL2) :
    ConicalBallRestriction.vector T (hybridField c S J T z f) =
      Packet06ExternalGreen.residueRepresentative c S J T z f := by
  simp only [hybridField,Packet06ExternalGreen.residueRepresentative,localIncident,selectedScattered,
    Packet06MaterialPole.observation,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply,map_smul,map_add]
  rfl

#print axioms OQ14.Packet06ExternalHybridEquation.hybrid_restriction
#print axioms OQ14.Packet06ExternalHybridEquation.hybrid_maxwell_test
end OQ14.Packet06ExternalHybridEquation
