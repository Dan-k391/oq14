import Packet06MaterialSector
import Packet06SchurPole
import Packet06KernelMaxwell

/-! A simple crossing of an actual symmetric material pencil gives its complete
selected-sector inverse pole and its nonzero physical electric observation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06MaterialPole
open Filter Metric Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open StaticCoefficient (Coefficient)
open Packet06MaterialSector (pencil)
open scoped Topology

def observation (c : Coefficient) (S T : ℝ) (z : ℂ) : Sector →L[ℂ] VectorL2 :=
  (Packet06LocalPencil.response c z S T).comp Sector.subtypeL

theorem observation_analyticAt (c : Coefficient) (S T : ℝ) (hST : 0 ≤ T+S) (z : ℂ) :
    AnalyticAt ℂ (observation c S T) z := by
  exact (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip Sector.subtypeL).analyticAt
    (Packet06LocalPencil.response c z S T)).comp
      (f := fun w : ℂ => Packet06LocalPencil.response c w S T)
      (Packet06LocalPencil.response_analyticAt c S T hST z)

theorem actual_inverse_expansion (c : Coefficient) (ha : Packet06MaterialSymmetry.Axial c)
    (hm : Packet06MaterialSymmetry.Meridional c) (S : ℝ) (hS : 0 ≤ S)
    (hc : ∀ x : FourierL2.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0) :
    let φ := ψ.comp (Ring.inverse (repair (pencil c S z) w ψ))
    ∃ (R : Sector →L[ℂ] Sector) (B : ℂ → Sector →L[ℂ] Sector),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, R x = (φ x / φ (deriv (pencil c S) z u)) • u) ∧
      Tendsto (fun v => (v-z) • Ring.inverse (pencil c S v)) (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ v in 𝓝[≠] z, Ring.inverse (pencil c S v) = (v-z)⁻¹ • R + B v) := by
  have hA := Packet06MaterialSector.pencil_analyticAt c S hS z
  have hk := (Packet06MaterialSector.pencil_kernel_actual c ha hm S hS hc z u).mpr hu
  have hi := repaired_inverse_vector (pencil c S z) u w ψ hC hk hψ
  have hs := scalar_zero (pencil c S z) u w ψ hC hk hψ
  have hder := Packet06SchurAnalytic.scalar_hasDerivAt (pencil c S) (deriv (pencil c S) z)
    w ψ z hA.differentiableAt.hasDerivAt hC
  have hds : deriv (fun v => scalar (pencil c S v) w ψ) z ≠ 0 := by
    rw [hder.deriv,hi]
    exact hd
  simpa only [hi] using Packet06SchurPole.simple_inverse_expansion (pencil c S) w ψ z hA hC hs hds

theorem actual_observed_expansion (c : Coefficient) (ha : Packet06MaterialSymmetry.Axial c)
    (hm : Packet06MaterialSymmetry.Meridional c) (S T : ℝ) (hS : 0 ≤ S) (hST : S ≤ T)
    (hc : ∀ x : FourierL2.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0) :
    let φ := ψ.comp (Ring.inverse (repair (pencil c S z) w ψ))
    ∃ (R : Sector →L[ℂ] VectorL2) (B : ℂ → Sector →L[ℂ] VectorL2),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, R x = (φ x / φ (deriv (pencil c S) z u)) • Packet06LocalPencil.response c z S T u) ∧
      Tendsto (fun v => (v-z) • (observation c S T v).comp (Ring.inverse (pencil c S v)))
        (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ v in 𝓝[≠] z, (observation c S T v).comp (Ring.inverse (pencil c S v)) =
        (v-z)⁻¹ • R + B v) := by
  obtain ⟨R,B,_,hB,hform,hlim,hexp⟩ := actual_inverse_expansion c ha hm S hS hc z u w ψ hC hu hψ hd
  have hObs := observation_analyticAt c S T (by linarith) z
  obtain ⟨D,hD,he⟩ := Packet06LaurentTransport.observation_expansion
    (fun v => Ring.inverse (pencil c S v)) R B (observation c S T) z hB hObs hexp
  have hune : (u : VectorL2) ≠ 0 := by
    intro h
    have hu0 : u = 0 := Subtype.ext h
    rw [hu0,map_zero] at hψ
    exact zero_ne_one hψ
  have hCu : observation c S T z u ≠ 0 :=
    Packet06Observation.kernel_observation_nonzero c z S T hST u hc hu hune
  refine ⟨(observation c S T z).comp R,D,?_,hD,?_,?_,he⟩
  · exact Packet06LaurentTransport.observed_residue_nonzero R (observation c S T z) u
      (ψ.comp (Ring.inverse (repair (pencil c S z) w ψ))) _ hd hform hCu
      (deriv (pencil c S) z u) hd
  · intro x
    exact Packet06LaurentTransport.observed_residue_form R (observation c S T z) u
      (ψ.comp (Ring.inverse (repair (pencil c S z) w ψ))) _ hform x
  · exact Packet06LaurentTransport.observation_residue_limit
      (fun v => Ring.inverse (pencil c S v)) R (observation c S T) z hObs.continuousAt hlim

end OQ14.Packet06MaterialPole
#print axioms OQ14.Packet06MaterialPole.observation_analyticAt
#print axioms OQ14.Packet06MaterialPole.actual_inverse_expansion
#print axioms OQ14.Packet06MaterialPole.actual_observed_expansion
