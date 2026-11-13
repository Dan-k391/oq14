import Packet06MaterialPole
import Packet06ExternalKernelReciprocity
import ConicalBallRestriction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalResidue
open Filter Metric Packet06SectorOperator Packet06LocalPencil Packet06MaterialPole
open Packet06MaterialSector (pencil)
open StaticCoefficient (Coefficient)
open scoped Topology
abbrev BallL2 := ConicalRungeBall.BallL2
abbrev VectorL2 := VectorFourier.VectorL2

/-- Actual incident dyadic response of an arbitrary source, weighted by the
material and orthogonally selected into the proven electric symmetry sector. -/
def incidentDatum (c : StaticCoefficient.Coefficient) (S J : ℝ) (z : ℂ) : VectorL2 →L[ℂ] Sector :=
  Sector.orthogonalProjection.comp ((Ring.inverse (StaticNewton.volumeBlock c)).comp
    ((StaticCoefficient.sqrtMultiplier c).comp (kernel z J S)))

def localIncident (J T : ℝ) (z : ℂ) : VectorL2 →L[ℂ] BallL2 T :=
  (ConicalBallRestriction.vector T).comp (kernel z J T)

def selectedScattered (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) : VectorL2 →L[ℂ] BallL2 T :=
  ((ConicalBallRestriction.vector T).comp (observation c S T z)).comp
    ((Ring.inverse (pencil c S z)).comp (incidentDatum c S J z))

theorem incidentDatum_analyticAt (c : StaticCoefficient.Coefficient) (S J : ℝ) (h : 0 ≤ S+J) (z : ℂ) :
    AnalyticAt ℂ (incidentDatum c S J) z := by
  let B : VectorL2 →L[ℂ] Sector := Sector.orthogonalProjection.comp
    ((Ring.inverse (StaticNewton.volumeBlock c)).comp (StaticCoefficient.sqrtMultiplier c))
  have hB : incidentDatum c S J = fun w : ℂ => B.comp (kernel w J S) := by
    funext w
    simp only [incidentDatum, B, ContinuousLinearMap.comp_assoc]
  rw [hB]
  exact (((ContinuousLinearMap.compL ℂ VectorL2 VectorL2 Sector) B).analyticAt
    (kernel z J S)).comp (f := fun w : ℂ => kernel w J S) (kernel_analyticAt J S h z)
theorem localIncident_analyticAt (J T : ℝ) (h : 0 ≤ T+J) (z : ℂ) :
    AnalyticAt ℂ (localIncident J T) z := by
  exact (((ContinuousLinearMap.compL ℂ VectorL2 VectorL2 (BallL2 T))
    (ConicalBallRestriction.vector T)).analyticAt (kernel z J T)).comp
      (f := fun w : ℂ => kernel w J T) (kernel_analyticAt J T h z)

/-- The selected physical scattered field has the actual rank-one residue
against every ambient L² source, with its projected forcing kept explicit. -/
theorem selected_residue_limit (c : StaticCoefficient.Coefficient) (ha : Packet06MaterialSymmetry.Axial c)
    (hm : Packet06MaterialSymmetry.Meridional c) (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (Packet06RankOneRepair.repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (Packet06RankOneRepair.repair (pencil c S z) w ψ)
      (deriv (pencil c S) z u)) ≠ 0) :
    let φ := ψ.comp (Ring.inverse (Packet06RankOneRepair.repair (pencil c S z) w ψ))
    ∃ R : VectorL2 →L[ℂ] BallL2 T,
      (∀ f, R f = (φ (incidentDatum c S J z f) / φ (deriv (pencil c S) z u)) •
        ConicalBallRestriction.vector T (response c z S T u)) ∧
      Tendsto (fun v => (v-z) • selectedScattered c S J T v) (𝓝[≠] z) (𝓝 R) := by
  dsimp only
  obtain ⟨R,B,hRn,hB,hform,hlim,hexp⟩ := actual_inverse_expansion c ha hm S hS hc z u w ψ hC hu hψ hd
  let C : ℂ → Sector →L[ℂ] BallL2 T := fun v =>
    (ConicalBallRestriction.vector T).comp (observation c S T v)
  let D : ℂ → VectorL2 →L[ℂ] Sector := incidentDatum c S J
  have hCa : AnalyticAt ℂ C z := by
    exact (((ContinuousLinearMap.compL ℂ Sector VectorL2 (BallL2 T))
      (ConicalBallRestriction.vector T)).analyticAt (observation c S T z)).comp
        (f := fun v : ℂ => observation c S T v)
        (observation_analyticAt c S T (by linarith) z)
  have hDa : AnalyticAt ℂ D z := incidentDatum_analyticAt c S J (by linarith) z
  have hleft := Packet06LaurentTransport.observation_residue_limit
    (fun v => Ring.inverse (pencil c S v)) R C z hCa.continuousAt hlim
  have hboth := (ContinuousLinearMap.compL ℂ VectorL2 Sector (BallL2 T)).continuous₂.tendsto
    ((C z).comp R,D z) |>.comp
      (hleft.prodMk_nhds (hDa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds))
  refine ⟨((C z).comp R).comp (D z), ?_, ?_⟩
  · intro f
    change C z (R (D z f)) = _
    rw [hform,map_smul]
    rfl
  · change Tendsto (fun v => (v-z) • (C v).comp ((Ring.inverse (pencil c S v)).comp (D v))) _ _
    simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_assoc] using hboth

#print axioms OQ14.Packet06ExternalResidue.incidentDatum_analyticAt
#print axioms OQ14.Packet06ExternalResidue.localIncident_analyticAt
#print axioms OQ14.Packet06ExternalResidue.selected_residue_limit
end OQ14.Packet06ExternalResidue
