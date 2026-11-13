import Packet06ProjectedPhysicalResidue
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ProjectedNonzero
open Filter MeasureTheory Metric Maxwell Packet06SectorOperator Packet06ExternalSymmetry
open Packet06SectorConjugate Packet06ProjectedModePairing Packet06ProjectedGreen
open Packet06MaterialSector Packet06RankOneRepair Packet06PhysicalNormalization KernelReciprocity
open scoped InnerProductSpace Topology
abbrev V := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

theorem conjugate_involutive (F : V) : conjugate (conjugate F) = F := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  filter_upwards [conjugate_ae (conjugate F) i,conjugate_ae F i] with x h1 h2
  rw [h1,h2]
  simp

theorem conjugate_support (F : V) (S : ℝ)
    (hF : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 S → F (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 S → conjugate F (VectorFourier.coordinateMap x) = 0 := by
  have ha := ae_all_iff.mpr (fun i => conjugate_ae F i)
  filter_upwards [ha,hF] with x ha hF hx
  apply PiLp.ext
  intro i
  rw [ha i,hF hx]
  simp

theorem physical_residue_nonzero (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hSJ : S ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ R : V →L[ℂ] BallL2 T, R ≠ 0 ∧
      Tendsto (fun v => (v-z) • projectedGreen c S J T v) (𝓝[≠] z) (𝓝 R) := by
  obtain ⟨R,hR,hlim⟩ := Packet06ProjectedPhysicalResidue.projected_green_physical_residue
    c ha hm S J T hS (by linarith) hST hc z hz u w ψ hC hu hψ hd hN
  let E := Packet06LocalPencil.response c z S J u
  let f := conjugate (StaticCoefficient.sqrtMultiplier c u)
  have hsource : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0 := by
    have h := conjugate_support (StaticCoefficient.sqrtMultiplier c u) S
      (material_source_supported c S hc u)
    filter_upwards [h] with x hx hout
    exact hx (fun hin => hout (closedBall_subset_closedBall hSJ hin))
  have hune : (u : V) ≠ 0 := by
    intro h
    have hu0 : u = 0 := Subtype.ext h
    rw [hu0,map_zero] at hψ
    exact zero_ne_one hψ
  have hE : StaticCoefficient.sqrtMultiplier c E = (u : V) := by
    change StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.response c z S J u) = _
    rw [Packet06Observation.weighted_observation_independent c z S J hSJ u hc]
    exact (Packet06LocalPencil.actual_kernel_transport c z S u hu).2
  have hpair : vectorPair f E = (‖(u : V)‖^2 : ℝ) := by
    rw [vectorPair_comm,vectorPair_inner]
    change ⟪conjugate (conjugate (StaticCoefficient.sqrtMultiplier c u)), E⟫_ℂ = _
    rw [conjugate_involutive,StaticCoefficient.sqrtMultiplier_symmetric,hE]
    simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (u : V))
  have hpairne : vectorPair f E ≠ 0 := by
    rw [hpair]
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hune))
  have hobs : ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u) ≠ 0 :=
    Packet06BallObservation.kernel_ball_observation_nonzero c z S T hST u hc hu hune
  refine ⟨R,?_,hlim⟩
  intro hzero
  have h := congrArg (fun L : V →L[ℂ] BallL2 T => L f) hzero
  change R f = 0 at h
  rw [hR f hsource] at h
  have hp : (∫ x : Maxwell.Space, ∑ i : Fin 3, f (VectorFourier.coordinateMap x) i * E (VectorFourier.coordinateMap x) i) ≠ 0 := by
    rw [← Packet06PhysicalPairing.vectorPair_physical]
    exact hpairne
  exact smul_ne_zero (div_ne_zero (neg_ne_zero.mpr hp) (mul_ne_zero (by norm_num) hz)) hobs h

#print axioms OQ14.Packet06ProjectedNonzero.conjugate_involutive
#print axioms OQ14.Packet06ProjectedNonzero.conjugate_support
#print axioms OQ14.Packet06ProjectedNonzero.physical_residue_nonzero
end OQ14.Packet06ProjectedNonzero
