import Packet06ProjectedGlobal
import Packet06ProjectedPhysicalResidue
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ProjectedGlobalResidue
open MeasureTheory Metric Set Filter Maxwell Packet06SectorOperator Packet06MaterialSector
open Packet06ProjectedGreen Packet06ProjectedPhysicalResidue Packet06GlobalField Packet06RankOneRepair
open Packet06PhysicalNormalization KernelReciprocity
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

theorem global_mode_source_pair (c : StaticCoefficient.Coefficient) (S J : ℝ) (hSJ : S+1 ≤ J)
    (z : ℂ) (u f : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hf : ∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    vectorPair f (Packet06LocalPencil.response c z S J u) =
      ∫ x : Maxwell.Space, ∑ i : Fin 3, f (VectorFourier.coordinateMap x) i * electric c z S u x i := by
  rw [Packet06PhysicalPairing.vectorPair_physical]
  apply integral_congr_ae
  have he := ae_all_iff.mpr (fun i => (ae_restrict_iff' measurableSet_closedBall).mp
    (electric_matches_response c z S J hSJ u hc i))
  filter_upwards [he,hf] with x he hf
  by_cases hx : x ∈ closedBall (0 : Maxwell.Space) J
  · apply Finset.sum_congr rfl
    intro i hi
    rw [he i hx]
    rfl
  · rw [hf hx]
    simp

theorem global_mode_observation_ae (c : StaticCoefficient.Coefficient) (S T : ℝ) (hST : S+1 ≤ T)
    (z : ℂ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u) i : Maxwell.Space → ℂ)
      =ᵐ[volume.restrict (closedBall 0 T)] fun x => electric c z S u x i := by
  filter_upwards [ConicalBallRestriction.vector_ae T (Packet06LocalPencil.response c z S T u) i,
    ae_restrict_of_ae (NewtonL2.physicalCoordinate_ae (Packet06LocalPencil.response c z S T u) i),
    electric_matches_response c z S T hST u hc i] with x h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

/-- The physical pole couples arbitrary compact sources to the one global
outgoing mode, rather than merely to a local L² representative. -/
theorem residue_global_mode (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hSJ : S+1 ≤ J) (hST : S+1 ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ R : V →L[ℂ] BallL2 T,
      (∀ f, (∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) →
        R f = (-(∫ x : Maxwell.Space, ∑ i : Fin 3,
          f (VectorFourier.coordinateMap x) i * electric c z S u x i) / (2*z)) •
          ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u)) ∧
      (∀ i : Fin 3,
        (ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u) i : Maxwell.Space → ℂ)
          =ᵐ[volume.restrict (closedBall 0 T)] fun x => electric c z S u x i) ∧
      Tendsto (fun v => (v-z) • projectedGreen c S J T v) (𝓝[≠] z) (𝓝 R) := by
  obtain ⟨R,hR,hlim⟩ := projected_green_physical_residue c ha hm S J T hS (by linarith) (by linarith) hc z hz u w ψ hC hu hψ hd hN
  refine ⟨R,?_,fun i => global_mode_observation_ae c S T hST z u hc i,hlim⟩
  intro f hf
  rw [hR f hf]
  have h := global_mode_source_pair c S J hSJ z u f hc hf
  rw [Packet06PhysicalPairing.vectorPair_physical] at h
  rw [h]

#print axioms OQ14.Packet06ProjectedGlobalResidue.global_mode_source_pair
#print axioms OQ14.Packet06ProjectedGlobalResidue.global_mode_observation_ae
#print axioms OQ14.Packet06ProjectedGlobalResidue.residue_global_mode
end OQ14.Packet06ProjectedGlobalResidue
