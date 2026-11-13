import Packet06ProjectedModePairing
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ProjectedPhysicalResidue
open MeasureTheory Metric Filter Maxwell Packet06SectorOperator Packet06MaterialSector
open Packet06ProjectedGreen Packet06ProjectedModePairing Packet06RankOneRepair Packet06PhysicalNormalization
open KernelReciprocity
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

/-- Physical source/mode residue of the actual selected-sector Green operator.
The input source may be any compactly supported L² field; the Maxwell source
it solves for is its actual electric-sector projection. -/
theorem projected_green_physical_residue (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ R : VectorL2 →L[ℂ] BallL2 T,
      (∀ f, (∀ᵐ x : Maxwell.Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) →
        R f = (-(∫ x : Maxwell.Space, ∑ i : Fin 3,
          f (VectorFourier.coordinateMap x) i *
            (Packet06LocalPencil.response c z S J u) (VectorFourier.coordinateMap x) i) / (2*z)) •
          ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u)) ∧
      Tendsto (fun v => (v-z) • projectedGreen c S J T v) (𝓝[≠] z) (𝓝 R) := by
  obtain ⟨R,hR,hlim⟩ := projected_green_residue c ha hm S J T hS hJ hST hc z hz u w ψ hC hu hψ hd hN
  refine ⟨R,?_,hlim⟩
  intro f hf
  rw [hR]
  have hp := source_projection_pair c ha hm S J hS hc z u f hf
  rw [Packet06PhysicalPairing.vectorPair_physical,Packet06PhysicalPairing.vectorPair_physical] at hp
  rw [hp]

#print axioms OQ14.Packet06ProjectedPhysicalResidue.projected_green_physical_residue
end OQ14.Packet06ProjectedPhysicalResidue
