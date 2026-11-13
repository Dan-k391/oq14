import Packet06ExternalInducedSector
import Packet06ExternalGreen
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ProjectedGreen
open MeasureTheory Metric Filter Maxwell Packet06SectorOperator Packet06MaterialSector
open Packet06ExternalResidue Packet06ExternalGreen Packet06ExternalHybridEquation
open Packet06ExternalInducedSector Packet06ProjectedSupport Packet06ExternalSectorMaxwell
open Packet06RankOneRepair Packet06PhysicalNormalization ComplexResponseTests DynamicSource
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2
abbrev BallL2 := ConicalRungeBall.BallL2

def project : VectorL2 →L[ℂ] VectorL2 := Sector.subtypeL.comp Sector.orthogonalProjection

def projectedGreen (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) :
    VectorL2 →L[ℂ] BallL2 T := (residueRepresentative c S J T z).comp project

def projectedField (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) (f : VectorL2) : VectorL2 :=
  hybridField c S J T z (project f)

theorem projected_restriction (c : StaticCoefficient.Coefficient) (S J T : ℝ) (z : ℂ) (f : VectorL2) :
    ConicalBallRestriction.vector T (projectedField c S J T z f) = projectedGreen c S J T z f := by
  exact hybrid_restriction c S J T z (project f)

/-- The selected source solution satisfies Maxwell with the exact projected
current, even when the original compact source has no symmetry. -/
theorem projected_source_maxwell (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (hunit : IsUnit (pencil c S z)) (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (φ : Test) (hφ : tsupport (φ.val : Space → ℂ) ⊆ closedBall 0 T) :
    Packet06GreenSource.maxwellTest c z i φ (projectedField c S J T z f) =
      testPair i φ.val (project f) := by
  have hp : project f ∈ Sector := (Sector.orthogonalProjection f).property
  have hs : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → (project f) (VectorFourier.coordinateMap x) = 0 :=
    projected_supported J f hf
  exact induced_sector_maxwell_test c ha hm S J T hS hJ hST hc z hz hunit (project f) hs
    (weighted_free_mem_sector c ha hm S J hS hc z (project f) hp hs) i φ hφ

/-- The actual projected-source Green operator has the physical normalized
residue on every ambient source; its source coupling uses the explicitly
projected current and the actual mode representative on the source ball. -/
theorem projected_green_residue (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (hN : reciprocalNorm c S z u = 1) :
    ∃ R : VectorL2 →L[ℂ] BallL2 T,
      (∀ f, R f =
        (-(∫ x : Space, ∑ i : Fin 3,
          (project f) (VectorFourier.coordinateMap x) i *
            (Packet06LocalPencil.response c z S J u) (VectorFourier.coordinateMap x) i) / (2*z)) •
          ConicalBallRestriction.vector T (Packet06LocalPencil.response c z S T u)) ∧
      Tendsto (fun v => (v-z) • projectedGreen c S J T v) (𝓝[≠] z) (𝓝 R) := by
  obtain ⟨R,hR,hlim⟩ := selected_residue_representative c ha hm S J T hS hJ hST hc z hz u w ψ hC hu hψ hd hN
  let B : (VectorL2 →L[ℂ] BallL2 T) →L[ℂ] (VectorL2 →L[ℂ] BallL2 T) :=
    (ContinuousLinearMap.compL ℂ VectorL2 VectorL2 (BallL2 T)).flip project
  refine ⟨B R,?_,?_⟩
  · intro f
    exact hR (project f)
  · have ht := B.continuous.continuousAt.tendsto.comp hlim
    simpa only [projectedGreen,B,ContinuousLinearMap.compL_apply,ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.smul_comp,Function.comp_def] using ht

/-- The projected-source Maxwell equation holds throughout a punctured
neighborhood of the certified selected-sector pole. -/
theorem projected_source_punctured (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (u w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hC : IsUnit (repair (pencil c S z) w ψ))
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (hψ : ψ u = 1)
    (hd : ψ (Ring.inverse (repair (pencil c S z) w ψ) (deriv (pencil c S) z u)) ≠ 0)
    (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    ∀ᶠ v in 𝓝[≠] z, ∀ (i : Fin 3) (φ : Test),
      tsupport (φ.val : Space → ℂ) ⊆ closedBall 0 T →
      Packet06GreenSource.maxwellTest c v i φ (projectedField c S J T v f) = testPair i φ.val (project f) := by
  let A := pencil c S
  have hA : AnalyticAt ℂ A z := pencil_analyticAt c S hS z
  have hk : A z u = 0 := (pencil_kernel_actual c ha hm S hS hc z u).mpr hu
  have hrep : Ring.inverse (repair (A z) w ψ) w = u :=
    Packet06RankOneRepair.repaired_inverse_vector (A z) u w ψ hC hk hψ
  have hder := Packet06SchurAnalytic.scalar_hasDerivAt A (deriv A z) w ψ z hA.differentiableAt.hasDerivAt hC
  have hd' : ψ (Ring.inverse (repair (A z) w ψ)
      (deriv A z (Ring.inverse (repair (A z) w ψ) w))) ≠ 0 := by rw [hrep]; exact hd
  have hunits := Packet06SchurPole.punctured_units A w ψ z _ hA hC hder hd'
  have hnz : ∀ᶠ v in 𝓝[≠] z, v ≠ 0 :=
    nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hz)
  filter_upwards [hunits,hnz] with v hv hvz
  exact fun i φ hφ => projected_source_maxwell c ha hm S J T hS hJ hST hc v hvz hv f hf i φ hφ

#print axioms OQ14.Packet06ProjectedGreen.projected_source_punctured
#print axioms OQ14.Packet06ProjectedGreen.projected_restriction
#print axioms OQ14.Packet06ProjectedGreen.projected_source_maxwell
#print axioms OQ14.Packet06ProjectedGreen.projected_green_residue
end OQ14.Packet06ProjectedGreen
