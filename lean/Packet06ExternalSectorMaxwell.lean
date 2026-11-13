import Packet06ExternalStaticSector
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalSectorMaxwell
open MeasureTheory Metric Maxwell Packet06SectorOperator Packet06MaterialSector
open Packet06ExternalResidue Packet06ExternalHybridEquation Packet06ExternalOverlap
open Packet06ExternalStaticSector ComplexResponseTests DynamicSource
abbrev VectorL2 := VectorFourier.VectorL2

theorem induced_sector_maxwell_test (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J T : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J) (hST : S ≤ T)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (hunit : IsUnit (pencil c S z)) (f : VectorL2)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0)
    (hsector : StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.kernel z J S f) ∈ Sector)
    (i : Fin 3) (φ : Test) (hφ : tsupport (φ.val : Space → ℂ) ⊆ closedBall 0 T) :
    Packet06GreenSource.maxwellTest c z i φ (hybridField c S J T z f) = testPair i φ.val f := by
  let g := StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.kernel z J S f)
  let v := Ring.inverse (StaticNewton.volumeBlock c) g
  have hv : v ∈ Sector := static_inverse_mem_sector c ha hm g hsector
  have hp : (Sector.orthogonalProjection v : VectorL2) = v :=
    congrArg Subtype.val (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨v,hv⟩ : Sector))
  let q : Sector := Ring.inverse (pencil c S z) (incidentDatum c S J z f)
  have hq : pencil c S z q = incidentDatum c S J z f := by
    have h := congrArg (fun L : Sector →L[ℂ] Sector => L (incidentDatum c S J z f))
      (Ring.mul_inverse_cancel _ hunit)
    simpa only [ContinuousLinearMap.mul_apply,ContinuousLinearMap.one_apply] using h
  have hvol : ComplexConvolutionAnalytic.volumeBlock c z S q = g := by
    rw [ComplexConvolutionAnalytic.volumeBlock_factor]
    change StaticNewton.volumeBlock c (ComplexConvolutionAnalytic.pencil c z S q) = g
    rw [← pencil_actual c ha hm S hS hc z q, hq]
    change StaticNewton.volumeBlock c (Sector.orthogonalProjection v : VectorL2) = g
    rw [hp]
    change (StaticNewton.volumeBlock c * Ring.inverse (StaticNewton.volumeBlock c)) g = g
    rw [Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c),ContinuousLinearMap.one_apply]
  have he := hybrid_maxwell_test c S J T hS hJ hST hc z hz f hf i φ hφ
  change _ = _ + testPair i φ.val (StaticCoefficient.sqrtMultiplier c
    (ComplexConvolutionAnalytic.volumeBlock c z S q - _)) at he
  rw [hvol,weighted_free_overlap c z J S T hST f hc hf,sub_self,map_zero,map_zero,add_zero] at he
  exact he

#print axioms OQ14.Packet06ExternalSectorMaxwell.induced_sector_maxwell_test
end OQ14.Packet06ExternalSectorMaxwell
