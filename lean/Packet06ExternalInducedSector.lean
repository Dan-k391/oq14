import Packet06ProjectedSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalInducedSector
open MeasureTheory Metric Set Maxwell Packet06SectorOperator Packet06LocalPencil
open Packet06ExternalSymmetry Packet06ExternalOverlap Packet06ExternalFreeMaxwell
abbrev VectorL2 := VectorFourier.VectorL2

theorem support_multiplier_absorbed (c : StaticCoefficient.Coefficient) (S R : ℝ) (hSR : S ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (F : VectorL2) :
    StaticCoefficient.sqrtMultiplier c (StaticCoefficient.sqrtMultiplier (supportCoefficient R) F) =
      StaticCoefficient.sqrtMultiplier c F := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  have ha := StaticNewton.material_source_ae c (StaticCoefficient.sqrtMultiplier (supportCoefficient R) F) i
  have hb := StaticNewton.material_source_ae c F i
  have hs := StaticNewton.material_source_ae (supportCoefficient R) F i
  filter_upwards [ha,hb,hs,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c (StaticCoefficient.sqrtMultiplier (supportCoefficient R) F)) i,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c F) i,
    NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier (supportCoefficient R) F) i] with x ha hb hs hpa hpb hps
  rw [← hpa,← hpb,ha,hb,← hps,hs,supportCoefficient_spatial]
  by_cases hx : x ∈ closedBall (0 : Space) S
  · have hr := closedBall_subset_closedBall hSR hx
    simp [hr]
  · rw [hc x hx]
    simp

theorem weighted_free_mem_sector (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J : ℝ) (hS : 0 ≤ S)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (f : VectorL2) (hsector : f ∈ Sector)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 J → f (VectorFourier.coordinateMap x) = 0) :
    StaticCoefficient.sqrtMultiplier c (kernel z J S f) ∈ Sector := by
  let R := max S J
  let b := supportCoefficient R
  have hSR : S ≤ R := le_max_left _ _
  have hJR : J ≤ R := le_max_right _ _
  have hR : 0 ≤ R := hS.trans hSR
  have hfR : ∀ᵐ x : Space ∂volume, x ∉ closedBall 0 R → f (VectorFourier.coordinateMap x) = 0 := by
    filter_upwards [hf] with x hx hout
    exact hx (fun hin => hout (closedBall_subset_closedBall hJR hin))
  have hfixed : StaticCoefficient.sqrtMultiplier b f = f := supported_multiplier_identity R f hfR
  have hvol : ComplexConvolutionAnalytic.volumeBlock b z R f ∈ Sector :=
    volume_mem_sector b (supportCoefficient_axial R) (supportCoefficient_meridional R) R hR
      (supportCoefficient_support R) z f hsector
  have hK : StaticCoefficient.sqrtMultiplier b (kernel z R R f) ∈ Sector := by
    have he := congrArg (fun A : VectorL2 →L[ℂ] VectorL2 => A f) (weighted_block_eq b z R)
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,
      ContinuousLinearMap.mul_apply,hfixed] at he
    have he' : StaticCoefficient.sqrtMultiplier b (kernel z R R f) =
        f - ComplexConvolutionAnalytic.volumeBlock b z R f := by
      rw [he]
      abel
    rw [he']
    exact Sector.sub_mem hsector hvol
  have hweighted : StaticCoefficient.sqrtMultiplier c (kernel z R R f) ∈ Sector := by
    have h := sqrt_mem_sector c ha hm _ hK
    rwa [support_multiplier_absorbed c S R hSR hc] at h
  let U := 2*R-J
  have hSU : S ≤ U := by dsimp [U]; linarith
  have hcut := weighted_free_overlap c z J S U hSU f hc hf
  have hkernel : kernel z J U = kernel z R R := by
    unfold kernel
    have : U+J = R+R := by dsimp [U]; ring
    rw [this]
  rw [hkernel] at hcut
  rwa [← hcut]

#print axioms OQ14.Packet06ExternalInducedSector.support_multiplier_absorbed
#print axioms OQ14.Packet06ExternalInducedSector.weighted_free_mem_sector
end OQ14.Packet06ExternalInducedSector
