import Packet06SphereReduced
import Packet06WeightedPencilHolomorphic

/-! Continuous electric-sector compression, with actual restriction identified
only under the explicit invariant-subspace hypothesis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SectorFamily
open Filter Set Packet06SectorOperator
open scoped Topology

def compression : (VectorL2 →L[ℂ] VectorL2) →L[ℂ] (Sector →L[ℂ] Sector) :=
  (ContinuousLinearMap.compL ℂ Sector VectorL2 Sector Sector.orthogonalProjection).comp
    ((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip Sector.subtypeL)

theorem compression_actual (A : VectorL2 →L[ℂ] VectorL2)
    (hA : ∀ u ∈ Sector, A u ∈ Sector) (u : Sector) :
    ((compression A u : Sector) : VectorL2) = A u := by
  change ((Sector.orthogonalProjection (A u) : Sector) : VectorL2) = A u
  exact congrArg Subtype.val
    (Submodule.orthogonalProjection_mem_subspace_eq_self (⟨A u,hA u u.property⟩ : Sector))

theorem compression_analyticAt (A : ℂ → VectorL2 →L[ℂ] VectorL2) (z : ℂ)
    (hA : AnalyticAt ℂ A z) : AnalyticAt ℂ (fun v => compression (A v)) z := by
  have h1 := (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip Sector.subtypeL).analyticAt
    (A z)).comp (f := A) hA
  exact ((ContinuousLinearMap.compL ℂ Sector VectorL2 Sector).analyticAt_bilinear
    (Sector.orthogonalProjection,(A z).comp Sector.subtypeL)).comp
      (f := fun v : ℂ => (Sector.orthogonalProjection,(A v).comp Sector.subtypeL))
        (analyticAt_const.prod h1)

theorem compression_locally_uniform (A : ℕ → ℂ → VectorL2 →L[ℂ] VectorL2)
    (A₀ : ℂ → VectorL2 →L[ℂ] VectorL2) (U : Set ℂ) (hU : IsOpen U)
    (hA : TendstoLocallyUniformlyOn A A₀ atTop U) :
    TendstoLocallyUniformlyOn (fun n z => compression (A n z))
      (fun z => compression (A₀ z)) atTop U := by
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mpr
  intro K hKU hK
  exact compression.uniformContinuous.comp_tendstoUniformlyOn
    ((tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hA K hKU hK)

theorem sphere_pencil (n : ℝ) (hn : 1 < n) (z : ℂ) :
    compression (ComplexConvolutionAnalytic.pencil (ModalWeightedMode.coefficient n hn) z 1) =
      Packet06SphereReduced.pencil n hn z :=
  (Packet06SphereReduced.pencil_eq_compression n hn z).symm

theorem compression_kernel_actual (A : VectorL2 →L[ℂ] VectorL2)
    (hA : ∀ u ∈ Sector, A u ∈ Sector) (u : Sector) :
    compression A u = 0 ↔ A u = 0 := by
  constructor
  · intro hu
    have h := congrArg Subtype.val hu
    rwa [compression_actual A hA] at h
  · intro hu
    apply Subtype.ext
    rw [compression_actual A hA,hu]
    rfl

end OQ14.Packet06SectorFamily
#print axioms OQ14.Packet06SectorFamily.compression_actual
#print axioms OQ14.Packet06SectorFamily.compression_analyticAt
#print axioms OQ14.Packet06SectorFamily.compression_locally_uniform
#print axioms OQ14.Packet06SectorFamily.sphere_pencil
#print axioms OQ14.Packet06SectorFamily.compression_kernel_actual
