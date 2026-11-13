import Packet06SectorConjugate
import Packet06ExternalKernelReciprocity
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06ExternalPairing
open MeasureTheory Packet06SectorOperator Packet06ExternalLeft Packet06ExternalResidue
open KernelReciprocity Packet06SectorConjugate

abbrev VectorL2 := VectorFourier.VectorL2

theorem static_mem_sector (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (u : Sector) : StaticNewton.volumeBlock c u ∈ Sector := by
  rw [StaticNewton.volumeBlock_eq]
  refine ⟨?_,?_⟩
  · change StaticCoefficient.weightedBlock c u ∈ ModalAxialRotation.axialSector
    have hax : (u : VectorL2) ∈ ModalAxialRotation.axialSector := u.property.1
    simp only [ModalAxialRotation.axialSector,Submodule.mem_iInf,LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at hax ⊢
    intro θ
    rw [Packet06MaterialSymmetry.axial_static_comm c ha θ u,hax θ]
  · have href : ModalMeridionalReflection.action (u : VectorL2) = u := by
      have h := u.property.2
      change (ModalMeridionalReflection.action - 1) (u : VectorL2) = 0 at h
      simpa using sub_eq_zero.mp h
    change (ModalMeridionalReflection.action - 1) (StaticCoefficient.weightedBlock c u) = 0
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero]
    rw [Packet06MaterialSymmetry.meridional_static_comm c hm u,href]

/-- The selected preconditioned datum pairs with the true mode as the physical
unconjugated pairing of the arbitrary source with its local mode response. -/
theorem incident_physical_pairing (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J : ℝ) (hSJ : 0 ≤ S+J) (z : ℂ) (u : Sector) (f : VectorL2) :
    physicalLeft c u (incidentDatum c S J z f) =
      vectorPair f (Packet06LocalPencil.response c z S J u) := by
  let B := StaticNewton.volumeBlock c
  let g := StaticCoefficient.sqrtMultiplier c (Packet06LocalPencil.kernel z J S f)
  let v := Ring.inverse B g
  have hBu : B (u : VectorL2) ∈ Sector := static_mem_sector c ha hm u
  change vectorPair (B (Sector.orthogonalProjection v : VectorL2)) u = _
  rw [NewtonReciprocity.static_volumeBlock_reciprocity,
    projection_pair_right v (B u) hBu, ← NewtonReciprocity.static_volumeBlock_reciprocity]
  have hBv : B v = g := by
    change (B * Ring.inverse B) g = g
    rw [Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c),ContinuousLinearMap.one_apply]
  rw [hBv]
  exact Packet06ExternalKernelReciprocity.incident_mode_pairing c S J hSJ z f u

#print axioms OQ14.Packet06ExternalPairing.static_mem_sector
#print axioms OQ14.Packet06ExternalPairing.incident_physical_pairing
end OQ14.Packet06ExternalPairing
