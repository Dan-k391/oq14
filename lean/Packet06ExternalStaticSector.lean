import Packet06ExternalOverlap
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ExternalStaticSector
open Packet06SectorOperator
abbrev VectorL2 := VectorFourier.VectorL2

theorem static_inverse_mem_sector (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (g : VectorL2) (hg : g ∈ Sector) : Ring.inverse (StaticNewton.volumeBlock c) g ∈ Sector := by
  let B := StaticNewton.volumeBlock c
  have hrot (θ : ℝ) : ModalAxialRotation.action θ * B = B * ModalAxialRotation.action θ := by
    apply ContinuousLinearMap.ext
    intro f
    change ModalAxialRotation.action θ (StaticNewton.volumeBlock c f) = StaticNewton.volumeBlock c (ModalAxialRotation.action θ f)
    rw [StaticNewton.volumeBlock_eq]
    exact Packet06MaterialSymmetry.axial_static_comm c ha θ f
  have href : ModalMeridionalReflection.action * B = B * ModalMeridionalReflection.action := by
    apply ContinuousLinearMap.ext
    intro f
    change ModalMeridionalReflection.action (StaticNewton.volumeBlock c f) = StaticNewton.volumeBlock c (ModalMeridionalReflection.action f)
    rw [StaticNewton.volumeBlock_eq]
    exact Packet06MaterialSymmetry.meridional_static_comm c hm f
  refine ⟨?_,?_⟩
  · change Ring.inverse B g ∈ ModalAxialRotation.axialSector
    have hgax : g ∈ ModalAxialRotation.axialSector := hg.1
    simp only [ModalAxialRotation.axialSector,Submodule.mem_iInf,LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at hgax ⊢
    intro θ
    have he := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L g)
      (Packet06SymmetryPencil.comm_inverse B (ModalAxialRotation.action θ) (StaticNewton.volumeBlock_isUnit c) (hrot θ))
    change ModalAxialRotation.action θ (Ring.inverse B g) = Ring.inverse B (ModalAxialRotation.action θ g) at he
    simpa only [hgax θ] using he
  · have hgm : ModalMeridionalReflection.action g = g := by
      have h := hg.2
      change (ModalMeridionalReflection.action - 1) g = 0 at h
      simpa using sub_eq_zero.mp h
    change (ModalMeridionalReflection.action - 1) (Ring.inverse B g) = 0
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero]
    have he := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L g)
      (Packet06SymmetryPencil.comm_inverse B ModalMeridionalReflection.action (StaticNewton.volumeBlock_isUnit c) href)
    change ModalMeridionalReflection.action (Ring.inverse B g) = Ring.inverse B (ModalMeridionalReflection.action g) at he
    simpa only [hgm] using he

#print axioms OQ14.Packet06ExternalStaticSector.static_inverse_mem_sector
end OQ14.Packet06ExternalStaticSector
