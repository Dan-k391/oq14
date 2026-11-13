import Packet06ExternalSectorMaxwell
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ExternalSymmetry
open MeasureTheory Metric Set Maxwell Packet06SectorOperator Packet06ExternalFreeMaxwell
abbrev VectorL2 := VectorFourier.VectorL2

theorem supportCoefficient_axial (R : ℝ) : Packet06MaterialSymmetry.Axial (supportCoefficient R) := by
  intro θ x
  rw [supportCoefficient_spatial,supportCoefficient_spatial]
  have h : ModalAxialRotation.rotation θ x ∈ closedBall (0 : Space) R ↔ x ∈ closedBall (0 : Space) R := by
    simp only [mem_closedBall,dist_zero_right,(ModalAxialRotation.rotation θ).norm_map]
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simp [hx,h.mpr hx]
  · simp [hx,mt h.mp hx]

theorem supportCoefficient_meridional (R : ℝ) : Packet06MaterialSymmetry.Meridional (supportCoefficient R) := by
  intro x
  rw [supportCoefficient_spatial,supportCoefficient_spatial]
  have h : ModalMeridionalReflection.reflection x ∈ closedBall (0 : Space) R ↔ x ∈ closedBall (0 : Space) R := by
    simp only [mem_closedBall,dist_zero_right,ModalMeridionalReflection.reflection.norm_map]
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simp [hx,h.mpr hx]
  · simp [hx,mt h.mp hx]

theorem sqrt_mem_sector (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (f : VectorL2) (hf : f ∈ Sector) : StaticCoefficient.sqrtMultiplier c f ∈ Sector := by
  refine ⟨?_,?_⟩
  · change StaticCoefficient.sqrtMultiplier c f ∈ ModalAxialRotation.axialSector
    have hax : f ∈ ModalAxialRotation.axialSector := hf.1
    simp only [ModalAxialRotation.axialSector,Submodule.mem_iInf,LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at hax ⊢
    intro θ
    rw [Packet06MaterialSymmetry.axial_sqrt_comm c ha θ f,hax θ]
  · have href : ModalMeridionalReflection.action f = f := by
      have h := hf.2
      change (ModalMeridionalReflection.action - 1) f = 0 at h
      simpa using sub_eq_zero.mp h
    change (ModalMeridionalReflection.action - 1) (StaticCoefficient.sqrtMultiplier c f) = 0
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero]
    rw [Packet06MaterialSymmetry.meridional_sqrt_comm c hm f,href]

theorem volume_mem_sector (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (f : VectorL2) (hf : f ∈ Sector) :
    ComplexConvolutionAnalytic.volumeBlock c z R f ∈ Sector := by
  refine ⟨?_,?_⟩
  · change ComplexConvolutionAnalytic.volumeBlock c z R f ∈ ModalAxialRotation.axialSector
    have hax : f ∈ ModalAxialRotation.axialSector := hf.1
    simp only [ModalAxialRotation.axialSector,Submodule.mem_iInf,LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at hax ⊢
    intro θ
    have he := congrArg (fun A : VectorL2 →L[ℂ] VectorL2 => A f)
      (Packet06SymmetryVolume.axial_volume_comm c ha R hR hc θ z)
    change ModalAxialRotation.action θ (ComplexConvolutionAnalytic.volumeBlock c z R f) =
      ComplexConvolutionAnalytic.volumeBlock c z R (ModalAxialRotation.action θ f) at he
    simpa only [hax θ] using he
  · have href : ModalMeridionalReflection.action f = f := by
      have h := hf.2
      change (ModalMeridionalReflection.action - 1) f = 0 at h
      simpa using sub_eq_zero.mp h
    change (ModalMeridionalReflection.action - 1) (ComplexConvolutionAnalytic.volumeBlock c z R f) = 0
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero]
    have he := congrArg (fun A : VectorL2 →L[ℂ] VectorL2 => A f)
      (Packet06SymmetryVolume.meridional_volume_comm c hm R hR hc z)
    change ModalMeridionalReflection.action (ComplexConvolutionAnalytic.volumeBlock c z R f) =
      ComplexConvolutionAnalytic.volumeBlock c z R (ModalMeridionalReflection.action f) at he
    simpa only [href] using he

#print axioms OQ14.Packet06ExternalSymmetry.volume_mem_sector
#print axioms OQ14.Packet06ExternalSymmetry.supportCoefficient_axial
#print axioms OQ14.Packet06ExternalSymmetry.supportCoefficient_meridional
#print axioms OQ14.Packet06ExternalSymmetry.sqrt_mem_sector
end OQ14.Packet06ExternalSymmetry
