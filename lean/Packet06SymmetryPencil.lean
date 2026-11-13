import Packet06SymmetryVolume
import Packet06SectorOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SymmetryPencil
open Filter Metric Set OQ14.StaticCoefficient OQ14.Packet06SectorOperator
open scoped Topology
abbrev V := VectorFourier.VectorL2
abbrev Space := FourierL2.Space

theorem comm_inverse (B T : V →L[ℂ] V) (hu : IsUnit B) (h : T*B=B*T) :
    T*Ring.inverse B = Ring.inverse B*T := by
  have hl := Ring.inverse_mul_cancel B hu
  have hr := Ring.mul_inverse_cancel B hu
  calc
    T*Ring.inverse B = (Ring.inverse B*B)*T*Ring.inverse B := by rw [hl,one_mul]
    _ = Ring.inverse B*(T*B)*Ring.inverse B := by rw [h]; noncomm_ring
    _ = Ring.inverse B*T := by rw [mul_assoc (Ring.inverse B) (T*B) (Ring.inverse B), mul_assoc T B (Ring.inverse B), hr, mul_one]

theorem action_pencil_comm (c : Coefficient) (R : ℝ) (T : V →L[ℂ] V) (z : ℂ)
    (hstatic : T*weightedBlock c = weightedBlock c*T)
    (hvolume : T*ComplexConvolutionAnalytic.volumeBlock c z R =
      ComplexConvolutionAnalytic.volumeBlock c z R*T) :
    T*ComplexConvolutionAnalytic.pencil c z R = ComplexConvolutionAnalytic.pencil c z R*T := by
  have hi := comm_inverse (weightedBlock c) T (weightedBlock_isUnit c) hstatic
  have hf := ComplexConvolutionAnalytic.volumeBlock_factor c z R
  rw [StaticNewton.volumeBlock_eq] at hf
  have hp : ComplexConvolutionAnalytic.pencil c z R =
      Ring.inverse (weightedBlock c) * ComplexConvolutionAnalytic.volumeBlock c z R := by
    rw [hf,←mul_assoc,Ring.inverse_mul_cancel _ (weightedBlock_isUnit c),one_mul]
  rw [hp, ←mul_assoc, hi, mul_assoc, hvolume, ←mul_assoc]

theorem axial_pencil_comm (c : Coefficient) (hc : Packet06MaterialSymmetry.Axial c)
    (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (θ : ℝ) (z : ℂ) :
    ModalAxialRotation.action θ * ComplexConvolutionAnalytic.pencil c z R =
      ComplexConvolutionAnalytic.pencil c z R * ModalAxialRotation.action θ := by
  apply action_pencil_comm c R _ z
  · apply ContinuousLinearMap.ext
    intro u
    exact Packet06MaterialSymmetry.axial_static_comm c hc θ u
  · exact Packet06SymmetryVolume.axial_volume_comm c hc R hR hsupp θ z

theorem meridional_pencil_comm (c : Coefficient) (hc : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) :
    ModalMeridionalReflection.action * ComplexConvolutionAnalytic.pencil c z R =
      ComplexConvolutionAnalytic.pencil c z R * ModalMeridionalReflection.action := by
  apply action_pencil_comm c R _ z
  · apply ContinuousLinearMap.ext
    intro u
    exact Packet06MaterialSymmetry.meridional_static_comm c hc u
  · exact Packet06SymmetryVolume.meridional_volume_comm c hc R hR hsupp z

theorem pencil_mem_electricSector (c : Coefficient) (ha : Packet06MaterialSymmetry.Axial c)
    (hm : Packet06MaterialSymmetry.Meridional c) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (u : V) (hu : u ∈ Sector) : ComplexConvolutionAnalytic.pencil c z R u ∈ Sector := by
  refine ⟨?_,?_⟩
  · change ComplexConvolutionAnalytic.pencil c z R u ∈ ModalAxialRotation.axialSector
    have hax : u ∈ ModalAxialRotation.axialSector := hu.1
    simp only [ModalAxialRotation.axialSector,Submodule.mem_iInf,LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at hax ⊢
    intro θ
    have h := congrArg (fun L : V →L[ℂ] V => L u) (axial_pencil_comm c ha R hR hsupp θ z)
    change ModalAxialRotation.action θ (ComplexConvolutionAnalytic.pencil c z R u) =
      ComplexConvolutionAnalytic.pencil c z R (ModalAxialRotation.action θ u) at h
    simpa only [hax θ] using h
  · have hf : ModalMeridionalReflection.action u = u := by
      have h := hu.2
      change (ModalMeridionalReflection.action - 1) u = 0 at h
      simpa using sub_eq_zero.mp h
    change (ModalMeridionalReflection.action - 1) (ComplexConvolutionAnalytic.pencil c z R u) = 0
    have h := congrArg (fun L : V →L[ℂ] V => L u) (meridional_pencil_comm c hm R hR hsupp z)
    change ModalMeridionalReflection.action (ComplexConvolutionAnalytic.pencil c z R u) =
      ComplexConvolutionAnalytic.pencil c z R (ModalMeridionalReflection.action u) at h
    simpa only [hf,ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] using h
#print axioms OQ14.Packet06SymmetryPencil.comm_inverse
#print axioms OQ14.Packet06SymmetryPencil.action_pencil_comm
#print axioms OQ14.Packet06SymmetryPencil.axial_pencil_comm
#print axioms OQ14.Packet06SymmetryPencil.meridional_pencil_comm
#print axioms OQ14.Packet06SymmetryPencil.pencil_mem_electricSector
end OQ14.Packet06SymmetryPencil
