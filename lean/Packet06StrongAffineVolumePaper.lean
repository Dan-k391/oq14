import Packet06StrongAffineVolumeFamily

/-! Literal permittivity-ceiling parameterization of the complete core
conclusion; the scalar square-root identity converts every K² bound to ε. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06StrongAffineVolumePaper
open Set Maxwell Packet07PlaneCoordinates
abbrev Space := Maxwell.Space

theorem sqrt_gt_one (ε : ℝ) (hε : 1 < ε) : 1 < Real.sqrt ε := by
  have hε0 : 0 ≤ ε := le_trans zero_le_one hε.le
  have hs := Real.sq_sqrt hε0
  have hp := Real.sqrt_nonneg ε
  nlinarith

theorem sqrt_ceiling (ε : ℝ) (hε : 1 < ε) : (Real.sqrt ε)^2=ε :=
  Real.sq_sqrt (le_trans zero_le_one hε.le)

theorem literal_bound (ε value : ℝ) (hε : 1 < ε) (hv : value ≤ (Real.sqrt ε)^2) : value ≤ ε := by
  rwa [sqrt_ceiling ε hε] at hv

def exists_strong_affine_volume_family (N : ℕ) (ε target Q ell : ℝ)
    (hε : 1 < ε) (ht : 0 < target) (hQ : 0 ≤ Q) (hell : 0 < ell)
    (normal origin : Space) (hnormal : ‖normal‖=1) (O : Set Space) (hO : IsOpen O)
    (hne : (affinePlane normal origin ∩ O).Nonempty) :=
  Packet06StrongAffineVolumeFamily.exists_strong_affine_volume_family N (Real.sqrt ε)
    target Q ell (sqrt_gt_one ε hε) ht hQ hell normal origin hnormal O hO hne
end OQ14.Packet06StrongAffineVolumePaper
#print axioms OQ14.Packet06StrongAffineVolumePaper.sqrt_gt_one
#print axioms OQ14.Packet06StrongAffineVolumePaper.sqrt_ceiling
#print axioms OQ14.Packet06StrongAffineVolumePaper.literal_bound
#print axioms OQ14.Packet06StrongAffineVolumePaper.exists_strong_affine_volume_family
