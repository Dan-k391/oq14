import Packet06RigidStateObservedPole

/-! The complete Euler-plus-translation frame preserves the actual selected
sector simple observed pole with an explicit transformed physical mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06FullFrameObservedPole
open Metric Maxwell Packet06SectorOperator Packet06PlacedKernel Packet06PlacedEquivalence
  Packet06RigidPencilState Packet06RigidStateSector

def full {c : StaticCoefficient.Coefficient} {R : ℝ} (θ φ : ℝ) (a : Space) (d : State c R) : State c R :=
  affine a (affine 0 (affine 0 (axial θ (affine 0 (affine 0 (axial φ (affine 0 d)))))))

theorem full_frame_observed_pole (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u) (θ φ : ℝ) (t : Space) :
    let d := full θ φ t (initial (placedCoefficient s a c) (R/s+‖a‖)
      (add_nonneg (div_nonneg hR hs.le) (norm_nonneg a))
      (Packet06PlacedPole.coefficient_support c R hc s hs a))
    Packet06GenericObservedPole.SimpleObservedPole d.material d.radius (embedding d s hs a)
      (pencil d s hs a) ((s : ℂ)*z) u := by
  exact Packet06RigidStateObservedPole.certified_observed_pole c ha hm R hR hc s hs a z u hcert _
end OQ14.Packet06FullFrameObservedPole
#print axioms OQ14.Packet06FullFrameObservedPole.full_frame_observed_pole
