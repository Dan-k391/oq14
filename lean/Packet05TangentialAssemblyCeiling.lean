import Packet05AssembledArrayCeiling

/-! Scalar iteration ceilings survive finite-direction assembly. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05TangentialAssemblyCeiling
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05AssembleTangentialArrays

theorem first_local_ceiling (D0 D1 : L2Vector) (L : ℝ) (hL : 0 ≤ L)
    (h0 : ∀ j, ‖D0 j‖ ≤ L) (h1 : ∀ j, ‖D1 j‖ ≤ L) :
    ∀ i j, ‖firstLocal D0 D1 i j‖ ≤ L := by
  intro i j
  fin_cases i
  · exact h0 j
  · exact h1 j
  · simpa [firstLocal] using hL

theorem second_local_ceiling (H00 H01 H10 H11 : L2Vector) (L : ℝ) (hL : 0 ≤ L)
    (h00 : ∀ j, ‖H00 j‖ ≤ L) (h01 : ∀ j, ‖H01 j‖ ≤ L)
    (h10 : ∀ j, ‖H10 j‖ ≤ L) (h11 : ∀ j, ‖H11 j‖ ≤ L) :
    ∀ i t j, ‖secondLocal H00 H01 H10 H11 i t j‖ ≤ L := by
  intro i t j
  fin_cases i <;> fin_cases t
  · exact h00 j
  · exact h01 j
  · simpa [secondLocal] using hL
  · exact h10 j
  · exact h11 j
  · simpa [secondLocal] using hL
  · simpa [secondLocal] using hL
  · simpa [secondLocal] using hL
  · simpa [secondLocal] using hL

end OQ14.Packet05TangentialAssemblyCeiling
#print axioms OQ14.Packet05TangentialAssemblyCeiling.first_local_ceiling
#print axioms OQ14.Packet05TangentialAssemblyCeiling.second_local_ceiling
