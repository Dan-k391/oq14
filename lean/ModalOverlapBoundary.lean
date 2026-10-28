import ModalInterface

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalOverlapBoundary
open Complex OQ14.ModalAlgebra OQ14.ModalInterface

theorem regular_boundary_wronskian_ne_zero (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet 1 n z = 0) :
    n * psi 1 (n*z) * psiD 1 z - psi 1 z * psiD 1 (n*z) ≠ 0 := by
  intro hw
  have hout := regular_outgoing_wronskian 1 z hz
  have hint := regular_state_nonzero 1 (n*z) (mul_ne_zero hn hz)
  unfold tmDet at hd
  have hA : n * psi 1 (n*z) = 0 := by
    have h : I * (n * psi 1 (n*z)) = 0 := by
      linear_combination -(n * psi 1 (n*z)) * hout + psi 1 z * hd - xi 1 z * hw
    exact (mul_eq_zero.mp h).resolve_left I_ne_zero
  have hB : psiD 1 (n*z) = 0 := by
    have h : I * psiD 1 (n*z) = 0 := by
      linear_combination -psiD 1 (n*z) * hout + psiD 1 z * hd - xiD 1 z * hw
    exact (mul_eq_zero.mp h).resolve_left I_ne_zero
  exact hint.elim (fun h => h ((mul_eq_zero.mp hA).resolve_left hn)) (fun h => h hB)
end OQ14.ModalOverlapBoundary
#print axioms OQ14.ModalOverlapBoundary.regular_boundary_wronskian_ne_zero


