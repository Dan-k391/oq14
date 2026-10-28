import ModalWeak

noncomputable section
set_option autoImplicit false

namespace OQ14.ModalDriven

open Complex OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalMatching
  OQ14.ModalInterface OQ14.ModalOrigin OQ14.ModalDipole OQ14.ModalProfiles

def incidentState (k : ℂ) : Amplitudes := (psi 1 k, psiD 1 k)
def numerator (n k : ℂ) : Amplitudes := adjugate 1 n k (incidentState k)
def determinant (n k : ℂ) : ℂ := tmDet 1 n k

theorem numerator_first (n k : ℂ) (hk : k ≠ 0) : (numerator n k).1 = I := by
  simpa [numerator, adjugate, incidentState, mul_comm] using
    regular_outgoing_wronskian 1 k hk

theorem numerator_matching (n k : ℂ) :
    matching 1 n k (numerator n k) =
      (determinant n k * psi 1 k, determinant n k * psiD 1 k) := by
  simpa [numerator, determinant, incidentState] using
    matching_adjugate 1 n k (incidentState k)

def electric (n k : ℂ) : Field := fun x =>
  if ‖x‖ ≤ 1 then ((numerator n k).1 / n) • centerE (n*k) x
  else determinant n k • centerE k x + (numerator n k).2 • outgoingE k x

def magnetic (n k : ℂ) : Field := fun x =>
  if ‖x‖ ≤ 1 then ((numerator n k).1 / n) • centerH (n*k) k x
  else determinant n k • centerH k k x + (numerator n k).2 • outgoingH k k x

theorem interior (n k : ℂ) (hk : k ≠ 0) (x : Space) (hx : ‖x‖ ≤ 1) :
    electric n k x = (I/n) • centerE (n*k) x ∧
    magnetic n k x = (I/n) • centerH (n*k) k x := by
  simp [electric, magnetic, hx, numerator_first n k hk]

theorem exterior (n k : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    electric n k x = determinant n k • centerE k x + (numerator n k).2 • outgoingE k x ∧
    magnetic n k x = determinant n k • centerH k k x + (numerator n k).2 • outgoingH k k x := by
  simp [electric, magnetic, not_le.mpr hx]

theorem scattered_exterior (n k : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    electric n k x - determinant n k • centerE k x = (numerator n k).2 • outgoingE k x ∧
    magnetic n k x - determinant n k • centerH k k x = (numerator n k).2 • outgoingH k k x := by
  rw [(exterior n k x hx).1, (exterior n k x hx).2]
  constructor <;> abel

#print axioms OQ14.ModalDriven.numerator_first
#print axioms OQ14.ModalDriven.numerator_matching
#print axioms OQ14.ModalDriven.scattered_exterior

end OQ14.ModalDriven

