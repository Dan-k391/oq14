import ModalAlgebraicity
import LindemannWeierstrassPort

/-!
# All-degree simplicity and separation of spherical TM determinant zeros

The algebraic obstruction is contradicted by the fully proved
Hermite--Lindemann theorem. No exponential transcendence premise is needed.
These are statements about the actual spherical matching determinants;
identifying the whole volume-operator kernel remains a separate obligation.
-/

noncomputable section
set_option autoImplicit false

namespace OQ14.ModalTMIsolation

open Complex OQ14.ModalAlgebra OQ14.ModalAlgebraicity

/-- Every nonzero TM zero has transcendental frequency for algebraic index. -/
theorem zero_transcendental (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) : Transcendental ℚ z := by
  intro hza
  obtain ⟨ha, ha0, he⟩ := algebraic_pole_exponential_obstruction l n z hna hza hn hz hd
  exact LindemannWeierstrassPort.exponential_algebraicity_impossible ha ha0 he

/-- Every nonzero TM zero is simple for algebraic index outside 0, 1 and -1. -/
theorem zero_simple (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (hz : z ≠ 0) (hd : tmDet l n z = 0) : deriv (tmDet l n) z ≠ 0 := by
  intro hdd
  exact zero_transcendental l n z hna hn hz hd
    (multiple_zero_isAlgebraic l n z hna hn hp hm hz hd hdd)

/-- Different angular degrees have no common nonzero TM zero. -/
theorem distinct_degree_nonzero (l j : ℕ) (n z : ℂ)
    (hlj : l ≠ j) (hna : IsAlgebraic ℚ n) (hn : n ≠ 0)
    (hp : n ≠ 1) (hm : n ≠ -1) (hz : z ≠ 0)
    (hl : tmDet l n z = 0) : tmDet j n z ≠ 0 := by
  intro hj
  exact zero_transcendental l n z hna hn hz hl
    (common_zero_isAlgebraic l j n z hlj hna hn hp hm hz hl hj)

/-- At a selected zero, precisely its own degree vanishes and its derivative is nonzero. -/
theorem isolated_degree (l : ℕ) (n z : ℂ)
    (hna : IsAlgebraic ℚ n) (hn : n ≠ 0) (hp : n ≠ 1) (hm : n ≠ -1)
    (hz : z ≠ 0) (hl : tmDet l n z = 0) :
    deriv (tmDet l n) z ≠ 0 ∧ ∀ j : ℕ, tmDet j n z = 0 ↔ j = l := by
  refine ⟨zero_simple l n z hna hn hp hm hz hl, ?_⟩
  intro j
  constructor
  · intro hj
    by_contra hjl
    exact distinct_degree_nonzero l j n z (Ne.symm hjl) hna hn hp hm hz hl hj
  · rintro rfl
    exact hl

end OQ14.ModalTMIsolation

#print axioms OQ14.ModalTMIsolation.zero_transcendental
#print axioms OQ14.ModalTMIsolation.zero_simple
#print axioms OQ14.ModalTMIsolation.distinct_degree_nonzero
#print axioms OQ14.ModalTMIsolation.isolated_degree
