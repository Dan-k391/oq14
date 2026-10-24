import RestrictedTEDipoleProfile

/-! Positivity of the half-plane profile integral `halfPlane n h`. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.RestrictedTEHalfPlanePositive
open MeasureTheory Metric Set Filter OQ14.RestrictedTEDipoleProfile
abbrev Plane := PlaneInverseCube.Plane

theorem U_isOpen (n : Plane) : IsOpen (U n) :=
  isOpen_lt continuous_const (ip_continuous n)

theorem U_nonempty (n : Plane) (hn : ‖n‖=1) : (U n).Nonempty := by
  refine ⟨n, ?_⟩
  change 0 < ip n n
  unfold ip
  rw [real_inner_self_eq_norm_sq, hn]
  norm_num

theorem psi_pos_on (n : Plane) (t : ℝ) (ht : 0<t) (ξ : Plane) (hξ : ξ∈U n) : 0<psi n t ξ := by
  have hr := rad_pos t ht ξ
  have hp : 0<prof t ξ := by
    unfold prof
    have := Real.pi_pos
    positivity
  unfold psi
  exact mul_pos hξ hp

/-- The half-plane profile integral is strictly positive. -/
theorem halfPlane_pos (n : Plane) (hn : ‖n‖=1) (h : ℝ) (hh : 0<h) : 0<halfPlane n h := by
  unfold halfPlane
  have hnn : 0≤(U n).indicator (psi n h) := by
    intro ξ
    by_cases hξ : ξ∈U n
    · rw [Set.indicator_of_mem hξ]
      exact (psi_pos_on n h hh ξ hξ).le
    · rw [Set.indicator_of_not_mem hξ]
      exact le_rfl
  have hint : Integrable ((U n).indicator (psi n h)) := (psi_integrable n hn h hh).indicator (U_measurable n)
  refine (integral_pos_iff_support_of_nonneg hnn hint).mpr ?_
  have hsub : U n⊆Function.support ((U n).indicator (psi n h)) := by
    intro ξ hξ
    rw [Function.mem_support, Set.indicator_of_mem hξ]
    exact (psi_pos_on n h hh ξ hξ).ne'
  exact lt_of_lt_of_le ((U_isOpen n).measure_pos volume (U_nonempty n hn)) (measure_mono hsub)

end OQ14.RestrictedTEHalfPlanePositive
#print axioms OQ14.RestrictedTEHalfPlanePositive.U_isOpen
#print axioms OQ14.RestrictedTEHalfPlanePositive.U_nonempty
#print axioms OQ14.RestrictedTEHalfPlanePositive.psi_pos_on
#print axioms OQ14.RestrictedTEHalfPlanePositive.halfPlane_pos
