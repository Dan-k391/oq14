import RiccatiLogDerivative

/-! # Actual normalized functions for the Riccati barrier estimate -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.RiccatiBarrierNormalization

open Complex Filter Set Metric OQ14.RiccatiBarrier OQ14.RiccatiOriginLimits
open OQ14.RiccatiSeriesCoefficients OQ14.RiccatiLogDerivative
open scoped Topology

def v (l : ℕ) (x : ℝ) : ℝ := (normalized l (x : ℂ)).re
def slope (l : ℕ) (x : ℝ) : ℝ := (normalizedSlope l (x : ℂ)).re
def y (l : ℕ) (x : ℝ) : ℝ := slope l x/v l x

theorem v_zero (l : ℕ) : v l 0 = amplitude l 0 := by simp [v,normalized_zero]
theorem slope_zero (l : ℕ) : slope l 0 = (l+1)*amplitude l 0 := by
  simp [slope,normalizedSlope_zero]

theorem v_eq (l : ℕ) (x : ℝ) (hx : x ≠ 0) : v l x = u l x/x^(l+1) := by
  rw [u_eq_regular l x hx,regular_factor l x hx]
  dsimp [v]
  field_simp [hx]

theorem slope_eq (l : ℕ) (x : ℝ) (hx : x ≠ 0) : slope l x = du l x/x^l := by
  rw [du_eq_regularD l x hx,regularD_factor l x hx]
  dsimp [slope]
  field_simp [hx]

theorem v_continuous (l : ℕ) : Continuous (v l) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact Complex.continuous_re.continuousAt.comp
      ((normalized_continuousAt_zero l).comp (f := Complex.ofReal) (x := (0 : ℝ))
        Complex.continuous_ofReal.continuousAt)
  · have heq : v l =ᶠ[𝓝 x] fun t => u l t/t^(l+1) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with t ht
      exact v_eq l t ht
    apply (continuousAt_congr heq).mpr
    exact (u_continuous l).continuousAt.div (continuousAt_id.pow _) (pow_ne_zero _ hx)

theorem slope_continuous (l : ℕ) : Continuous (slope l) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact Complex.continuous_re.continuousAt.comp
      ((normalizedSlope_continuousAt_zero l).comp (f := Complex.ofReal) (x := (0 : ℝ))
        Complex.continuous_ofReal.continuousAt)
  · have heq : slope l =ᶠ[𝓝 x] fun t => du l t/t^l := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with t ht
      exact slope_eq l t ht
    apply (continuousAt_congr heq).mpr
    exact (du_continuous l).continuousAt.div (continuousAt_id.pow _) (pow_ne_zero _ hx)

theorem v_positive (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Icc 0 R) : 0 < v l x := by
  by_cases hx0 : x = 0
  · subst x
    rw [v_zero]
    exact amplitude_pos l 0
  · have hp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    rw [v_eq l x hx0,u_eq_regular l x hx0]
    exact div_pos (barrier_positive l R hR hbarrier x ⟨hp,hx.2⟩).1 (pow_pos hp _)

theorem y_zero (l : ℕ) : y l 0 = l+1 := by
  rw [y,v_zero,slope_zero]
  field_simp [(amplitude_pos l 0).ne']

theorem y_eq (l : ℕ) (x : ℝ) (hx : x ≠ 0) (hu : u l x ≠ 0) :
    y l x = x*du l x/u l x := by
  rw [y,v_eq l x hx,slope_eq l x hx,pow_succ]
  field_simp [hx,hu]
  ring

theorem y_continuousOn (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l) :
    ContinuousOn (y l) (Icc 0 R) :=
  (slope_continuous l).continuousOn.div (v_continuous l).continuousOn
    (fun x hx => (v_positive l R hR hbarrier x hx).ne')

theorem y_hasDerivAt (l : ℕ) (x : ℝ) (hx : x ≠ 0) (hu : u l x ≠ 0) :
    HasDerivAt (y l) ((ν l-x^2+y l x-(y l x)^2)/x) x := by
  have hn : ∀ᶠ t in 𝓝 x, u l t ≠ 0 :=
    (u_continuous l).continuousAt.tendsto.eventually (isOpen_compl_singleton.mem_nhds hu)
  have heq : y l =ᶠ[𝓝 x] fun t => t*du l t/u l t := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx,hn] with t ht htu
    exact y_eq l t ht htu
  have hd := ((hasDerivAt_id x).mul (du_hasDerivAt l x hx)).div (u_hasDerivAt l x) hu
  apply hd.congr_of_eventuallyEq heq |>.congr_deriv
  rw [y_eq l x hx hu]
  field_simp [hx,hu]
  ring

theorem y_barrier_bounds (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : gamma l R ≤ y l x ∧ y l x ≤ l+1 := by
  have hu : 0 < u l x := by
    rw [u_eq_regular l x hx.1.ne']
    exact (barrier_positive l R hR hbarrier x hx).1
  rw [y_eq l x hx.1.ne' hu.ne',u_eq_regular l x hx.1.ne',du_eq_regularD l x hx.1.ne']
  exact barrier_logDerivative_bounds l R hR hbarrier x hx

theorem v_hasDerivAt (l : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (v l) ((x*du l x-(l+1)*u l x)/x^(l+2)) x := by
  have heq : v l =ᶠ[𝓝 x] fun t => u l t/t^(l+1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with t ht
    exact v_eq l t ht
  have hd := (u_hasDerivAt l x).div (hasDerivAt_pow (l+1) x) (pow_ne_zero _ hx)
  apply hd.congr_of_eventuallyEq heq |>.congr_deriv
  simp only [Nat.add_sub_cancel]
  rw [show l+2=l+1+1 by omega,pow_succ,pow_succ]
  push_cast
  field_simp [hx]
  ring

theorem v_log_hasDerivAt (l : ℕ) (x : ℝ) (hx : x ≠ 0) (hu : u l x ≠ 0) :
    HasDerivAt (v l) (v l x*(y l x-(l+1))/x) x := by
  apply (v_hasDerivAt l x hx).congr_deriv
  rw [v_eq l x hx,y_eq l x hx hu]
  rw [show l+2=l+1+1 by omega,pow_succ]
  field_simp [hx,hu]
  ring

end OQ14.RiccatiBarrierNormalization

#print axioms OQ14.RiccatiBarrierNormalization.v_zero
#print axioms OQ14.RiccatiBarrierNormalization.slope_zero
#print axioms OQ14.RiccatiBarrierNormalization.v_eq
#print axioms OQ14.RiccatiBarrierNormalization.slope_eq
#print axioms OQ14.RiccatiBarrierNormalization.v_continuous
#print axioms OQ14.RiccatiBarrierNormalization.slope_continuous
#print axioms OQ14.RiccatiBarrierNormalization.v_positive
#print axioms OQ14.RiccatiBarrierNormalization.y_zero
#print axioms OQ14.RiccatiBarrierNormalization.y_eq
#print axioms OQ14.RiccatiBarrierNormalization.y_continuousOn
#print axioms OQ14.RiccatiBarrierNormalization.y_hasDerivAt
#print axioms OQ14.RiccatiBarrierNormalization.y_barrier_bounds
#print axioms OQ14.RiccatiBarrierNormalization.v_hasDerivAt
#print axioms OQ14.RiccatiBarrierNormalization.v_log_hasDerivAt
