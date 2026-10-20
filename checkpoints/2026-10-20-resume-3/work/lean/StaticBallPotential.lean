import ParityMaterialField
import Mathlib.Topology.Piecewise

/-! # Explicit scalar potential of a uniform three-dimensional ball

This module begins the actual static-ball construction. The piecewise
potential and its first derivative match at the physical sphere radius.
The Newton/projection identification is a separate subsequent obligation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.StaticBallPotential

open Set Filter Metric
open scoped Topology
open scoped InnerProductSpace

def radial (R r : ℝ) : ℝ := if r ≤ R then R^2/2-r^2/6 else R^3/(3*r)
def radialD (R r : ℝ) : ℝ := if r ≤ R then -r/3 else -R^3/(3*r^2)

theorem boundary_value (R : ℝ) (hR : R ≠ 0) :
    R^2/2-R^2/6 = R^3/(3*R) := by field_simp; ring

theorem boundary_derivative (R : ℝ) (hR : R ≠ 0) :
    -R/3 = -R^3/(3*R^2) := by field_simp; ring

theorem interior_hasDerivAt (R r : ℝ) :
    HasDerivAt (fun t : ℝ => R^2/2-t^2/6) (-r/3) r := by
  convert (hasDerivAt_const r (R^2/2)).sub (((hasDerivAt_id r).pow 2).div_const 6) using 1
  simp only [id_eq]
  ring

theorem exterior_hasDerivAt (R r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ => R^3/(3*t)) (-R^3/(3*r^2)) r := by
  convert (hasDerivAt_const r (R^3)).div ((hasDerivAt_id r).const_mul 3)
    (mul_ne_zero (by norm_num) hr) using 1
  field_simp
  ring

theorem radial_hasDerivAt (R r : ℝ) (hR : 0 < R) :
    HasDerivAt (radial R) (radialD R r) r := by
  rcases lt_trichotomy r R with hr | hr | hr
  · have he : radial R =ᶠ[𝓝 r] fun t => R^2/2-t^2/6 := by
      filter_upwards [Iio_mem_nhds hr] with t ht
      exact if_pos ht.le
    simpa only [radialD, if_pos hr.le] using (interior_hasDerivAt R r).congr_of_eventuallyEq he
  · subst r
    have hl : HasDerivWithinAt (radial R) (-R/3) (Iic R) R := by
      apply (interior_hasDerivAt R R).hasDerivWithinAt.congr_of_mem
      · intro t ht
        exact if_pos ht
      · simp
    have hr : HasDerivWithinAt (radial R) (-R/3) (Ici R) R := by
      rw [boundary_derivative R hR.ne']
      apply (exterior_hasDerivAt R R hR.ne').hasDerivWithinAt.congr_of_mem
      · intro t ht
        by_cases he : t ≤ R
        · have heq : t = R := le_antisymm he ht
          subst t
          simpa only [radial, if_pos le_rfl] using boundary_value R hR.ne'
        · exact if_neg he
      · simp
    have hh := hl.union hr
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at hh
    simpa only [radialD, if_pos le_rfl] using hh
  · have he : radial R =ᶠ[𝓝 r] fun t => R^3/(3*t) := by
      filter_upwards [Ioi_mem_nhds hr] with t ht
      exact if_neg (not_le.mpr ht)
    simpa only [radialD, if_neg (not_le.mpr hr)] using
      (exterior_hasDerivAt R r (hR.trans hr).ne').congr_of_eventuallyEq he

theorem radialD_continuous (R : ℝ) (hR : 0 < R) : Continuous (radialD R) := by
  apply continuous_if
  · intro r hr
    have he : r = R := by simpa only [show {r : ℝ | r ≤ R} = Iic R from rfl,
      frontier_Iic, mem_singleton_iff] using hr
    subst r
    exact boundary_derivative R hR.ne'
  · exact (continuous_id.neg.div_const 3).continuousOn
  · intro r hr
    have hrr : R ≤ r := by
      simpa only [not_le, show {r : ℝ | R < r} = Ioi R from rfl, closure_Ioi, mem_Ici] using hr
    have hrp : 0 < r := hR.trans_le hrr
    exact continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 2))
      (by positivity : (3 : ℝ)*r^2 ≠ 0) |>.continuousWithinAt

theorem radial_continuous (R : ℝ) (hR : 0 < R) : Continuous (radial R) :=
  continuous_iff_continuousAt.mpr (fun r => (radial_hasDerivAt R r hR).continuousAt)

def potential (R : ℝ) (x : FourierL2.Space) : ℝ := radial R ‖x‖

theorem potential_continuous (R : ℝ) (hR : 0 < R) : Continuous (potential R) :=
  (radial_continuous R hR).comp continuous_norm

theorem potential_inside (R : ℝ) (x : FourierL2.Space) (hx : ‖x‖ ≤ R) :
    potential R x = R^2/2-‖x‖^2/6 := if_pos hx

theorem potential_outside (R : ℝ) (x : FourierL2.Space) (hx : R < ‖x‖) :
    potential R x = R^3/(3*‖x‖) := if_neg (not_le.mpr hx)

def force (R r : ℝ) : ℝ := if r ≤ R then -1/3 else -R^3/(3*r^3)

theorem force_continuous (R : ℝ) (hR : 0 < R) : Continuous (force R) := by
  apply continuous_if
  · intro r hr
    have he : r = R := by simpa only [show {r : ℝ | r ≤ R} = Iic R from rfl,
      frontier_Iic, mem_singleton_iff] using hr
    subst r
    field_simp
    ring
  · exact continuous_const.continuousOn
  · intro r hr
    have hrr : R ≤ r := by
      simpa only [not_le, show {r : ℝ | R < r} = Ioi R from rfl, closure_Ioi, mem_Ici] using hr
    have hrp : 0 < r := hR.trans_le hrr
    exact continuousAt_const.div (continuousAt_const.mul (continuousAt_id.pow 3))
      (by positivity : (3 : ℝ)*r^3 ≠ 0) |>.continuousWithinAt

theorem radialD_eq_force (R r : ℝ) (hr : r ≠ 0) : radialD R r = force R r * r := by
  unfold radialD force
  split_ifs
  · ring
  · field_simp
    ring

theorem potential_hasFDerivAt (R : ℝ) (hR : 0 < R) (x : FourierL2.Space) :
    HasFDerivAt (potential R) (force R ‖x‖ • innerSL ℝ x) x := by
  by_cases hx : x = 0
  · subst x
    have he : potential R =ᶠ[𝓝 (0 : FourierL2.Space)] fun y => R^2/2-‖y‖^2/6 := by
      filter_upwards [isOpen_ball.mem_nhds (show (0 : FourierL2.Space) ∈ ball 0 R from
        by simpa using hR)] with y hy
      exact potential_inside R y (by
        have hh : ‖y‖ < R := by simpa only [mem_ball, dist_zero_right] using hy
        exact hh.le)
    have hd := (hasFDerivAt_const (𝕜 := ℝ) (R^2/2 : ℝ) (0 : FourierL2.Space)).sub
      ((hasStrictFDerivAt_norm_sq (0 : FourierL2.Space)).hasFDerivAt.const_smul (1/6 : ℝ))
    have hd' : HasFDerivAt (𝕜 := ℝ) (fun y : FourierL2.Space => R^2/2-‖y‖^2/6) 0 0 := by
      simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hd
    simpa using hd'.congr_of_eventuallyEq he
  · have hn := (differentiableAt_id.norm ℝ hx).hasFDerivAt
    have he := (hn.mul hn).unique (by simpa only [pow_two] using
      (hasStrictFDerivAt_norm_sq x).hasFDerivAt)
    have hd := (radial_hasDerivAt R ‖x‖ hR).hasFDerivAt.comp x hn
    have hnz : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    convert hd using 1
    ext v
    have hv := congrArg (fun L : FourierL2.Space →L[ℝ] ℝ => L v) he
    simp only [id_eq, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, two_smul] at hv
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply,
      smul_eq_mul, mul_one, id_eq]
    rw [radialD_eq_force R ‖x‖ hnz]
    have hnv : ‖x‖ * (fderiv ℝ (fun y : FourierL2.Space => ‖y‖) x) v = innerSL ℝ x v := by linarith
    linear_combination -(force R ‖x‖) * hnv

theorem potential_contDiff_one (R : ℝ) (hR : 0 < R) : ContDiff ℝ 1 (potential R) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun x => force R ‖x‖ • innerSL ℝ x, ?_, potential_hasFDerivAt R hR⟩
  exact ((force_continuous R hR).comp continuous_norm).smul (innerSL ℝ).continuous

end OQ14.StaticBallPotential

#print axioms OQ14.StaticBallPotential.boundary_value
#print axioms OQ14.StaticBallPotential.boundary_derivative
#print axioms OQ14.StaticBallPotential.interior_hasDerivAt
#print axioms OQ14.StaticBallPotential.exterior_hasDerivAt
#print axioms OQ14.StaticBallPotential.radial_hasDerivAt
#print axioms OQ14.StaticBallPotential.radialD_continuous
#print axioms OQ14.StaticBallPotential.radial_continuous
#print axioms OQ14.StaticBallPotential.potential_continuous
#print axioms OQ14.StaticBallPotential.potential_inside
#print axioms OQ14.StaticBallPotential.potential_outside
#print axioms OQ14.StaticBallPotential.force_continuous
#print axioms OQ14.StaticBallPotential.radialD_eq_force
#print axioms OQ14.StaticBallPotential.potential_hasFDerivAt
#print axioms OQ14.StaticBallPotential.potential_contDiff_one
