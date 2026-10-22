import ConicalVolumePeaks
import Mathlib.Analysis.SpecificLimits.Basic

/-! Explicit smooth radial removal of the conical material in a shrinking tip ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalTipRounding
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume
open scoped Topology
abbrev Space := Maxwell.Space

def radius (n : ℕ) : ℝ := 1/((n : ℝ)+1)

theorem radius_positive (n : ℕ) : 0 < radius n := by unfold radius; positivity

def scalarBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (radius n)^2
  rOut := 4*(radius n)^2
  rIn_pos := sq_pos_of_pos (radius_positive n)
  rIn_lt_rOut := by nlinarith [sq_pos_of_pos (radius_positive n)]

def gate (n : ℕ) (x : Space) : ℝ := 1-scalarBump n (‖x‖^2)

theorem gate_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (gate n) :=
  contDiff_const.sub ((scalarBump n).contDiff.comp (contDiff_norm_sq ℝ))

theorem gate_radial (n : ℕ) (x y : Space) (h : ‖x‖=‖y‖) : gate n x=gate n y := by
  simp only [gate,h]

theorem gate_bounds (n : ℕ) (x : Space) : gate n x ∈ Icc (0 : ℝ) 1 := by
  unfold gate
  constructor
  · exact sub_nonneg.mpr (scalarBump n).le_one
  · linarith [(scalarBump n).nonneg' (‖x‖^2)]

theorem gate_zero_inner (n : ℕ) (x : Space) (hx : ‖x‖ ≤ radius n) : gate n x=0 := by
  have hm : ‖x‖^2 ∈ closedBall (0 : ℝ) (scalarBump n).rIn := by
    simp only [mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖x‖),scalarBump]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  simp only [gate,(scalarBump n).one_of_mem_closedBall hm,sub_self]

theorem gate_one_outer (n : ℕ) (x : Space) (hx : 2*radius n ≤ ‖x‖) : gate n x=1 := by
  have hm : (scalarBump n).rOut ≤ dist (‖x‖^2) 0 := by
    simp only [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖x‖),scalarBump]
    nlinarith [radius_positive n,norm_nonneg x]
  simp only [gate,(scalarBump n).zero_of_le_dist hm,sub_zero]

theorem gate_eventually_one (x : Space) (hx : x ≠ 0) : ∀ᶠ n : ℕ in atTop, gate n x=1 := by
  have ht : Tendsto (fun n => 2*radius n) atTop (𝓝 0) := by
    simpa only [radius,mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 2
  have he := ht.eventually (gt_mem_nhds (norm_pos_iff.mpr hx))
  exact he.mono (fun n hn => gate_one_outer n x hn.le)

def rounded (c : StaticCoefficient.Coefficient) (n : ℕ) : StaticCoefficient.Coefficient where
  value ξ := gate n (VectorFourier.coordinateMap.symm ξ)*c.value ξ
  bound := c.bound
  measurable := (((gate_smooth n).continuous.measurable.comp VectorFourier.coordinateMap.symm.measurable).mul c.measurable)
  nonnegative ξ := mul_nonneg (gate_bounds n _).1 (c.nonnegative ξ)
  bounded ξ := (mul_le_of_le_one_left (c.nonnegative ξ) (gate_bounds n _).2).trans (c.bounded ξ)

theorem rounded_bound (c : StaticCoefficient.Coefficient) (n : ℕ) : (rounded c n).bound=c.bound := rfl

theorem rounded_spatial (c : StaticCoefficient.Coefficient) (n : ℕ) (x : Space) :
    (rounded c n).value (VectorFourier.coordinateMap x)=gate n x*c.value (VectorFourier.coordinateMap x) := by
  simp only [rounded,MeasurableEquiv.symm_apply_apply]

theorem rounded_zero_inner (c : StaticCoefficient.Coefficient) (n : ℕ) (x : Space)
    (hx : ‖x‖ ≤ radius n) : (rounded c n).value (VectorFourier.coordinateMap x)=0 := by
  rw [rounded_spatial,gate_zero_inner n x hx,zero_mul]

theorem rounded_eq_outer (c : StaticCoefficient.Coefficient) (n : ℕ) (x : Space)
    (hx : 2*radius n ≤ ‖x‖) :
    (rounded c n).value (VectorFourier.coordinateMap x)=c.value (VectorFourier.coordinateMap x) := by
  rw [rounded_spatial,gate_one_outer n x hx,one_mul]

theorem rounded_smooth_near_tip (c : StaticCoefficient.Coefficient) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Space => (rounded c n).value (VectorFourier.coordinateMap x))
      (ball (0 : Space) (radius n)) := by
  apply contDiffOn_const.congr
  intro x hx
  have hn : ‖x‖ < radius n := by simpa only [mem_ball,dist_zero_right] using hx
  exact rounded_zero_inner c n x hn.le

theorem rounded_ae_tendsto (c : StaticCoefficient.Coefficient) :
    ∀ᵐ ξ : StaticCoefficient.Space,
      Tendsto (fun n => (rounded c n).value ξ) atTop (𝓝 (c.value ξ)) := by
  have he : ∀ᵐ ξ : StaticCoefficient.Space, ξ ∉ ({VectorFourier.coordinateMap (0 : Space)} : Set StaticCoefficient.Space) :=
    (countable_singleton _).ae_not_mem volume
  filter_upwards [he] with ξ hξ
  have hx : VectorFourier.coordinateMap.symm ξ ≠ (0 : Space) := by
    intro h
    apply hξ
    rw [mem_singleton_iff,← h,MeasurableEquiv.apply_symm_apply]
  have hn := gate_eventually_one (VectorFourier.coordinateMap.symm ξ) hx
  apply tendsto_const_nhds.congr'
  exact hn.mono (fun n hn => by simp only [rounded,hn,one_mul])

theorem conical_common_support (p : Data) (n : ℕ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) :
    (rounded (coefficient p) n).value (VectorFourier.coordinateMap x)=0 := by
  rw [rounded_spatial,coefficient_compact p x hx,mul_zero]

end OQ14.ConicalTipRounding

#print axioms OQ14.ConicalTipRounding.radius_positive
#print axioms OQ14.ConicalTipRounding.gate_smooth
#print axioms OQ14.ConicalTipRounding.gate_radial
#print axioms OQ14.ConicalTipRounding.gate_bounds
#print axioms OQ14.ConicalTipRounding.gate_zero_inner
#print axioms OQ14.ConicalTipRounding.gate_one_outer
#print axioms OQ14.ConicalTipRounding.gate_eventually_one
#print axioms OQ14.ConicalTipRounding.rounded_bound
#print axioms OQ14.ConicalTipRounding.rounded_spatial
#print axioms OQ14.ConicalTipRounding.rounded_zero_inner
#print axioms OQ14.ConicalTipRounding.rounded_eq_outer
#print axioms OQ14.ConicalTipRounding.rounded_smooth_near_tip
#print axioms OQ14.ConicalTipRounding.rounded_ae_tendsto
#print axioms OQ14.ConicalTipRounding.conical_common_support
