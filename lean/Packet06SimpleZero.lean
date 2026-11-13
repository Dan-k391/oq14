import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OQ14.Packet06SimpleZero
open Metric Set Filter
open scoped Topology NNReal

theorem zero_of_small_derivative_error (f : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hf : ∀ z ∈ closedBall a r, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ closedBall a r, ‖1 - deriv f z‖ ≤ 1/2)
    (ha : ‖f a‖ ≤ r/2) :
    ∃ z ∈ closedBall a r, f z = 0 := by
  let g : ℂ → ℂ := fun z => z - f z
  have hga : g a - a = - f a := by simp [g]
  have hdiff : ∀ z ∈ closedBall a r, DifferentiableAt ℂ g z := by
    intro z hz
    exact differentiableAt_id.sub (hf z hz)
  have hder (z : ℂ) (hz : z ∈ closedBall a r) : ‖deriv g z‖₊ ≤ (1/2 : ℝ≥0) := by
    have he : deriv g z = 1 - deriv f z := by
      exact ((hasDerivAt_id z).sub (hf z hz).hasDerivAt).deriv
    exact_mod_cast (he ▸ hd z hz)
  have hlip : LipschitzOnWith (1/2 : ℝ≥0) g (closedBall a r) :=
    (convex_closedBall a r).lipschitzOnWith_of_nnnorm_deriv_le hdiff hder
  have hmaps : MapsTo g (closedBall a r) (closedBall a r) := by
    intro z hz
    have hza : a ∈ closedBall a r := mem_closedBall_self hr.le
    have hbound : ‖g z - g a‖ ≤ (1/2 : ℝ)*‖z-a‖ := by
      have h := hlip.dist_le_mul z hz a hza
      simpa only [dist_eq_norm, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h
    rw [mem_closedBall, dist_eq_norm] at hz ⊢
    have hsum : ‖g z - a‖ ≤ ‖g z - g a‖ + ‖g a-a‖ := by
      convert norm_add_le (g z - g a) (g a-a) using 1
      congr 1
      ring
    rw [hga, norm_neg] at hsum
    linarith
  have hcontract : ContractingWith (1/2 : ℝ≥0) (hmaps.restrict g _ _) := by
    constructor
    · exact_mod_cast (show (1/2 : ℝ) < 1 by norm_num)
    · intro x y
      exact hlip x.property y.property
  have hcomplete : IsComplete (closedBall a r) := isClosed_closedBall.isComplete
  obtain ⟨z,hz,hfix,_,_⟩ := ContractingWith.exists_fixedPoint' hcomplete hmaps hcontract
    (mem_closedBall_self hr.le) (edist_ne_top a (g a))
  refine ⟨z,hz,?_⟩
  change g z = z at hfix
  dsimp [g] at hfix
  exact sub_eq_self.mp hfix
theorem unique_and_simple_of_small_derivative_error (f : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (hf : ∀ z ∈ closedBall a r, DifferentiableAt ℂ f z)
    (hd : ∀ z ∈ closedBall a r, ‖1 - deriv f z‖ ≤ 1/2) :
    (∀ z ∈ closedBall a r, deriv f z ≠ 0) ∧
      ∀ z ∈ closedBall a r, ∀ w ∈ closedBall a r, f z = 0 → f w = 0 → z = w := by
  let g : ℂ → ℂ := fun z => z - f z
  have hdiff : ∀ z ∈ closedBall a r, DifferentiableAt ℂ g z := by
    intro z hz
    exact differentiableAt_id.sub (hf z hz)
  have hder (z : ℂ) (hz : z ∈ closedBall a r) : ‖deriv g z‖₊ ≤ (1/2 : ℝ≥0) := by
    have he : deriv g z = 1 - deriv f z := ((hasDerivAt_id z).sub (hf z hz).hasDerivAt).deriv
    exact_mod_cast (he ▸ hd z hz)
  have hlip : LipschitzOnWith (1/2 : ℝ≥0) g (closedBall a r) :=
    (convex_closedBall a r).lipschitzOnWith_of_nnnorm_deriv_le hdiff hder
  constructor
  · intro z hz he
    have h := hd z hz
    rw [he] at h
    norm_num at h
  · intro z hz w hw hz0 hw0
    have h := hlip.dist_le_mul z hz w hw
    have hg : g z = z := by simp [g,hz0]
    have hwg : g w = w := by simp [g,hw0]
    rw [hg, hwg] at h
    have hdist : dist z w = 0 := by
      have hp := dist_nonneg (x := z) (y := w)
      norm_num at h
      linarith
    exact dist_eq_zero.mp hdist

#print axioms OQ14.Packet06SimpleZero.unique_and_simple_of_small_derivative_error
#print axioms OQ14.Packet06SimpleZero.zero_of_small_derivative_error
end OQ14.Packet06SimpleZero
