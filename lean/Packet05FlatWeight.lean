import Packet05DifferenceConverse
import FlatDifferenceCoercivity

/-! L² multiplication by the genuine flat dielectric and its tangential
difference-quotient commutation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FlatWeight
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient

def weight (d : ℝ) (x : Space) : ℂ := FlatDifferenceCoercivity.dielectric d x

theorem weight_memLp_top (d : ℝ) (hd : 0 ≤ d) : MemLp (weight d) ⊤ volume := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.measurable.comp (FlatDifferenceCoercivity.dielectric_measurable d)).aestronglyMeasurable) (1+d)
  filter_upwards with x
  change ‖weight d x‖ ≤ 1+d
  have h := FlatDifferenceCoercivity.dielectric_bounds d hd x
  simpa only [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) h.1)] using h.2

def mulWeight (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar) : L2Scalar :=
  ((Lp.memLp u).mul' (weight_memLp_top d hd)).toLp (fun x => weight d x * u x)

theorem mulWeight_ae (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar) :
    (fun x => mulWeight d hd u x) =ᵐ[volume] fun x => weight d x * u x :=
  ((Lp.memLp u).mul' (weight_memLp_top d hd)).coeFn_toLp

theorem weight_tangential (d : ℝ) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (x : Space) :
    weight d (x + h • basis i) = weight d x := by
  fin_cases i <;> simp [weight, FlatDifferenceCoercivity.dielectric, basis, EuclideanSpace.single_apply] at hi ⊢

theorem weighted_quotient_bound (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) :
    ‖quotient (mulWeight d hd u) i h‖ ≤ (1+d) * ‖quotient u i h‖ := by
  have he := quotient_commutes_invariant_weight
    (fun _ => mulWeight d hd u) (fun _ => u) (weight d) i h (weight_tangential d i hi h)
    (fun _ => mulWeight_ae d hd u) 0
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [he] with x hx
  change quotient (mulWeight d hd u) i h x = weight d x * quotient u i h x at hx
  change ‖quotient (mulWeight d hd u) i h x‖ ≤ (1+d) * ‖quotient u i h x‖
  rw [hx, norm_mul]
  have h := FlatDifferenceCoercivity.dielectric_bounds d hd x
  have hw : ‖weight d x‖ ≤ 1+d := by
    simpa only [weight, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) h.1)] using h.2
  exact mul_le_mul_of_nonneg_right hw (norm_nonneg _)

theorem weighted_weakPartial_of_bounded_quotients (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar)
    (i : Fin 3) (hi : i ≠ 2) (B δ : ℝ) (hB : 0 ≤ B) (hδ : 0 < δ)
    (hbound : ∀ h : ℝ, h ≠ 0 → |h| < δ → ‖quotient u i h‖ ≤ B) :
    ∃ v : L2Scalar, DivCurlCompact.HasWeakPartial (mulWeight d hd u) v i ∧ ‖v‖ ≤ (1+d)*B := by
  apply Packet05DifferenceConverse.weakPartial_of_bounded_quotients _ i ((1+d)*B) δ
    (mul_nonneg (by linarith) hB) hδ
  intro h hh hs
  exact (weighted_quotient_bound d hd u i hi h).trans
    (mul_le_mul_of_nonneg_left (hbound h hh hs) (by linarith))

end OQ14.Packet05FlatWeight
#print axioms OQ14.Packet05FlatWeight.weight_memLp_top
#print axioms OQ14.Packet05FlatWeight.mulWeight_ae
#print axioms OQ14.Packet05FlatWeight.weight_tangential
#print axioms OQ14.Packet05FlatWeight.weighted_quotient_bound
#print axioms OQ14.Packet05FlatWeight.weighted_weakPartial_of_bounded_quotients
