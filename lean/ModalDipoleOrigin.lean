import ModalOrigin
import Mathlib.Analysis.Complex.CauchyIntegral

/-! The actual degree-one matching determinant has a removable frequency origin,
jointly with the refractive index. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OQ14.ModalDipoleOrigin

open Complex Filter Set Metric OQ14.ModalAlgebra OQ14.ModalOrigin
open scoped Topology

/-- Entire expression obtained by cancelling the actual regular dipole factors
against the outgoing dipole's poles. -/
def regularized (n z : ℂ) : ℂ :=
  exp (I*z) * (n^3*(I+z-I*z^2)*profile (n*z) +
    (z+I)*(2*n*profile (n*z)+n^2*z*deriv profile (n*z)))

theorem regularized_eq (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    regularized n z = tmDet 1 n z := by
  unfold tmDet
  rw [psi_profile (n*z) (mul_ne_zero hn hz),psiD_profile (n*z) (mul_ne_zero hn hz)]
  unfold xi xiD
  rw [p_one,pD_one]
  norm_num
  unfold regularized
  field_simp [hz]
  ring_nf
  norm_num [I_sq]
  ring

theorem regularized_zero (n : ℂ) : regularized n 0 = I*n*(n^2+2)/3 := by
  simp only [regularized,mul_zero,exp_zero,one_mul,add_zero,zero_pow (by decide : 2 ≠ 0),
    sub_zero,profile_zero,zero_mul]
  ring

theorem regularized_one_zero : regularized 1 0 = I := by
  rw [regularized_zero]
  ring

theorem regularized_continuous : Continuous (fun w : ℂ × ℂ => regularized w.1 w.2) := by
  have hp := profile_differentiable.continuous.comp (continuous_fst.mul continuous_snd)
  have hd := profile_deriv_differentiable.continuous.comp (continuous_fst.mul continuous_snd)
  unfold regularized
  fun_prop

theorem regularized_differentiable (n : ℂ) : Differentiable ℂ (regularized n) := by
  have hp := profile_differentiable.comp ((differentiable_const n).mul differentiable_id)
  have hd := profile_deriv_differentiable.comp ((differentiable_const n).mul differentiable_id)
  unfold regularized
  fun_prop

theorem regularized_analyticAt (n z : ℂ) : AnalyticAt ℂ (regularized n) z :=
  (regularized_differentiable n).analyticAt z

theorem tmDet_one (z : ℂ) (hz : z ≠ 0) : tmDet 1 1 z = I := by
  have hw := l_one_wronskian z hz
  unfold tmDet psi psiD
  simp only [one_mul]
  linear_combination -(1/2 : ℂ)*hw

theorem regularized_one (z : ℂ) : regularized 1 z = I := by
  by_cases hz : z = 0
  · subst z
    exact regularized_one_zero
  · rw [regularized_eq 1 z one_ne_zero hz]
    exact tmDet_one z hz

theorem product_nonzero_near (f : ℂ × ℂ → ℂ) (hf : ContinuousAt f ((1 : ℂ),0))
    (h0 : f (1,0) ≠ 0) : ∃ δ : ℝ, 0 < δ ∧ ∀ n z : ℂ,
      ‖n-1‖ < δ → ‖z‖ < δ → f (n,z) ≠ 0 := by
  have he : ∀ᶠ w : ℂ × ℂ in 𝓝 ((1 : ℂ),0), f w ≠ (0 : ℂ) :=
    hf.tendsto.eventually (eventually_ne_nhds h0)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨δ,hδ,?_⟩
  intro n z hn hz
  apply hball
  rw [Prod.dist_eq]
  exact max_lt (by simpa only [dist_eq_norm] using hn) (by simpa using hz)

theorem uniform_origin_nonzero : ∃ δ : ℝ, 0 < δ ∧ ∀ n z : ℂ,
    ‖n-1‖ < δ → ‖z‖ < δ → regularized n z ≠ 0 := by
  have h0 : regularized (1 : ℂ) (0 : ℂ) ≠ (0 : ℂ) := by
    rw [regularized_one_zero]
    exact I_ne_zero
  exact product_nonzero_near (fun w : ℂ × ℂ => regularized w.1 w.2)
    regularized_continuous.continuousAt h0

theorem uniform_tmDet_nonzero : ∃ δ : ℝ, 0 < δ ∧ ∀ n z : ℂ,
    n ≠ 0 → z ≠ 0 → ‖n-1‖ < δ → ‖z‖ < δ → tmDet 1 n z ≠ 0 := by
  obtain ⟨δ,hδ,h⟩ := uniform_origin_nonzero
  exact ⟨δ,hδ,fun n z hn hz hnd hzd => regularized_eq n z hn hz ▸ h n z hnd hzd⟩

theorem uniform_real_tmDet_nonzero : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℝ, ∀ z : ℂ,
    1 ≤ n → z ≠ 0 → |n-1| < δ → ‖z‖ < δ → tmDet 1 (n : ℂ) z ≠ 0 := by
  obtain ⟨δ,hδ,h⟩ := uniform_tmDet_nonzero
  refine ⟨δ,hδ,?_⟩
  intro n z hn hz hnd hzd
  apply h n z (by exact_mod_cast (by linarith : n ≠ 0)) hz _ hzd
  simpa only [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hnd

/-- For each compact frequency set, the same index neighborhood excludes every
zero, including branches approaching the removable frequency origin. -/
theorem compact_regularized_nonzero (K : Set ℂ) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℂ, ‖n-1‖ < δ → ∀ z ∈ K, regularized n z ≠ 0 := by
  have he : ∀ᶠ n : ℂ in 𝓝 (1 : ℂ), ∀ z ∈ K, regularized n z ≠ 0 := by
    apply hK.eventually_forall_of_forall_eventually
    intro z _
    have hc : ContinuousAt (fun w : ℂ × ℂ => regularized w.1 w.2) ((1 : ℂ),z) :=
      regularized_continuous.continuousAt
    have h0 : regularized 1 z ≠ 0 := by rw [regularized_one]; exact I_ne_zero
    exact hc.tendsto.eventually (eventually_ne_nhds h0)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨δ,hδ,fun n hn => hball (by simpa only [dist_eq_norm] using hn)⟩

theorem compact_tmDet_nonzero (K : Set ℂ) (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n z : ℂ, n ≠ 0 → z ≠ 0 →
      ‖n-1‖ < δ → z ∈ K → tmDet 1 n z ≠ 0 := by
  obtain ⟨δ,hδ,h⟩ := compact_regularized_nonzero K hK
  exact ⟨δ,hδ,fun n z hn hz hnd hzK => regularized_eq n z hn hz ▸ h n hnd z hzK⟩

theorem bounded_real_tmDet_nonzero (B : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℝ, ∀ z : ℂ, 1 ≤ n → z ≠ 0 →
      |n-1| < δ → ‖z‖ ≤ B → tmDet 1 (n : ℂ) z ≠ 0 := by
  obtain ⟨δ,hδ,h⟩ := compact_tmDet_nonzero (closedBall (0 : ℂ) B) (isCompact_closedBall _ _)
  refine ⟨δ,hδ,?_⟩
  intro n z hn hz hnd hzB
  apply h n z (by exact_mod_cast (by linarith : n ≠ 0)) hz _ _
  · simpa only [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using hnd
  · simpa only [mem_closedBall,dist_zero_right] using hzB

theorem zero_frequencies_escape {α : Type*} (f : Filter α) (n : α → ℝ) (z : α → ℂ)
    (hn : Tendsto n f (𝓝 1)) (hindex : ∀ᶠ a in f, 1 ≤ n a)
    (hz : ∀ᶠ a in f, z a ≠ 0) (hroot : ∀ᶠ a in f, tmDet 1 (n a : ℂ) (z a) = 0) :
    Tendsto (fun a => ‖z a‖) f atTop := by
  apply Filter.tendsto_atTop.2
  intro B
  obtain ⟨δ,hδ,h⟩ := bounded_real_tmDet_nonzero B
  have he : ∀ᶠ a in f, |n a-1| < δ := by
    have ht : Tendsto (fun a => |n a-1|) f (𝓝 0) := by
      simpa using (hn.sub_const 1).abs
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [he,hindex,hz,hroot] with a ha hi hza hra
  have hh : ¬‖z a‖ ≤ B := fun hb => h (n a) (z a) hi hza ha hb hra
  exact (not_le.mp hh).le

end OQ14.ModalDipoleOrigin

#print axioms OQ14.ModalDipoleOrigin.regularized_eq
#print axioms OQ14.ModalDipoleOrigin.regularized_zero
#print axioms OQ14.ModalDipoleOrigin.regularized_one_zero
#print axioms OQ14.ModalDipoleOrigin.regularized_continuous
#print axioms OQ14.ModalDipoleOrigin.regularized_differentiable
#print axioms OQ14.ModalDipoleOrigin.regularized_analyticAt
#print axioms OQ14.ModalDipoleOrigin.tmDet_one
#print axioms OQ14.ModalDipoleOrigin.regularized_one
#print axioms OQ14.ModalDipoleOrigin.product_nonzero_near
#print axioms OQ14.ModalDipoleOrigin.uniform_origin_nonzero
#print axioms OQ14.ModalDipoleOrigin.uniform_tmDet_nonzero
#print axioms OQ14.ModalDipoleOrigin.uniform_real_tmDet_nonzero
#print axioms OQ14.ModalDipoleOrigin.compact_regularized_nonzero
#print axioms OQ14.ModalDipoleOrigin.compact_tmDet_nonzero
#print axioms OQ14.ModalDipoleOrigin.bounded_real_tmDet_nonzero
#print axioms OQ14.ModalDipoleOrigin.zero_frequencies_escape
