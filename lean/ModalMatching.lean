import ModalAsymptotics
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Actual spherical TM matching inverse and its simple-zero residue

The map is constructed from the actual factorial-series matching entries.
Its inverse and residue are derived, rather than postulated. Identification
of these boundary amplitudes with full vector Maxwell traces is separate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.ModalMatching

open Complex Filter OQ14.ModalAlgebra OQ14.ModalWronskian
open scoped Topology

abbrev Amplitudes := ℂ × ℂ

def matching (l : ℕ) (n z : ℂ) (v : Amplitudes) : Amplitudes :=
  (n * psi l (n * z) * v.1 - xi l z * v.2,
    psiD l (n * z) * v.1 - xiD l z * v.2)

def adjugate (l : ℕ) (n z : ℂ) (f : Amplitudes) : Amplitudes :=
  (xiD l z * f.1 - xi l z * f.2,
    psiD l (n * z) * f.1 - n * psi l (n * z) * f.2)

def solve (l : ℕ) (n z : ℂ) (f : Amplitudes) : Amplitudes :=
  ((adjugate l n z f).1 / tmDet l n z, (adjugate l n z f).2 / tmDet l n z)

def residue (l : ℕ) (n z : ℂ) (f : Amplitudes) : Amplitudes :=
  ((adjugate l n z f).1 / deriv (tmDet l n) z,
    (adjugate l n z f).2 / deriv (tmDet l n) z)

theorem matching_adjugate (l : ℕ) (n z : ℂ) (f : Amplitudes) :
    matching l n z (adjugate l n z f) =
      (tmDet l n z * f.1, tmDet l n z * f.2) := by
  apply Prod.ext <;> simp only [matching, adjugate, tmDet] <;> ring

theorem adjugate_matching (l : ℕ) (n z : ℂ) (f : Amplitudes) :
    adjugate l n z (matching l n z f) =
      (tmDet l n z * f.1, tmDet l n z * f.2) := by
  apply Prod.ext <;> simp only [matching, adjugate, tmDet] <;> ring

theorem solve_right_inverse (l : ℕ) (n z : ℂ) (h : tmDet l n z ≠ 0) (f : Amplitudes) :
    matching l n z (solve l n z f) = f := by
  have he := matching_adjugate l n z f
  apply Prod.ext
  · have h1 := congrArg Prod.fst he
    dsimp [matching, solve] at h1 ⊢
    field_simp
    simpa only [mul_comm] using h1
  · have h2 := congrArg Prod.snd he
    dsimp [matching, solve] at h2 ⊢
    field_simp
    simpa only [mul_comm] using h2

theorem solve_left_inverse (l : ℕ) (n z : ℂ) (h : tmDet l n z ≠ 0) (f : Amplitudes) :
    solve l n z (matching l n z f) = f := by
  have he := adjugate_matching l n z f
  simp only [solve, he, mul_div_cancel_left₀ _ h]

theorem outgoing_state_nonzero (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    xi l z ≠ 0 ∨ xiD l z ≠ 0 := by
  by_cases h : xi l z = 0
  · right
    intro hd
    have hw := hankel_wronskian l z hz
    rw [h, hd] at hw
    norm_num at hw
  · exact Or.inl h

/-- A determinant zero is exactly the existence of a nonzero solution of
the constructed two-amplitude matching system. -/
theorem matching_kernel_iff (l : ℕ) (n z : ℂ) (hz : z ≠ 0) :
    tmDet l n z = 0 ↔ ∃ v : Amplitudes, v ≠ 0 ∧ matching l n z v = 0 := by
  classical
  constructor
  · intro hd
    rcases outgoing_state_nonzero l z hz with hx | hxd
    · refine ⟨(xi l z, n * psi l (n * z)), ?_, ?_⟩
      · intro hv
        exact hx (congrArg Prod.fst hv)
      · apply Prod.ext
        · simp only [matching, Prod.fst_zero]
          ring
        · simp only [matching, Prod.snd_zero]
          dsimp only [tmDet] at hd
          linear_combination -hd
    · refine ⟨(xiD l z, psiD l (n * z)), ?_, ?_⟩
      · intro hv
        exact hxd (congrArg Prod.fst hv)
      · apply Prod.ext
        · exact hd
        · simp only [matching, Prod.snd_zero]
          ring
  · rintro ⟨v, hv, hm⟩
    by_contra hd
    have hsol := solve_left_inverse l n z hd v
    rw [hm] at hsol
    have hzsol : solve l n z 0 = 0 := by simp [solve, adjugate]
    rw [hzsol] at hsol
    exact hv hsol.symm

theorem psiD_hasDerivAt (l : ℕ) (z : ℂ) (hz : z ≠ 0) :
    HasDerivAt (psiD l) ((((l : ℂ) * (l + 1)) / z ^ 2 - 1) * psi l z) z := by
  convert ((xiD_hasDerivAt l z hz).add (xiMinusD_hasDerivAt l z hz)).div_const 2 using 1
  simp only [psi]
  ring

theorem tmDet_differentiableAt (l : ℕ) (n z : ℂ) (hn : n ≠ 0) (hz : z ≠ 0) :
    DifferentiableAt ℂ (tmDet l n) z := by
  have hnz := mul_ne_zero hn hz
  have hi := ((hasDerivAt_id z).const_mul n).differentiableAt
  have hfirst := (((psi_hasDerivAt l (n * z) hnz).differentiableAt.comp z hi).const_mul n).mul
    (xiD_hasDerivAt l z hz).differentiableAt
  exact hfirst.sub ((xi_hasDerivAt l z hz).differentiableAt.mul
    ((psiD_hasDerivAt l (n * z) hnz).differentiableAt.comp z hi))

theorem inverse_determinant_residue (l : ℕ) (n z₀ : ℂ)
    (hn : n ≠ 0) (hz : z₀ ≠ 0) (hd : tmDet l n z₀ = 0)
    (hs : deriv (tmDet l n) z₀ ≠ 0) :
    Tendsto (fun z => (z - z₀) / tmDet l n z) (𝓝[≠] z₀)
      (𝓝 (deriv (tmDet l n) z₀)⁻¹) := by
  have ht := hasDerivAt_iff_tendsto_slope.mp
    (tmDet_differentiableAt l n z₀ hn hz).hasDerivAt
  have hi := ht.inv₀ hs
  simpa only [slope_def_field, hd, sub_zero, inv_div] using hi

theorem determinant_eventually_nonzero (l : ℕ) (n z₀ : ℂ)
    (hn : n ≠ 0) (hz : z₀ ≠ 0) (hd : tmDet l n z₀ = 0)
    (hs : deriv (tmDet l n) z₀ ≠ 0) :
    ∀ᶠ z in 𝓝[≠] z₀, tmDet l n z ≠ 0 := by
  have ht := hasDerivAt_iff_tendsto_slope.mp
    (tmDet_differentiableAt l n z₀ hn hz).hasDerivAt
  have he := ht.eventually (eventually_ne_nhds hs)
  filter_upwards [he] with z hz'
  rw [slope_def_field, hd, sub_zero] at hz'
  exact (div_ne_zero_iff.mp hz').1

theorem adjugate_continuousAt (l : ℕ) (n z₀ : ℂ) (hn : n ≠ 0) (hz : z₀ ≠ 0)
    (f : Amplitudes) : ContinuousAt (fun z => adjugate l n z f) z₀ := by
  have hnz := mul_ne_zero hn hz
  have hi : ContinuousAt (fun z : ℂ => n * z) z₀ := continuousAt_const.mul continuousAt_id
  exact (((xiD_hasDerivAt l z₀ hz).continuousAt.mul continuousAt_const).sub
    ((xi_hasDerivAt l z₀ hz).continuousAt.mul continuousAt_const)).prodMk
      ((((psiD_hasDerivAt l (n * z₀) hnz).continuousAt.comp hi).mul continuousAt_const).sub
        ((continuousAt_const.mul ((psi_hasDerivAt l (n * z₀) hnz).continuousAt.comp hi)).mul
          continuousAt_const))

/-- Actual punctured-neighborhood limit of the inverse matching map.
The determinant is also proved nonzero on a sufficiently small punctured
neighborhood, so this is a genuine simple-pole inverse residue. -/
theorem solve_residue_limit (l : ℕ) (n z₀ : ℂ)
    (hn : n ≠ 0) (hz : z₀ ≠ 0) (hd : tmDet l n z₀ = 0)
    (hs : deriv (tmDet l n) z₀ ≠ 0) (f : Amplitudes) :
    Tendsto (fun z => (z - z₀) • solve l n z f) (𝓝[≠] z₀) (𝓝 (residue l n z₀ f)) := by
  have hr := inverse_determinant_residue l n z₀ hn hz hd hs
  have hc : Tendsto (fun z => adjugate l n z f) (𝓝[≠] z₀)
      (𝓝 (adjugate l n z₀ f)) :=
    (adjugate_continuousAt l n z₀ hn hz f).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hr.smul hc
  convert hlim using 1
  · funext z
    apply Prod.ext <;> simp [solve, smul_eq_mul, div_eq_mul_inv] <;> ring
  · congr 1
    apply Prod.ext <;> simp [residue, smul_eq_mul, div_eq_mul_inv] <;> ring

theorem residue_in_matching_kernel (l : ℕ) (n z : ℂ) (hd : tmDet l n z = 0)
    (f : Amplitudes) : matching l n z (residue l n z f) = 0 := by
  have he := matching_adjugate l n z f
  rw [hd] at he
  apply Prod.ext
  · have h1 := congrArg Prod.fst he
    dsimp [matching, residue] at h1 ⊢
    calc
      _ = (n * psi l (n * z) * (adjugate l n z f).1 -
        xi l z * (adjugate l n z f).2) / deriv (tmDet l n) z := by ring
      _ = 0 := by rw [h1]; simp
  · have h2 := congrArg Prod.snd he
    dsimp [matching, residue] at h2 ⊢
    calc
      _ = (psiD l (n * z) * (adjugate l n z f).1 -
        xiD l z * (adjugate l n z f).2) / deriv (tmDet l n) z := by ring
      _ = 0 := by rw [h2]; simp

theorem residue_nonzero (l : ℕ) (n z : ℂ) (hz : z ≠ 0)
    (hs : deriv (tmDet l n) z ≠ 0) : ∃ f : Amplitudes, residue l n z f ≠ 0 := by
  rcases outgoing_state_nonzero l z hz with hx | hxd
  · refine ⟨(0, 1), ?_⟩
    intro he
    have h1 := congrArg Prod.fst he
    simp only [residue, adjugate, mul_zero, mul_one, zero_sub, Prod.fst_zero] at h1
    exact (div_ne_zero (neg_ne_zero.mpr hx) hs) h1
  · refine ⟨(1, 0), ?_⟩
    intro he
    have h1 := congrArg Prod.fst he
    simp only [residue, adjugate, mul_zero, mul_one, sub_zero, Prod.fst_zero] at h1
    exact (div_ne_zero hxd hs) h1

/-- An explicit nonzero-vector factorization of the residue image: its
range is a nonzero complex line, rather than merely having a zero determinant. -/
theorem residue_rank_one_factor (l : ℕ) (n z : ℂ) (hz : z ≠ 0)
    (hd : tmDet l n z = 0) (hs : deriv (tmDet l n) z ≠ 0) :
    ∃ v : Amplitudes, v ≠ 0 ∧ (∃ f : Amplitudes, residue l n z f = v) ∧
      ∀ f : Amplitudes, ∃ a : ℂ, residue l n z f = a • v := by
  classical
  by_cases hxd : xiD l z = 0
  · have hx : xi l z ≠ 0 := (outgoing_state_nonzero l z hz).resolve_right (not_ne_iff.mpr hxd)
    have hpd : psiD l (n * z) = 0 := by
      dsimp only [tmDet] at hd
      rw [hxd, mul_zero, zero_sub] at hd
      exact (mul_eq_zero.mp (neg_eq_zero.mp hd)).resolve_left hx
    refine ⟨residue l n z (0, 1), ?_, ⟨(0, 1), rfl⟩, ?_⟩
    · intro hv
      have h1 := congrArg Prod.fst hv
      simp only [residue, adjugate, mul_zero, mul_one, zero_sub, Prod.fst_zero] at h1
      exact (div_ne_zero (neg_ne_zero.mpr hx) hs) h1
    · intro f
      refine ⟨f.2, ?_⟩
      apply Prod.ext <;> simp [residue, adjugate, hxd, hpd, smul_eq_mul] <;> ring
  · refine ⟨residue l n z (1, 0), ?_, ⟨(1, 0), rfl⟩, ?_⟩
    · intro hv
      have h1 := congrArg Prod.fst hv
      simp only [residue, adjugate, mul_zero, mul_one, sub_zero, Prod.fst_zero] at h1
      exact (div_ne_zero hxd hs) h1
    · intro f
      refine ⟨f.1 - xi l z / xiD l z * f.2, ?_⟩
      apply Prod.ext
      · simp only [residue, adjugate, Prod.smul_fst, smul_eq_mul, mul_one, mul_zero, sub_zero]
        field_simp
        ring
      · simp only [residue, adjugate, Prod.smul_snd, smul_eq_mul, mul_one, mul_zero, sub_zero]
        field_simp
        dsimp only [tmDet] at hd
        linear_combination -(deriv (tmDet l n) z) * f.2 * hd

/-- Actual existence of an inverse matching-map pole with a nonzero
matching-kernel residue and arbitrarily large frequency-to-decay ratio.
No determinant-zero or simple-pole premise remains in this conclusion. -/
theorem exists_high_quality_matching_pole (l : ℕ) (n : ℝ) (hn : 1 < n)
    (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ z₀ : ℂ, z₀ ≠ 0 ∧ tmDet l (n : ℂ) z₀ = 0 ∧ L < z₀.re ∧ z₀.im < 0 ∧
      Q < z₀.re / (-2 * z₀.im) ∧
      (∀ᶠ z in 𝓝[≠] z₀, tmDet l (n : ℂ) z ≠ 0) ∧
      ∃ f v : Amplitudes, v ≠ 0 ∧ matching l (n : ℂ) z₀ v = 0 ∧
        Tendsto (fun z => (z - z₀) • solve l (n : ℂ) z f) (𝓝[≠] z₀) (𝓝 v) := by
  obtain ⟨z₀, hz, hd, hs, hL, hi, hratio⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros l n hn L Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  obtain ⟨f, hf⟩ := residue_nonzero l (n : ℂ) z₀ hz hs
  exact ⟨z₀, hz, hd, hL, hi, hratio,
    determinant_eventually_nonzero l (n : ℂ) z₀ hn0 hz hd hs,
    f, residue l (n : ℂ) z₀ f, hf, residue_in_matching_kernel l (n : ℂ) z₀ hd f,
    solve_residue_limit l (n : ℂ) z₀ hn0 hz hd hs f⟩

end OQ14.ModalMatching

#print axioms OQ14.ModalMatching.matching_adjugate
#print axioms OQ14.ModalMatching.adjugate_matching
#print axioms OQ14.ModalMatching.solve_right_inverse
#print axioms OQ14.ModalMatching.solve_left_inverse
#print axioms OQ14.ModalMatching.outgoing_state_nonzero
#print axioms OQ14.ModalMatching.matching_kernel_iff
#print axioms OQ14.ModalMatching.psiD_hasDerivAt
#print axioms OQ14.ModalMatching.tmDet_differentiableAt
#print axioms OQ14.ModalMatching.inverse_determinant_residue
#print axioms OQ14.ModalMatching.determinant_eventually_nonzero
#print axioms OQ14.ModalMatching.adjugate_continuousAt
#print axioms OQ14.ModalMatching.solve_residue_limit
#print axioms OQ14.ModalMatching.residue_in_matching_kernel
#print axioms OQ14.ModalMatching.residue_nonzero
#print axioms OQ14.ModalMatching.residue_rank_one_factor
#print axioms OQ14.ModalMatching.exists_high_quality_matching_pole
