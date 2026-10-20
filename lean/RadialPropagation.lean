import RadialLayer

/-! Quantitative propagation for actual homogeneous radial solutions. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.RadialPropagation

open Set OQ14.RadialGreen OQ14.RadialLayer

def energy (u p : ℂ) : ℝ := Complex.normSq u+Complex.normSq p

theorem energy_nonnegative (u p : ℂ) : 0 ≤ energy u p :=
  add_nonneg (Complex.normSq_nonneg u) (Complex.normSq_nonneg p)

theorem load_absolute_bound (u p : ℂ) : 2*|radialLoad u p| ≤ energy u p := by
  rw [radialLoad_components]
  unfold energy
  simp only [Complex.normSq_apply]
  rcases le_total 0 (p.re*u.re+p.im*u.im) with h|h
  · rw [abs_of_nonneg h]
    nlinarith [sq_nonneg (u.re-p.re),sq_nonneg (u.im-p.im)]
  · rw [abs_of_nonpos h]
    nlinarith [sq_nonneg (u.re+p.re),sq_nonneg (u.im+p.im)]

theorem energy_derivative_bound (u p : ℂ) (σ V C : ℝ) (hC : |σ|+|V| ≤ C) :
    |2*(σ+V)*radialLoad u p| ≤ C*energy u p := by
  have hb := load_absolute_bound u p
  calc
    _ = |σ+V| * (2 * |radialLoad u p|) := by rw [abs_mul,abs_mul]; norm_num; ring
    _ ≤ (|σ|+|V|)*energy u p := mul_le_mul (abs_add _ _) hb (by positivity) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right hC (energy_nonnegative u p)

theorem scalar_growth (f fD : ℝ → ℝ) (C a b : ℝ) (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (fD x) x)
    (hbound : ∀ x ∈ Ioo a b, |fD x| ≤ C*f x) :
    f b ≤ Real.exp (C*(b-a))*f a ∧ f a ≤ Real.exp (C*(b-a))*f b := by
  have hminus (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (-C*(t-a)))
      (Real.exp (-C*(x-a))*(-C)) x := by
    convert (((hasDerivAt_id x).sub_const a).const_mul (-C)).exp using 1
    simp only [id_eq]
    ring
  have hplus (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (C*(t-a)))
      (Real.exp (C*(x-a))*C) x := by
    convert (((hasDerivAt_id x).sub_const a).const_mul C).exp using 1
    simp only [id_eq]
    ring
  have hm : AntitoneOn (fun x => f x*Real.exp (-C*(x-a))) (Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (hc.mul (Real.continuous_exp.comp (continuous_const.mul
        (continuous_id.sub continuous_const))).continuousOn)
    · intro x hx
      have hi : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      exact ((hd x hi).mul (hminus x)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hi : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      change deriv (fun y => f y*Real.exp (-C*(y-a))) x ≤ 0
      rw [((hd x hi).mul (hminus x)).deriv]
      have hb := (le_abs_self (fD x)).trans (hbound x hi)
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hb)
        (Real.exp_pos (-C*(x-a))).le]
  have hp : MonotoneOn (fun x => f x*Real.exp (C*(x-a))) (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b)
      (hc.mul (Real.continuous_exp.comp (continuous_const.mul
        (continuous_id.sub continuous_const))).continuousOn)
    · intro x hx
      have hi : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      exact ((hd x hi).mul (hplus x)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hi : x ∈ Ioo a b := by simpa only [interior_Icc] using hx
      change 0 ≤ deriv (fun y => f y*Real.exp (C*(y-a))) x
      rw [((hd x hi).mul (hplus x)).deriv]
      have hb := (neg_le_abs (fD x)).trans (hbound x hi)
      nlinarith [mul_nonneg (by linarith : 0 ≤ fD x+C*f x)
        (Real.exp_pos (C*(x-a))).le]
  have hmab := hm ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  have hpab := hp ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ hab
  simp only [sub_self,mul_zero,Real.exp_zero,mul_one] at hmab hpab
  constructor
  · rw [neg_mul,Real.exp_neg,← div_eq_mul_inv] at hmab
    exact ((div_le_iff₀ (Real.exp_pos _)).mp hmab).trans_eq (mul_comm _ _)
  · simpa only [mul_comm] using hpab

theorem solution_energy_hasDerivAt (l : ℕ) (q σ : ℝ) (α β : ℂ) (x : ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (fun x => energy (value l q σ α β x) (momentum l q σ α β x))
      (2*(σ+potential l q σ x)*radialLoad (value l q σ α β x) (momentum l q σ α β x)) x := by
  obtain ⟨hu,hp⟩ := solution_ode l q σ α β x hq hσ hx
  obtain ⟨heu,hep⟩ := barrier_state_hasDerivAt hu hp
  convert heu.add hep using 1
  ring

theorem solution_energy_bound (l : ℕ) (q σ : ℝ) (α β : ℂ) (C a b : ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (ha : 0 < a) (hab : a ≤ b)
    (hbound : ∀ x ∈ Ioo a b, |σ|+|potential l q σ x| ≤ C) :
    energy (value l q σ α β b) (momentum l q σ α β b) ≤
      Real.exp (C*(b-a))*energy (value l q σ α β a) (momentum l q σ α β a) ∧
    energy (value l q σ α β a) (momentum l q σ α β a) ≤
      Real.exp (C*(b-a))*energy (value l q σ α β b) (momentum l q σ α β b) := by
  apply scalar_growth _ _ C a b hab
  · intro x hx
    exact (solution_energy_hasDerivAt l q σ α β x hq hσ
      (ne_of_gt (ha.trans_le hx.1))).continuousAt.continuousWithinAt
  · intro x hx
    exact solution_energy_hasDerivAt l q σ α β x hq hσ (ne_of_gt (ha.trans hx.1))
  · intro x hx
    exact energy_derivative_bound _ _ σ (potential l q σ x) C (hbound x hx)

def generatorBound (l : ℕ) (q σ a : ℝ) : ℝ :=
  σ+OQ14.HankelEnergy.angular l/(σ*a^2)+q^2/σ

theorem potential_bound (l : ℕ) (q σ a x : ℝ) (hσ : 0 < σ)
    (ha : 0 < a) (hax : a ≤ x) :
    |σ|+|potential l q σ x| ≤ generatorBound l q σ a := by
  have hx : 0 < x := ha.trans_le hax
  have hν : 0 ≤ OQ14.HankelEnergy.angular l := by unfold OQ14.HankelEnergy.angular; positivity
  have hden : σ*a^2 ≤ σ*x^2 := mul_le_mul_of_nonneg_left
    (sq_le_sq₀ ha.le hx.le |>.mpr hax) hσ.le
  have hdiv := div_le_div_of_nonneg_left hν (by positivity : 0 < σ*a^2) hden
  have htriangle := abs_sub (OQ14.HankelEnergy.angular l/(σ*x^2)) (q^2/σ)
  rw [abs_of_nonneg (div_nonneg hν (by positivity)),abs_of_nonneg (div_nonneg (sq_nonneg q) hσ.le)] at htriangle
  rw [abs_of_pos hσ]
  unfold potential generatorBound
  linarith

theorem actual_layer_energy_bound (l : ℕ) (q σ : ℝ) (α β : ℂ) (a b : ℝ)
    (hq : q ≠ 0) (hσ : 0 < σ) (ha : 0 < a) (hab : a ≤ b) :
    energy (value l q σ α β b) (momentum l q σ α β b) ≤
      Real.exp (generatorBound l q σ a*(b-a))*energy (value l q σ α β a) (momentum l q σ α β a) ∧
    energy (value l q σ α β a) (momentum l q σ α β a) ≤
      Real.exp (generatorBound l q σ a*(b-a))*energy (value l q σ α β b) (momentum l q σ α β b) :=
  solution_energy_bound l q σ α β (generatorBound l q σ a) a b hq hσ.ne' ha hab
    (fun x hx => potential_bound l q σ a x hσ ha hx.1.le)

theorem potential_nonnegative (l : ℕ) (q σ b x : ℝ) (hσ : 0 < σ)
    (hx : 0 < x) (hxb : x ≤ b)
    (hbarrier : q^2*b^2 ≤ OQ14.HankelEnergy.angular l) : 0 ≤ potential l q σ x := by
  have hb : 0 < b := hx.trans_le hxb
  have hxx : x^2 ≤ b^2 := (sq_le_sq₀ hx.le hb.le).mpr hxb
  have hν : q^2*x^2 ≤ OQ14.HankelEnergy.angular l :=
    (mul_le_mul_of_nonneg_left hxx (sq_nonneg q)).trans hbarrier
  have he : potential l q σ x = (OQ14.HankelEnergy.angular l-q^2*x^2)/(σ*x^2) := by
    unfold potential
    field_simp
    ring
  rw [he]
  exact div_nonneg (sub_nonneg.mpr hν) (by positivity)

theorem actual_layer_barrier (l : ℕ) (q σ : ℝ) (α β : ℂ) (a b : ℝ)
    (hq : q ≠ 0) (hσ : 0 < σ) (ha : 0 < a) (hab : a ≤ b)
    (hbarrier : q^2*b^2 ≤ OQ14.HankelEnergy.angular l)
    (hright : radialLoad (value l q σ α β b) (momentum l q σ α β b) ≤ 0) :
    MonotoneOn (fun x => radialLoad (value l q σ α β x) (momentum l q σ α β x)) (Icc a b) ∧
    AntitoneOn (fun x => Complex.normSq (value l q σ α β x)) (Icc a b) ∧
    AntitoneOn (fun x => Complex.normSq (momentum l q σ α β x)) (Icc a b) := by
  apply barrier_interval_monotonicity hab
  · intro x hx
    exact (solution_ode l q σ α β x hq hσ.ne' (ne_of_gt (ha.trans_le hx.1))).1.continuousAt.continuousWithinAt
  · intro x hx
    exact (solution_ode l q σ α β x hq hσ.ne' (ne_of_gt (ha.trans_le hx.1))).2.continuousAt.continuousWithinAt
  · intro x hx
    exact solution_ode l q σ α β x hq hσ.ne' (ne_of_gt (ha.trans hx.1))
  · intro x hx
    exact hσ.le
  · intro x hx
    exact potential_nonnegative l q σ b x hσ (ha.trans hx.1) hx.2.le hbarrier
  · exact hright

end OQ14.RadialPropagation

#print axioms OQ14.RadialPropagation.energy_nonnegative
#print axioms OQ14.RadialPropagation.load_absolute_bound
#print axioms OQ14.RadialPropagation.energy_derivative_bound
#print axioms OQ14.RadialPropagation.scalar_growth
#print axioms OQ14.RadialPropagation.solution_energy_hasDerivAt
#print axioms OQ14.RadialPropagation.solution_energy_bound
#print axioms OQ14.RadialPropagation.potential_bound
#print axioms OQ14.RadialPropagation.actual_layer_energy_bound
#print axioms OQ14.RadialPropagation.potential_nonnegative
#print axioms OQ14.RadialPropagation.actual_layer_barrier
