import RadialReference
import Mathlib.Analysis.ODE.Gronwall

/-! Quantitative comparison of the actual radial ODE with its constant
coefficient reference, with the angular error derived from the literal ODE. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RadialApproximation
open Set Filter OQ14.RadialStack OQ14.RadialLayer OQ14.RadialPropagation
open scoped Topology

def rhs (σ V : ℝ) (s : State) : State := ((σ : ℂ)*s.2,(V : ℂ)*s.1)

theorem rhs_norm (σ V : ℝ) (s : State) :
    ‖rhs σ V s‖ ≤ (|σ|+|V|)*‖s‖ := by
  simp only [rhs,Prod.norm_mk,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  apply max_le
  · exact (mul_le_mul_of_nonneg_left (norm_snd_le s) (abs_nonneg σ)).trans
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg V]) (norm_nonneg s))
  · exact (mul_le_mul_of_nonneg_left (norm_fst_le s) (abs_nonneg V)).trans
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg σ]) (norm_nonneg s))

def state (l : ℕ) (q σ R : ℝ) (s : State) (x : ℝ) : State :=
  (value l q σ (initialAlpha l q σ R s.1 s.2) (initialBeta l q σ R s.1 s.2) x,
   momentum l q σ (initialAlpha l q σ R s.1 s.2) (initialBeta l q σ R s.1 s.2) x)

theorem state_initial (l : ℕ) (q σ R : ℝ) (s : State)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hR : R ≠ 0) : state l q σ R s R = s :=
  Prod.ext (initial_value l q σ R s.1 s.2 hq hσ hR)
    (initial_momentum l q σ R s.1 s.2 hq hσ hR)

theorem state_hasDerivAt (l : ℕ) (q σ R : ℝ) (s : State) (x : ℝ)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hx : x ≠ 0) :
    HasDerivAt (state l q σ R s) (rhs σ (potential l q σ x) (state l q σ R s x)) x := by
  obtain ⟨hu,hp⟩ := RadialLayer.solution_ode l q σ
    (initialAlpha l q σ R s.1 s.2) (initialBeta l q σ R s.1 s.2) x hq hσ hx
  exact hu.prodMk hp

theorem state_norm_bound (l : ℕ) (q σ R : ℝ) (s : State) (w x : ℝ)
    (hq : q ≠ 0) (hσ : 0 < σ) (hR : 0 < R) (hx : x ∈ Icc R (R+w)) :
    ‖state l q σ R s x‖ ≤ ‖s‖*Real.exp (generatorBound l q σ R*(x-R)) := by
  have hc : ContinuousOn (state l q σ R s) (Icc R (R+w)) := by
    intro y hy
    exact (state_hasDerivAt l q σ R s y hq hσ.ne'
      (ne_of_gt (hR.trans_le hy.1))).continuousAt.continuousWithinAt
  have hd (y : ℝ) (hy : y ∈ Ico R (R+w)) :=
    (state_hasDerivAt l q σ R s y hq hσ.ne' (ne_of_gt (hR.trans_le hy.1))).hasDerivWithinAt (s := Ici y)
  have hb (y : ℝ) (hy : y ∈ Ico R (R+w)) :
      ‖rhs σ (potential l q σ y) (state l q σ R s y)‖ ≤
        generatorBound l q σ R*‖state l q σ R s y‖+0 := by
    rw [add_zero]
    exact (rhs_norm _ _ _).trans (mul_le_mul_of_nonneg_right
      (potential_bound l q σ R y hσ hR hy.1) (norm_nonneg _))
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc hd
    (by rw [state_initial l q σ R s hq hσ.ne' hR.ne']) hb x hx
  simpa only [gronwallBound_ε0] using h

theorem generatorBound_le_one (l : ℕ) (q σ R : ℝ) (hσ : 0 < σ) (hR : 1 ≤ R) :
    generatorBound l q σ R ≤ generatorBound l q σ 1 := by
  have hν : 0 ≤ HankelEnergy.angular l := by unfold HankelEnergy.angular; positivity
  have hR2 : 1 ≤ R^2 := by nlinarith
  have h := div_le_div_of_nonneg_left hν hσ (by nlinarith : σ ≤ σ*R^2)
  simpa [generatorBound] using add_le_add_right (add_le_add_left h σ) (q^2/σ)

theorem state_norm_uniform (l : ℕ) (q σ R : ℝ) (s : State) (w x : ℝ)
    (hq : q ≠ 0) (hσ : 0 < σ) (hR : 1 ≤ R) (hx : x ∈ Icc R (R+w)) :
    ‖state l q σ R s x‖ ≤ ‖s‖*Real.exp (generatorBound l q σ 1*w) := by
  have hR0 : 0 < R := by linarith
  have hC : 0 ≤ generatorBound l q σ 1 := by
    unfold generatorBound HankelEnergy.angular
    positivity
  apply (state_norm_bound l q σ R s w x hq hσ hR0 hx).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg s)
  calc
    generatorBound l q σ R*(x-R) ≤ generatorBound l q σ 1*(x-R) :=
      mul_le_mul_of_nonneg_right (generatorBound_le_one l q σ R hσ hR) (sub_nonneg.mpr hx.1)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith [hx.2]) hC

theorem reference_hasDerivAt (q σ R : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (s : State) (x : ℝ) :
    HasDerivAt (fun y => RadialReference.solution q σ hq hσ s (y-R))
      (rhs σ (-q^2/σ) (RadialReference.solution q σ hq hσ s (x-R))) x := by
  obtain ⟨hu,hp⟩ := RadialReference.solution_ode q σ hq hσ s (x-R)
  have hshift : HasDerivAt (fun y : ℝ => y-R) 1 x := by
    simpa using (hasDerivAt_id x).sub_const R
  convert (hu.prodMk hp).scomp x hshift using 1
  simp only [one_smul,id_eq,rhs]

theorem rhs_difference (σ V W : ℝ) (s t : State) :
    rhs σ V s-rhs σ W t = rhs σ W (s-t)+(0,((V-W : ℝ) : ℂ)*s.1) := by
  apply Prod.ext <;> simp [rhs] <;> ring

theorem angular_perturbation_bound (l : ℕ) (q σ R x : ℝ) (s : State)
    (hσ : 0 < σ) (hR : 0 < R) (hx : R ≤ x) :
    ‖((0,((potential l q σ x-(-q^2/σ) : ℝ) : ℂ)*s.1) : State)‖ ≤
      (HankelEnergy.angular l/(σ*R^2))*‖s‖ := by
  have hν : 0 ≤ HankelEnergy.angular l := by unfold HankelEnergy.angular; positivity
  have hx0 : 0 < x := hR.trans_le hx
  have he : potential l q σ x-(-q^2/σ)=HankelEnergy.angular l/(σ*x^2) := by
    unfold potential
    ring
  have hnn : 0 ≤ HankelEnergy.angular l/(σ*x^2) := div_nonneg hν (by positivity)
  simp only [he,Prod.norm_mk,norm_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [max_eq_right (mul_nonneg (abs_nonneg _) (norm_nonneg _)),abs_of_nonneg hnn]
  apply mul_le_mul
  · exact div_le_div_of_nonneg_left hν (by positivity)
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hR.le hx0.le).mpr hx) hσ.le)
  · exact norm_fst_le s
  · exact norm_nonneg _
  · positivity

def referenceBound (q σ : ℝ) : ℝ := σ+q^2/σ

theorem referenceBound_pos (q σ : ℝ) (hσ : 0 < σ) : 0 < referenceBound q σ := by
  unfold referenceBound
  positivity

theorem reference_rhs_norm (q σ : ℝ) (hσ : 0 < σ) (s : State) :
    ‖rhs σ (-q^2/σ) s‖ ≤ referenceBound q σ*‖s‖ := by
  convert rhs_norm σ (-q^2/σ) s using 1
  simp only [referenceBound,abs_of_pos hσ,abs_div,abs_neg,abs_pow,abs_of_nonneg (sq_nonneg q)]

theorem actual_reference_error (l : ℕ) (q σ R : ℝ) (s : State) (w : ℝ)
    (hq : q ≠ 0) (hσ : 0 < σ) (hR : 1 ≤ R) (hw : 0 ≤ w) :
    ‖state l q σ R s (R+w)-RadialReference.solution q σ hq hσ.ne' s w‖ ≤
      ((HankelEnergy.angular l/(σ*R^2))*(‖s‖*Real.exp (generatorBound l q σ 1*w))) /
        referenceBound q σ * (Real.exp (referenceBound q σ*w)-1) := by
  let f := fun x => state l q σ R s x-RadialReference.solution q σ hq hσ.ne' s (x-R)
  let fD := fun x => rhs σ (potential l q σ x) (state l q σ R s x)-
    rhs σ (-q^2/σ) (RadialReference.solution q σ hq hσ.ne' s (x-R))
  let ε := (HankelEnergy.angular l/(σ*R^2))*(‖s‖*Real.exp (generatorBound l q σ 1*w))
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hd (x : ℝ) (hx : R ≤ x) : HasDerivAt f (fD x) x :=
    (state_hasDerivAt l q σ R s x hq hσ.ne' (ne_of_gt (hR0.trans_le hx))).sub
      (reference_hasDerivAt q σ R hq hσ.ne' s x)
  have hc : ContinuousOn f (Icc R (R+w)) :=
    fun x hx => (hd x hx.1).continuousAt.continuousWithinAt
  have h0 : ‖f R‖ ≤ (0 : ℝ) := by
    simp [f,state_initial l q σ R s hq hσ.ne' hR0.ne',RadialReference.solution_zero]
  have hb (x : ℝ) (hx : x ∈ Ico R (R+w)) :
      ‖fD x‖ ≤ referenceBound q σ*‖f x‖+ε := by
    dsimp only [fD]
    rw [rhs_difference]
    apply (norm_add_le _ _).trans
    apply add_le_add (reference_rhs_norm q σ hσ _)
    exact (angular_perturbation_bound l q σ R x _ hσ hR0 hx.1).trans
      (mul_le_mul_of_nonneg_left
        (state_norm_uniform l q σ R s w x hq hσ hR ⟨hx.1,hx.2.le⟩)
        (by unfold HankelEnergy.angular; positivity))
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hc
    (fun x hx => (hd x hx.1).hasDerivWithinAt) h0 hb (R+w) ⟨by linarith,le_rfl⟩
  simpa only [f,ε,add_sub_cancel_left,gronwallBound_of_K_ne_0 (referenceBound_pos q σ hσ).ne',
    zero_mul,zero_add] using h

def errorConstant (l : ℕ) (q σ w : ℝ) : ℝ :=
  ((HankelEnergy.angular l/σ)*Real.exp (generatorBound l q σ 1*w))/
    referenceBound q σ*(Real.exp (referenceBound q σ*w)-1)

theorem actual_reference_error_scaled (l : ℕ) (q σ R : ℝ) (s : State) (w : ℝ)
    (hq : q ≠ 0) (hσ : 0 < σ) (hR : 1 ≤ R) (hw : 0 ≤ w) :
    ‖state l q σ R s (R+w)-RadialReference.solution q σ hq hσ.ne' s w‖ ≤
      errorConstant l q σ w*‖s‖/R^2 := by
  apply (actual_reference_error l q σ R s w hq hσ hR hw).trans_eq
  unfold errorConstant
  ring

theorem reference_continuous (q σ w : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) :
    Continuous (fun s : State => RadialReference.solution q σ hq hσ s w) := by
  exact (continuous_const.mul continuous_fst |>.add (continuous_const.mul continuous_snd)).prodMk
    (continuous_const.mul continuous_fst |>.add (continuous_const.mul continuous_snd))

theorem actual_reference_limit (l : ℕ) (q σ w : ℝ) (hq : q ≠ 0) (hσ : 0 < σ)
    (hw : 0 ≤ w) (s : ℝ → State) (s₀ : State) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R : ℝ => state l q σ R (s R) (R+w)) atTop
      (𝓝 (RadialReference.solution q σ hq hσ.ne' s₀ w)) := by
  have hi : Tendsto (fun R : ℝ => (R^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  have hm : Tendsto (fun R : ℝ => errorConstant l q σ w*‖s R‖/R^2) atTop (𝓝 0) := by
    simpa only [mul_zero,div_eq_mul_inv] using (hs.norm.const_mul (errorConstant l q σ w)).mul hi
  have he : Tendsto (fun R : ℝ => state l q σ R (s R) (R+w)-
      RadialReference.solution q σ hq hσ.ne' (s R) w) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hm
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
    exact actual_reference_error_scaled l q σ R (s R) w hq hσ hR hw
  have hr := (reference_continuous q σ w hq hσ.ne').continuousAt.tendsto.comp hs
  simpa only [Function.comp_def,sub_add_cancel,zero_add] using he.add hr

theorem state_transfer (l : ℕ) (q σ R x : ℝ) (s : State)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hR : R ≠ 0) (hx : x ≠ 0) :
    state l q σ R s x = act (transfer l q σ R x hq hσ hR hx) s :=
  Prod.ext (transfer_value l q σ R x s.1 s.2 hq hσ hR hx)
    (transfer_momentum l q σ R x s.1 s.2 hq hσ hR hx)

end OQ14.RadialApproximation

#print axioms OQ14.RadialApproximation.rhs_norm
#print axioms OQ14.RadialApproximation.state_initial
#print axioms OQ14.RadialApproximation.state_hasDerivAt
#print axioms OQ14.RadialApproximation.state_norm_bound
#print axioms OQ14.RadialApproximation.generatorBound_le_one
#print axioms OQ14.RadialApproximation.state_norm_uniform
#print axioms OQ14.RadialApproximation.reference_hasDerivAt
#print axioms OQ14.RadialApproximation.rhs_difference
#print axioms OQ14.RadialApproximation.angular_perturbation_bound
#print axioms OQ14.RadialApproximation.referenceBound_pos
#print axioms OQ14.RadialApproximation.reference_rhs_norm
#print axioms OQ14.RadialApproximation.actual_reference_error
#print axioms OQ14.RadialApproximation.actual_reference_error_scaled
#print axioms OQ14.RadialApproximation.reference_continuous
#print axioms OQ14.RadialApproximation.actual_reference_limit
#print axioms OQ14.RadialApproximation.state_transfer
