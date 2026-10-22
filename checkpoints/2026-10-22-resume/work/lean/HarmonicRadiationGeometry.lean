import PuncturedMaxwellScaling
import FischerDecomposition

/-! Actual homogeneous angular factors and uniform directional bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.HarmonicRadiationGeometry
open Set Metric OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.DebyeRadialTrace

theorem homogeneous_gradient (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (r : ℝ) (x : Space) (i : Fin 3) :
    (r : ℂ)*dcoord (complexEvaluate p) (r • x) i=(r : ℂ)^l*dcoord (complexEvaluate p) x i := by
  have he : (fun y : Space => complexEvaluate p (r • y))=
      fun y => (r : ℂ)^l*complexEvaluate p y :=
    funext (FischerDecomposition.complexEvaluate_smul p l hp r)
  have hd := congrArg (fun f : Space → ℂ => dcoord f x i) he
  dsimp only at hd
  rw [ModalScaling.dcoord_comp_smul r _ x
    ((complexEvaluate_regular p).differentiable (by simp)).differentiableAt,
    partial_const_mul ((complexEvaluate_regular p).differentiable (by simp)).differentiableAt] at hd
  exact hd

theorem angularToroidal_smul (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l)
    (r : ℝ) (x : Space) : angularToroidal p (r • x)=(r : ℂ)^l • angularToroidal p x := by
  have h0 := homogeneous_gradient p l hp r x 0
  have h1 := homogeneous_gradient p l hp r x 1
  have h2 := homogeneous_gradient p l hp r x 2
  ext i
  fin_cases i <;> simp [angularToroidal,PiLp.smul_apply,Complex.ofReal_mul]
  · linear_combination (x 2 : ℂ)*h1-(x 1 : ℂ)*h2
  · linear_combination (x 0 : ℂ)*h2-(x 2 : ℂ)*h0
  · linear_combination (x 1 : ℂ)*h0-(x 0 : ℂ)*h1

theorem angularToroidal_continuous (p : Poly) : Continuous (angularToroidal p) := by
  have hc (j : Fin 3) : Continuous (fun x : Space => dcoord (complexEvaluate p) x j) := by
    simp_rw [complexEvaluate_partial]
    exact (complexEvaluate_regular _).continuous
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [angularToroidal] <;> fun_prop

theorem normalized_toroidal_bound (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∃ M : ℝ,0≤M ∧ ∀ x : Space,x≠0 →
      ‖((‖x‖ : ℂ)^l)⁻¹ • angularToroidal p x‖≤M := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn
    (angularToroidal_continuous p).continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x hx
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hn : ‖‖x‖⁻¹ • x‖=1 := by simp [norm_smul,abs_of_pos hr,hr.ne']
  have hb : ‖x‖⁻¹ • x∈closedBall (0 : Space) 1 := by simp only [mem_closedBall_zero_iff,hn,le_refl]
  have he := angularToroidal_smul p l hp ‖x‖ (‖x‖⁻¹ • x)
  rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul] at he
  rw [he,smul_smul,inv_mul_cancel₀ (pow_ne_zero l hr0),one_smul]
  exact (hM _ hb).trans (le_max_left _ _)

end OQ14.HarmonicRadiationGeometry

#print axioms OQ14.HarmonicRadiationGeometry.homogeneous_gradient
#print axioms OQ14.HarmonicRadiationGeometry.angularToroidal_smul
#print axioms OQ14.HarmonicRadiationGeometry.angularToroidal_continuous
#print axioms OQ14.HarmonicRadiationGeometry.normalized_toroidal_bound
