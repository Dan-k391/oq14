import HarmonicRadiationGeometry

/-! Uniform angular control of radial and poloidal homogeneous factors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.HarmonicRadiationFactors
open Set Metric OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.DebyeRadialTrace

def radial (p : Poly) (x : Space) : Vector := fun i => (x i : ℂ)*complexEvaluate p x
def poloidal (p : Poly) (x : Space) : Vector := crossProduct (position x) (angularToroidal p x)

theorem poloidal_formula (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (x : Space) (i : Fin 3) :
    poloidal p x i=(‖x‖ : ℂ)^2*dcoord (complexEvaluate p) x i-(l : ℂ)*radial p x i := by
  have he := complexEvaluate_euler p l hp x
  have hs := OQ14.GreenKernel.coordinate_squares x
  simp only [Fin.sum_univ_three] at he
  fin_cases i <;> simp [poloidal,position,angularToroidal,cross_apply,radial]
  · linear_combination dcoord (complexEvaluate p) x 0*hs-(x 0 : ℂ)*he
  · linear_combination dcoord (complexEvaluate p) x 1*hs-(x 1 : ℂ)*he
  · linear_combination dcoord (complexEvaluate p) x 2*hs-(x 2 : ℂ)*he

theorem radial_smul (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (r : ℝ) (x : Space) :
    radial p (r • x)=(r : ℂ)^(l+1) • radial p x := by
  ext i
  simp only [radial,FischerDecomposition.complexEvaluate_smul p l hp,
    PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Pi.smul_apply,pow_succ]
  ring

theorem poloidal_smul (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) (r : ℝ) (x : Space) :
    poloidal p (r • x)=(r : ℂ)^(l+1) • poloidal p x := by
  rw [poloidal,HarmonicRadiationGeometry.angularToroidal_smul p l hp]
  ext i
  fin_cases i <;> simp [poloidal,position,cross_apply,PiLp.smul_apply,Complex.ofReal_mul,pow_succ] <;> ring

theorem radial_continuous (p : Poly) : Continuous (radial p) := by
  have h := (complexEvaluate_regular p).continuous
  apply continuous_pi
  intro i
  dsimp [radial]
  fun_prop

theorem poloidal_continuous (p : Poly) : Continuous (poloidal p) := by
  have hc (i : Fin 3) : Continuous (fun x => angularToroidal p x i) :=
    (continuous_apply i).comp (HarmonicRadiationGeometry.angularToroidal_continuous p)
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [poloidal,cross_apply,position] <;> fun_prop

theorem normalized_bound (F : Field) (l : ℕ) (hc : Continuous F)
    (hh : ∀ (r : ℝ) (x : Space),F (r • x)=(r : ℂ)^l • F x) :
    ∃ M : ℝ,0≤M ∧ ∀ x : Space,x≠0 → ‖((‖x‖ : ℂ)^l)⁻¹ • F x‖≤M := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Space) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro x hx
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hr0 : (‖x‖ : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hn : ‖‖x‖⁻¹ • x‖=1 := by simp [norm_smul,abs_of_pos hr,hr.ne']
  have hb : ‖x‖⁻¹ • x∈closedBall (0 : Space) 1 := by simp only [mem_closedBall_zero_iff,hn,le_refl]
  have he := hh ‖x‖ (‖x‖⁻¹ • x)
  rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul] at he
  rw [he,smul_smul,inv_mul_cancel₀ (pow_ne_zero l hr0),one_smul]
  exact (hM _ hb).trans (le_max_left _ _)

theorem radial_bound (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∃ M : ℝ,0≤M ∧ ∀ x : Space,x≠0 → ‖((‖x‖ : ℂ)^(l+1))⁻¹ • radial p x‖≤M :=
  normalized_bound _ _ (radial_continuous p) (radial_smul p l hp)

theorem poloidal_bound (p : Poly) (l : ℕ) (hp : p.IsHomogeneous l) :
    ∃ M : ℝ,0≤M ∧ ∀ x : Space,x≠0 → ‖((‖x‖ : ℂ)^(l+1))⁻¹ • poloidal p x‖≤M :=
  normalized_bound _ _ (poloidal_continuous p) (poloidal_smul p l hp)

end OQ14.HarmonicRadiationFactors

#print axioms OQ14.HarmonicRadiationFactors.poloidal_formula
#print axioms OQ14.HarmonicRadiationFactors.radial_smul
#print axioms OQ14.HarmonicRadiationFactors.poloidal_smul
#print axioms OQ14.HarmonicRadiationFactors.radial_continuous
#print axioms OQ14.HarmonicRadiationFactors.poloidal_continuous
#print axioms OQ14.HarmonicRadiationFactors.normalized_bound
#print axioms OQ14.HarmonicRadiationFactors.radial_bound
#print axioms OQ14.HarmonicRadiationFactors.poloidal_bound
