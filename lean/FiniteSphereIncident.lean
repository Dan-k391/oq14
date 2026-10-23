import FiniteSphereMaxwell
import IncidentLocalization

/-! Bounds derived from the literal sphere integrals for actual finite illuminations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereIncident
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus
open SphereMagneticParity (reflection)
open FiniteHerglotzFlux (electric)
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem moment_derivative_bound (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ)
    (hA : ∀ θ, ‖a θ‖ ≤ A) (k : ℝ) (x : Space) :
    ‖fderiv ℝ (moment a k) x‖ ≤ (A*|k|)*surfaceMass := by
  rw [(moment_hasFDerivAt a ha A hA k x).fderiv]
  apply norm_integral_le_of_norm_le_const
  filter_upwards with θ
  apply ((phase k θ).opNorm_smul_le (a θ*wave k x θ)).trans
  rw [norm_mul, wave_norm, mul_one]
  exact mul_le_mul (hA θ) (phase_bound k θ) (norm_nonneg _) ((norm_nonneg _).trans (hA θ))

private theorem amplitude_cont (i j : Fin 3) : Continuous (fun θ : Sphere => amplitude θ i j) :=
  continuous_const.sub ((coordinate_continuous i).mul (coordinate_continuous j))

theorem J_derivative_bound (k : ℝ) (x : Space) (i j : Fin 3) :
    ‖fderiv ℝ (fun y => J k y i j) x‖ ≤ entryBound k*|k| := by
  have hd := moment_hasFDerivAt _ (amplitude_cont i j) 2 (fun θ => amplitude_bound θ i j) k x
  have hh := (hd.const_mul ((k^3/(16*Real.pi^2) : ℝ) : ℂ)).fderiv
  change fderiv ℝ (fun y => J k y i j) x = _ at hh
  rw [hh]
  calc
    _ ≤ ‖((k^3/(16*Real.pi^2) : ℝ) : ℂ)‖*‖fderiv ℝ (moment (fun θ => amplitude θ i j) k) x‖ := by
      rw [hd.fderiv]
      exact ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖((k^3/(16*Real.pi^2) : ℝ) : ℂ)‖*((2*|k|)*surfaceMass) :=
      mul_le_mul_of_nonneg_left (moment_derivative_bound _ (amplitude_cont i j) 2
        (fun θ => amplitude_bound θ i j) k x) (norm_nonneg _)
    _ = _ := by rw [Complex.norm_real, Real.norm_eq_abs]; unfold entryBound; ring

theorem reflection_bound : ‖reflection‖ ≤ 3 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖x-(2 : ℝ) • ((x 2) • Maxwell.basis 2)‖ ≤ 3*‖x‖
  have hb : ‖Maxwell.basis 2‖ = 1 := by simp [Maxwell.basis]
  have hx := PiLp.norm_apply_le x 2
  calc
    _ ≤ ‖x‖+‖(2 : ℝ) • ((x 2) • Maxwell.basis 2)‖ := norm_sub_le _ _
    _ ≤ ‖x‖+2*‖x‖ := by
      simp only [norm_smul, hb, mul_one]
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add_left (mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 2)) ‖x‖
    _ = _ := by ring

private theorem affine_J_bound (k : ℝ) (x y : Space) (L : Space →L[ℝ] Space)
    (i j : Fin 3) :
    ‖fderiv ℝ (fun z => J k (L z-y) i j) x‖ ≤ (entryBound k*|k|)*‖L‖ := by
  have hd := ((moment_hasFDerivAt _ (amplitude_cont i j) 2 (fun θ => amplitude_bound θ i j) k (L x-y)).const_mul
    ((k^3/(16*Real.pi^2) : ℝ) : ℂ)).differentiableAt
  change DifferentiableAt ℝ (fun z => J k z i j) (L x-y) at hd
  have hh := hd.hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
  simp only [Function.comp_def] at hh
  rw [hh.fderiv]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (J_derivative_bound k (L x-y) i j) (norm_nonneg _))

theorem reaction_derivative_bound (e : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    ‖fderiv ℝ (fun z => reaction e k z y i j) x‖ ≤ 2*entryBound k*|k| := by
  have hdiff (L : Space →L[ℝ] Space) : DifferentiableAt ℝ (fun z => J k (L z-y) i j) x := by
    have hd := ((moment_hasFDerivAt _ (amplitude_cont i j) 2 (fun θ => amplitude_bound θ i j) k (L x-y)).const_mul
      ((k^3/(16*Real.pi^2) : ℝ) : ℂ)).differentiableAt
    change DifferentiableAt ℝ (fun z => J k z i j) (L x-y) at hd
    have hh := hd.hasFDerivAt.comp x (L.hasFDerivAt.sub_const y)
    simpa only [Function.comp_def] using hh.differentiableAt
  have hi := hdiff (ContinuousLinearMap.id ℝ Space)
  have hr := hdiff reflection
  simp only [ContinuousLinearMap.id_apply] at hi
  simp only [SphereMagneticParity.reflection_apply] at hr
  have hs : ‖(if e then -1 else 1 : ℂ)*(sign i : ℂ)‖=1 := by
    cases e <;> unfold sign <;> split_ifs <;> norm_num
  unfold reaction
  rw [fderiv_const_mul (hi.add (hr.const_mul _))]
  apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
  rw [fderiv_add hi (hr.const_mul _), fderiv_const_mul hr]
  have hnorm : ‖Complex.I/2‖=(1/2 : ℝ) := by norm_num [norm_div]
  rw [hnorm]
  have ht := norm_add_le (fderiv ℝ (fun z => J k (z-y) i j) x)
    (((if e then -1 else 1 : ℂ)*(sign i : ℂ)) • fderiv ℝ (fun z => J k (reflect z-y) i j) x)
  have hni := affine_J_bound k x y (ContinuousLinearMap.id ℝ Space) i j
  simp only [ContinuousLinearMap.id_apply] at hni
  have hnr := affine_J_bound k x y reflection i j
  simp only [SphereMagneticParity.reflection_apply] at hnr
  have hi1 : ‖ContinuousLinearMap.id ℝ Space‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hn : 0 ≤ entryBound k*|k| := mul_nonneg (entryBound_nonnegative k) (abs_nonneg k)
  have hni' := hni.trans (mul_le_mul_of_nonneg_left hi1 hn)
  have hnr' := hnr.trans (mul_le_mul_of_nonneg_left reflection_bound hn)
  have ht' := (fderiv ℝ (fun z => J k (reflect z-y) i j) x).opNorm_smul_le
    ((if e then -1 else 1 : ℂ)*(sign i : ℂ))
  rw [hs] at ht'
  nlinarith

theorem electric_bound (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) (i : Fin 3) :
    ‖electric k e p j A x i‖ ≤ entryBound k*(∑ s, ‖A s‖) := by
  classical
  calc
    _ ≤ ∑ s, ‖A s*reaction (e s) k x (p s) i (j s)‖ := norm_sum_le _ _
    _ ≤ ∑ s, ‖A s‖*entryBound k := Finset.sum_le_sum (fun s _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (reaction_bound (e s) k x (p s) i (j s)) (norm_nonneg _))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem electric_derivative_bound (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) (i : Fin 3) :
    ‖fderiv ℝ (fun y => electric k e p j A y i) x‖ ≤
      (2*entryBound k*|k|)*(∑ s, ‖A s‖) := by
  classical
  unfold electric
  rw [fderiv_sum (fun s _ => (SphereParityMaxwell.electric_differentiable (e s) k x (p s) i (j s)).const_mul (A s))]
  calc
    _ ≤ ∑ s, ‖fderiv ℝ (fun y => A s*reaction (e s) k y (p s) i (j s)) x‖ := norm_sum_le _ _
    _ ≤ ∑ s, ‖A s‖*(2*entryBound k*|k|) := Finset.sum_le_sum (fun s _ => by
      rw [fderiv_const_mul (SphereParityMaxwell.electric_differentiable (e s) k x (p s) i (j s))]
      exact ((fderiv ℝ (fun y => reaction (e s) k y (p s) i (j s)) x).opNorm_smul_le (A s)).trans
        (mul_le_mul_of_nonneg_left (reaction_derivative_bound (e s) k x (p s) i (j s)) (norm_nonneg _)))
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem electric_scaled_bounds (k a A₀ : ℝ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (hA : (∑ s, ‖A s‖) ≤ A₀/a) (x : Space) (i : Fin 3) :
    ‖electric k e p j A x i‖ ≤ (entryBound k*A₀)/a ∧
    ‖fderiv ℝ (fun y => electric k e p j A y i) x‖ ≤ (2*entryBound k*|k| * A₀)/a := by
  constructor
  · calc
      _ ≤ entryBound k*(∑ s, ‖A s‖) := electric_bound k e p j A x i
      _ ≤ entryBound k*(A₀/a) := mul_le_mul_of_nonneg_left hA (entryBound_nonnegative k)
      _ = _ := by ring
  · calc
      _ ≤ (2*entryBound k*|k|)*(∑ s, ‖A s‖) := electric_derivative_bound k e p j A x i
      _ ≤ (2*entryBound k*|k|)*(A₀/a) := mul_le_mul_of_nonneg_left hA (mul_nonneg (mul_nonneg (by norm_num) (entryBound_nonnegative k)) (abs_nonneg k))
      _ = _ := by ring

theorem electric_memLp (k R : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (i : Fin 3) :
    MemLp (fun x => electric k e p j A x i) 2 (volume.restrict (closedBall 0 R)) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Space) R).measure_lt_top⟩
  have hc : Continuous (fun x => electric k e p j A x i) :=
    continuous_iff_continuousAt.mpr (fun x => (FiniteSphereMaxwell.electric_differentiable k e p j A x i).continuousAt)
  exact MemLp.of_bound hc.aestronglyMeasurable (entryBound k*(∑ s, ‖A s‖))
    (Filter.Eventually.of_forall (fun x => electric_bound k e p j A x i))

def datum (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0) :
    VectorFourier.VectorL2 :=
  IncidentLocalization.datum c R (electric k e p j A) hc (electric_memLp k R e p j A)

theorem datum_actual (c : StaticCoefficient.Coefficient) (k R : ℝ)
    (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3) (A : ι → ℂ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (i : Fin 3) :
    (fun x => datum c k R e p j A hc (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*electric k e p j A x i :=
  IncidentLocalization.datum_actual c R _ hc (electric_memLp k R e p j A) i

end OQ14.FiniteSphereIncident
#print axioms OQ14.FiniteSphereIncident.moment_derivative_bound
#print axioms OQ14.FiniteSphereIncident.J_derivative_bound
#print axioms OQ14.FiniteSphereIncident.reflection_bound
#print axioms OQ14.FiniteSphereIncident.reaction_derivative_bound
#print axioms OQ14.FiniteSphereIncident.electric_bound
#print axioms OQ14.FiniteSphereIncident.electric_derivative_bound
#print axioms OQ14.FiniteSphereIncident.electric_scaled_bounds
#print axioms OQ14.FiniteSphereIncident.electric_memLp
#print axioms OQ14.FiniteSphereIncident.datum_actual
