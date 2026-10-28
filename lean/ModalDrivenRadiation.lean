import ModalDrivenScattering
import ModalOutgoing
import RadiatingTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalDrivenRadiation
open Complex Filter MeasureTheory Metric Set OQ14.Maxwell OQ14.ModalOutgoing
  OQ14.ModalDriven OQ14.ModalDrivenScattering OQ14.AngularPower OQ14.MaxwellRadiation
open scoped Topology

theorem far_transverse (k b : ℂ) (n : Sphere) :
    dot (direction n) (electricFar k b n) = 0 := by
  have h0 : (n : Space) ≠ 0 := by
    intro h; have := sphere_norm n; simp [h] at this
  have hd := direction_dot (n : Space) h0
  have hdir (j : Fin 3) : direction (n : Space) j = ((n : Space) j : ℂ) := by
    simp [direction, GreenKernel.unitCoordinate, sphere_norm]
  simp only [dot, Fin.sum_univ_three] at hd ⊢
  simp only [hdir, electricFar, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_def] at hd ⊢
  norm_num at hd ⊢
  linear_combination (b*I*k*((n : Space) 2 : ℂ))*hd

theorem far_relation (k b : ℂ) (n : Sphere) :
    magneticFar k b n = crossProduct (direction n) (electricFar k b n) := by
  have h0 : (n : Space) ≠ 0 := by intro h; have := sphere_norm n; simp [h] at this
  have hdir : direction (n : Space) = fun j => ((n : Space) j : ℂ) := by
    ext j; simp [direction, GreenKernel.unitCoordinate, sphere_norm]
  rw [hdir]
  exact (far_tangential_relation k b (n : Space)).symm

theorem polynomial_continuous (k b : ℂ) (i : Fin 3) :
    Continuous (fun w : Sphere × ℂ => electricPolynomial k b w.2 w.1 i) ∧
    Continuous (fun w : Sphere × ℂ => magneticPolynomial k b w.2 w.1 i) := by
  have hn (j : Fin 3) : Continuous (fun w : Sphere × ℂ => ((w.1 : Space) j : ℂ)) :=
    ((coordinate j).continuous.comp continuous_subtype_val).comp continuous_fst
  constructor <;> fin_cases i <;> dsimp [electricPolynomial, magneticPolynomial]
  all_goals fun_prop

theorem polynomial_uniform_bound (k b : ℂ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ u : ℂ, ‖u‖ ≤ 1 → ∀ n : Sphere, ∀ i : Fin 3,
      ‖electricPolynomial k b u n i‖ ≤ C ∧ ‖magneticPolynomial k b u n i‖ ≤ C := by
  have hcompact : IsCompact ((univ : Set Sphere) ×ˢ closedBall (0 : ℂ) 1) :=
    isCompact_univ.prod (isCompact_closedBall (0 : ℂ) 1)
  have hbound (i : Fin 3) := hcompact.exists_bound_of_continuousOn (polynomial_continuous k b i).1.continuousOn
  have hbound' (i : Fin 3) := hcompact.exists_bound_of_continuousOn (polynomial_continuous k b i).2.continuousOn
  choose C hC using hbound
  choose D hD using hbound'
  let T : ℝ := ∑ i : Fin 3, (|C i| + |D i|)
  refine ⟨T, ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ => add_nonneg (abs_nonneg _) (abs_nonneg _))
  · intro u hu n i
    have hm : (n,u) ∈ ((univ : Set Sphere) ×ˢ closedBall (0 : ℂ) 1) := by
      simp [mem_closedBall, dist_zero_right, hu]
    have hsum : |C i| + |D i| ≤ T := by
      exact Finset.single_le_sum (f := fun j : Fin 3 => |C j| + |D j|)
        (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
    have hCi : C i ≤ T := (le_abs_self _).trans ((le_add_of_nonneg_right (abs_nonneg (D i))).trans hsum)
    have hDi : D i ≤ T := (le_abs_self _).trans ((le_add_of_nonneg_left (abs_nonneg (C i))).trans hsum)
    exact ⟨(hC i (n,u) hm).trans hCi, (hD i (n,u) hm).trans hDi⟩

theorem electric_poly_ray (k b : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) (n : Sphere) :
    scaledElectric k b r n = electricPolynomial k b ((r : ℂ)⁻¹) n := by
  rw [electric_ray_formula k b hk r hr n (sphere_norm n)]
  ext j
  fin_cases j <;> dsimp [electricPolynomial] <;>
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] <;> ring

theorem magnetic_poly_ray (k b : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : 0 < r) (n : Sphere) :
    scaledMagnetic k b r n = magneticPolynomial k b ((r : ℂ)⁻¹) n := by
  rw [magnetic_ray_formula k b hk r hr n (sphere_norm n)]
  ext j
  fin_cases j <;> dsimp [magneticPolynomial] <;> simp only [div_eq_mul_inv] <;> ring

theorem ray_exterior (n : Sphere) (r : ℝ) (hr : 1 < r) : 1 < ‖r • (n : Space)‖ := by
  simpa [norm_smul, abs_of_pos (by linarith : 0 < r), sphere_norm] using hr

theorem scaled_scattered (n k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : 1 < r) (v : Sphere) :
    (exp (-I*k*r)*(r : ℂ)) • scatteredE n k (r • (v : Space)) =
      electricPolynomial k (numerator n k).2 ((r : ℂ)⁻¹) v ∧
    (exp (-I*k*r)*(r : ℂ)) • scatteredH n k (r • (v : Space)) =
      magneticPolynomial k (numerator n k).2 ((r : ℂ)⁻¹) v := by
  rw [(OQ14.ModalDrivenScattering.scattered_exterior n k _ (ray_exterior v r hr)).1,
    (OQ14.ModalDrivenScattering.scattered_exterior n k _ (ray_exterior v r hr)).2]
  exact ⟨electric_poly_ray k _ hk r (by linarith) v,
    magnetic_poly_ray k _ hk r (by linarith) v⟩

def trace (n : ℂ) (k : ℝ) (hk : k ≠ 0) : RadiatingTrace.Trace k
    (scatteredE n k) (scatteredH n k) where
  far v := electricFar k (numerator n k).2 v
  transverse v := far_transverse k _ v
  sphericalContinuous := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hfac : (MaxwellFarField.factor k r) ≠ 0 := by
      unfold MaxwellFarField.factor
      exact mul_ne_zero (ofReal_ne_zero.mpr (ne_of_gt (by linarith : 0 < r))) (exp_ne_zero _)
    have hpE : Continuous (fun v : Sphere => electricPolynomial k (numerator n k).2 ((r : ℂ)⁻¹) v) := by
      apply continuous_pi; intro i
      have hmap : Continuous (fun v : Sphere => (v, ((r : ℂ)⁻¹))) := continuous_id.prodMk continuous_const
      simpa only [Function.comp_def] using ((polynomial_continuous (k : ℂ) (numerator n k).2 i).1.comp hmap)
    have hpH : Continuous (fun v : Sphere => magneticPolynomial k (numerator n k).2 ((r : ℂ)⁻¹) v) := by
      apply continuous_pi; intro i
      have hmap : Continuous (fun v : Sphere => (v, ((r : ℂ)⁻¹))) := continuous_id.prodMk continuous_const
      simpa only [Function.comp_def] using ((polynomial_continuous (k : ℂ) (numerator n k).2 i).2.comp hmap)
    have he : (fun v : Sphere => scatteredE n k (r • (v : Space))) =
        fun v : Sphere => (MaxwellFarField.factor k r)⁻¹ • electricPolynomial k (numerator n k).2 ((r : ℂ)⁻¹) v := by
      funext v
      have h := (scaled_scattered n k (ofReal_ne_zero.mpr hk) r hr v).1
      have hf : exp (-I*(k : ℂ)*r)*(r : ℂ) = MaxwellFarField.factor k r := by
        simp [MaxwellFarField.factor, mul_comm, mul_assoc]
      rw [hf] at h
      calc
        _ = (MaxwellFarField.factor k r)⁻¹ • ((MaxwellFarField.factor k r) • scatteredE n k (r • (v : Space))) := by simp [hfac]
        _ = _ := by rw [h]
    have hh : (fun v : Sphere => scatteredH n k (r • (v : Space))) =
        fun v : Sphere => (MaxwellFarField.factor k r)⁻¹ • magneticPolynomial k (numerator n k).2 ((r : ℂ)⁻¹) v := by
      funext v
      have h := (scaled_scattered n k (ofReal_ne_zero.mpr hk) r hr v).2
      have hf : exp (-I*(k : ℂ)*r)*(r : ℂ) = MaxwellFarField.factor k r := by
        simp [MaxwellFarField.factor, mul_comm, mul_assoc]
      rw [hf] at h
      calc
        _ = (MaxwellFarField.factor k r)⁻¹ • ((MaxwellFarField.factor k r) • scatteredH n k (r • (v : Space))) := by simp [hfac]
        _ = _ := by rw [h]
    rw [he, hh]
    exact ⟨continuous_const.smul hpE, continuous_const.smul hpH⟩
  bounded := by
    obtain ⟨C,hC,hbound⟩ := polynomial_uniform_bound (k : ℂ) (numerator n k).2
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr v i
    have hri : ‖(r : ℂ)⁻¹‖ ≤ 1 := by
      rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < r)]
      exact inv_le_one_of_one_le₀ (le_of_lt hr)
    have h := scaled_scattered n k (ofReal_ne_zero.mpr hk) r hr v
    have hf : exp (-I*(k : ℂ)*r)*(r : ℂ) = MaxwellFarField.factor k r := by
      simp [MaxwellFarField.factor, mul_comm, mul_assoc]
    rw [hf] at h
    have he := congrFun h.1 i
    have hh := congrFun h.2 i
    simp only [Pi.smul_apply, smul_eq_mul] at he hh
    rw [he, hh]
    exact hbound ((r : ℂ)⁻¹) hri v i
  electricLimit v := by
    have h := electric_far_limit (k : ℂ) (numerator n k).2 (ofReal_ne_zero.mpr hk) v (sphere_norm v)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have he := (OQ14.ModalDrivenScattering.scattered_exterior n k _ (ray_exterior v r hr)).1
    simp [scaledElectric, MaxwellFarField.factor, ModalInterface.outerE, he, mul_comm, mul_assoc]
  magneticLimit v := by
    rw [← far_relation (k : ℂ) (numerator n k).2 v]
    have h := magnetic_far_limit (k : ℂ) (numerator n k).2 (ofReal_ne_zero.mpr hk) v (sphere_norm v)
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hh := (OQ14.ModalDrivenScattering.scattered_exterior n k _ (ray_exterior v r hr)).2
    simp [scaledMagnetic, MaxwellFarField.factor, ModalInterface.outerH, hh, mul_comm, mul_assoc]

#print axioms OQ14.ModalDrivenRadiation.trace
#print axioms OQ14.ModalDrivenRadiation.scaled_scattered
#print axioms OQ14.ModalDrivenRadiation.polynomial_uniform_bound
#print axioms OQ14.ModalDrivenRadiation.far_transverse
#print axioms OQ14.ModalDrivenRadiation.far_relation
end OQ14.ModalDrivenRadiation











