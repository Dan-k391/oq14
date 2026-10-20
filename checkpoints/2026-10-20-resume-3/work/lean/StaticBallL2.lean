import StaticBallHessian
import PlaneInverseCube

/-! # Genuine L2 gradient and Hessian of the uniform-ball potential -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.StaticBallL2

open MeasureTheory Metric Set Filter StaticBallHessian StaticBallPotential
open scoped Topology

abbrev Space := FourierL2.Space

def majorant (R : ℝ) (x : Space) : ℝ := ((max ‖x‖ R)^2)⁻¹

theorem fourth_power_integrable (R : ℝ) (hR : 0 < R) :
    Integrable (fun x : Space => ((max ‖x‖ R)^4)⁻¹) := by
  apply KernelIntegrability.radial_integrable (fun r => ((max r R)^4)⁻¹)
  have hl : IntegrableOn (fun r : ℝ => r^2 * ((max r R)^4)⁻¹) (Icc 0 R) := by
    have hcont : Continuous (fun r : ℝ => r^2 * (R^4)⁻¹) :=
      (continuous_id.pow 2).mul continuous_const
    exact hcont.integrableOn_Icc.congr_fun (fun r hr => by rw [max_eq_right hr.2]) measurableSet_Icc
  have hr : IntegrableOn (fun r : ℝ => r^2 * ((max r R)^4)⁻¹) (Ioi R) := by
    apply (PlaneInverseCube.inverse_square_integrable R hR).congr_fun _ measurableSet_Ioi
    intro r hr
    change R < r at hr
    change (r^2)⁻¹ = r^2 * ((max r R)^4)⁻¹
    rw [max_eq_left hr.le]
    have hn : r ≠ 0 := (hR.trans hr).ne'
    field_simp
    ring
  exact (hl.union hr).mono_set (by
    intro r hpos
    by_cases hh : r ≤ R
    · exact Or.inl ⟨hpos.le, hh⟩
    · exact Or.inr (lt_of_not_ge hh))

theorem majorant_memLp (R : ℝ) (hR : 0 < R) : MemLp (majorant R) 2 volume := by
  have hm : Measurable (majorant R) :=
    ((continuous_norm.max continuous_const).measurable.pow_const 2).inv
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have he : (fun x : Space => majorant R x ^ 2) =
      fun x => ((max ‖x‖ R)^4)⁻¹ := by
    ext x
    unfold majorant
    simp only [← inv_pow, ← pow_mul]
  rw [he]
  exact fourth_power_integrable R hR

theorem force_radius_bound (R r : ℝ) (hR : 0 < R) :
    |force R r| * r ≤ (R^3/3)*((max r R)^2)⁻¹ := by
  by_cases hh : r ≤ R
  · have he : (R^3/3)*(R^2)⁻¹ = R/3 := by field_simp; ring
    rw [force, if_pos hh, max_eq_right hh, he]
    rw [abs_of_neg (by norm_num : (-1/3 : ℝ) < 0)]
    linarith
  · have hrp : 0 < r := hR.trans (lt_of_not_ge hh)
    have hnn : 0 ≤ R^3/(3*r^3) := div_nonneg (pow_nonneg hR.le _) (by positivity)
    rw [force, if_neg hh, max_eq_left (lt_of_not_ge hh).le]
    have hneg : -R^3/(3*r^3) = -(R^3/(3*r^3)) := by ring
    rw [hneg, abs_neg, abs_of_nonneg hnn]
    apply le_of_eq
    field_simp
    ring

theorem gradient_bound (R : ℝ) (hR : 0 < R) (j : Fin 3) (x : Space) :
    ‖StaticBallHessian.gradient R j x‖ ≤ (R^3/3)*majorant R x := by
  rw [StaticBallHessian.gradient, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x j)
    (abs_nonneg _)).trans (force_radius_bound R ‖x‖ hR)

theorem gradient_memLp (R : ℝ) (hR : 0 < R) (j : Fin 3) :
    MemLp (StaticBallHessian.gradient R j) 2 volume := by
  apply (majorant_memLp R hR).of_le_mul (gradient_continuous R hR j).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, majorant, abs_inv, abs_pow, abs_of_nonneg
    (le_trans (norm_nonneg x) (le_max_left _ _))] using gradient_bound R hR j x

def gradientL2 (R : ℝ) (hR : 0 < R) (j : Fin 3) : FourierL2.ScalarL2 :=
  (gradient_memLp R hR j).toLp (StaticBallHessian.gradient R j)

theorem gradientL2_ae (R : ℝ) (hR : 0 < R) (j : Fin 3) :
    gradientL2 R hR j =ᵐ[volume] StaticBallHessian.gradient R j :=
  (gradient_memLp R hR j).coeFn_toLp

theorem exterior_norm_bound (R : ℝ) (hR : 0 < R) (i j : Fin 3) (x : Space)
    (hx : x ≠ 0) :
    ‖StaticBallHessian.exterior R ‖x‖ i j x‖ ≤ (4/3 : ℝ)*(R^3/‖x‖^3) := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hxn : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have he : StaticBallHessian.exterior R ‖x‖ i j x = ((R^3/‖x‖^3 : ℝ) : ℂ) *
      ((x i : ℂ)*(x j : ℂ)/(‖x‖ : ℂ)^2 - (if i=j then 1 else 0 : ℂ)/3) := by
    unfold StaticBallHessian.exterior
    push_cast
    field_simp
    split_ifs <;> ring
  have hc : 0 ≤ R^3/‖x‖^3 := div_nonneg (pow_nonneg hR.le _) (by positivity)
  have hd : ‖(if i=j then 1 else 0 : ℂ)/3‖ ≤ 1/3 := by
    split_ifs <;> norm_num
  have hn := DyadicKernel.normalized_coordinate_product_bound x hx i j
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans
    ((add_le_add hn hd).trans_eq (by norm_num))) hc).trans_eq (mul_comm _ _)

theorem hessian_bound (R : ℝ) (hR : 0 < R) (i j : Fin 3) (x : Space) :
    ‖hessian R i j x‖ ≤ (4*R^2/3)*majorant R x := by
  by_cases hx : ‖x‖ ≤ R
  · have he : (4*R^2/3)*(R^2)⁻¹ = 4/3 := by field_simp; ring
    rw [hessian, if_pos hx, majorant, max_eq_right hx, he]
    split_ifs <;> norm_num
  · have hr : R < ‖x‖ := lt_of_not_ge hx
    have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (hR.trans hr).ne'
    have hb : R^3/‖x‖^3 ≤ R^2/‖x‖^2 := by
      apply (div_le_div_iff₀ (by positivity : 0 < ‖x‖^3) (by positivity : 0 < ‖x‖^2)).mpr
      have hh := mul_le_mul_of_nonneg_left hr.le (mul_nonneg (sq_nonneg R) (sq_nonneg ‖x‖))
      nlinarith
    rw [hessian, if_neg hx, majorant, max_eq_left hr.le]
    exact (exterior_norm_bound R hR i j x hx0).trans
      ((mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 4/3)).trans_eq (by ring))

theorem hessian_measurable (R : ℝ) (i j : Fin 3) : Measurable (hessian R i j) := by
  unfold hessian
  apply Measurable.ite (isClosed_le continuous_norm continuous_const).measurableSet measurable_const
  unfold StaticBallHessian.exterior
  have hn : Measurable (fun x : Space => (‖x‖ : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp continuous_norm.measurable
  exact measurable_const.mul ((((ModalDipole.coordinate i).continuous.measurable.mul
    (ModalDipole.coordinate j).continuous.measurable).div (hn.pow_const 5)).sub
      (measurable_const.div (measurable_const.mul (hn.pow_const 3))))

theorem hessian_memLp (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    MemLp (hessian R i j) 2 volume := by
  apply (majorant_memLp R hR).of_le_mul (hessian_measurable R i j).aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs, majorant, abs_inv, abs_pow, abs_of_nonneg
    (le_trans (norm_nonneg x) (le_max_left _ _))] using hessian_bound R hR i j x

def hessianL2 (R : ℝ) (hR : 0 < R) (i j : Fin 3) : FourierL2.ScalarL2 :=
  (hessian_memLp R hR i j).toLp (hessian R i j)

theorem hessianL2_ae (R : ℝ) (hR : 0 < R) (i j : Fin 3) :
    hessianL2 R hR i j =ᵐ[volume] hessian R i j := (hessian_memLp R hR i j).coeFn_toLp

end OQ14.StaticBallL2

#print axioms OQ14.StaticBallL2.fourth_power_integrable
#print axioms OQ14.StaticBallL2.majorant_memLp
#print axioms OQ14.StaticBallL2.force_radius_bound
#print axioms OQ14.StaticBallL2.gradient_bound
#print axioms OQ14.StaticBallL2.gradient_memLp
#print axioms OQ14.StaticBallL2.gradientL2_ae
#print axioms OQ14.StaticBallL2.exterior_norm_bound
#print axioms OQ14.StaticBallL2.hessian_bound
#print axioms OQ14.StaticBallL2.hessian_measurable
#print axioms OQ14.StaticBallL2.hessian_memLp
#print axioms OQ14.StaticBallL2.hessianL2_ae
