import ScalarGreenRadialBound
import SphereHarmonicAddition
import SphereHarmonicDimension
import SphereHarmonicHilbert
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Genuine uniform angular convergence bounds for the free physical Green modes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace OQ14.ScalarGreenAngularBound
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.SphereHarmonicAddition
  OQ14.SphereHarmonicHilbert OQ14.ScalarGreenRadialBound

theorem polynomial_geometric_summable (k : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ : ρ < 1) :
    Summable (fun l : ℕ => (l+1 : ℝ)^k*ρ^l) := by
  have h := (summable_pow_mul_geometric_of_norm_lt_one k
    (show ‖ρ‖ < 1 by simpa only [Real.norm_eq_abs,abs_of_pos hρ0] using hρ)).comp_injective Nat.succ_injective
  have hh := h.mul_right ρ⁻¹
  have he : (fun l : ℕ => (l+1 : ℝ)^k*ρ^l)=
      (fun l : ℕ => (l+1 : ℝ)^k*ρ^(l+1)*ρ⁻¹) := by
    funext l
    rw [pow_succ]
    field_simp [hρ0.ne']
    ring
  rw [he]
  simpa only [Function.comp_def,Nat.succ_eq_add_one,Nat.cast_add,Nat.cast_one] using hh

def indexMajorant (C ρ : ℝ) (k : ℕ) (a : TotalIndex) : ℝ := C*(a.1+1 : ℝ)^k*ρ^a.1

theorem indexMajorant_summable (C ρ : ℝ) (k : ℕ) (hC : 0 ≤ C) (hρ0 : 0 < ρ) (hρ : ρ < 1) :
    Summable (indexMajorant C ρ k) := by
  apply (summable_sigma_of_nonneg (fun _ => by dsimp [indexMajorant];positivity)).mpr
  refine ⟨fun _ => (hasSum_fintype _).summable,?_⟩
  simp only [tsum_fintype,indexMajorant,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  apply Summable.of_nonneg_of_le (fun _ => by positivity)
    (f := fun l : ℕ => C*((l+1 : ℝ)^(k+3)*ρ^l))
  · intro l
    have hcard : (Fintype.card (Index l) : ℝ) ≤ (l+1 : ℝ)^3 := by
      simp only [Index,Fintype.card_fin]
      exact_mod_cast SphereHarmonicDimension.harmonicSpace_finrank_le l
    have hh := mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ C*(l+1 : ℝ)^k*ρ^l)
    convert hh using 1; rw [pow_add]; ring
  · exact (polynomial_geometric_summable (k+3) ρ hρ0 hρ).mul_left C

theorem angular_product_bound (l : ℕ) (i : Index l) (n m : Sphere) :
    ‖(angular l i n : ℂ)*(angular l i m : ℂ)‖ ≤ (l+1 : ℝ)^3/angularMeasure.real Set.univ := by
  have hD : 0 ≤ (Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ :=
    div_nonneg (Nat.cast_nonneg _) area_pos.le
  calc
    _ = ‖angular l i n‖*‖angular l i m‖ := by simp only [norm_mul,Complex.norm_real]
    _ ≤ Real.sqrt ((Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ)*
        Real.sqrt ((Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ) :=
      mul_le_mul (angular_norm_bound l i n) (angular_norm_bound l i m) (norm_nonneg _) (Real.sqrt_nonneg _)
    _ = (Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ := by rw [← sq,Real.sq_sqrt hD]
    _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast SphereHarmonicDimension.harmonicSpace_finrank_le l) area_pos.le

def modeMap (a : TotalIndex) (k r s : ℝ) : C(Sphere × Sphere,ℂ) where
  toFun p := radialFactor a.1 k r s*((angular a.1 a.2 p.1 : ℂ)*(angular a.1 a.2 p.2 : ℂ))
  continuous_toFun := continuous_const.mul
    ((Complex.continuous_ofReal.comp ((angular a.1 a.2).continuous.comp continuous_fst)).mul
      (Complex.continuous_ofReal.comp ((angular a.1 a.2).continuous.comp continuous_snd)))

theorem modeMap_bound (a : TotalIndex) (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) :
    ‖modeMap a k r s‖ ≤
      indexMajorant (Real.exp ((k*r)^2/2+k*s)/(s*angularMeasure.real Set.univ)) (r/s) 3 a := by
  have hC : 0 ≤ Real.exp ((k*r)^2/2+k*s)/(s*angularMeasure.real Set.univ) := by positivity
  have hρ : 0 ≤ r/s := div_nonneg hr.le hs.le
  rw [(modeMap a k r s).norm_le (by dsimp [indexMajorant];positivity)]
  intro p
  change ‖radialFactor a.1 k r s*((angular a.1 a.2 p.1 : ℂ)*(angular a.1 a.2 p.2 : ℂ))‖ ≤ _
  rw [norm_mul]
  have hrad := radialFactor_bound a.1 k r s hk hr hs
  have hden : s ≤ s*(2*(a.1 : ℝ)+1) := by nlinarith [Nat.cast_nonneg (α := ℝ) a.1]
  have hrad' : ‖radialFactor a.1 k r s‖ ≤ Real.exp ((k*r)^2/2+k*s)/s*(r/s)^a.1 :=
    hrad.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left (Real.exp_pos _).le hs hden) (pow_nonneg hρ _))
  have hh := mul_le_mul hrad' (angular_product_bound a.1 a.2 p.1 p.2) (norm_nonneg _)
    (mul_nonneg (div_nonneg (Real.exp_pos _).le hs.le) (pow_nonneg hρ _))
  convert hh using 1
  dsimp [indexMajorant]
  field_simp
  ring

theorem actual_modes_summable (k r s : ℝ) (hk : 0 < k) (hr : 0 < r) (hrs : r < s) :
    Summable (fun a : TotalIndex => modeMap a k r s) := by
  have hs := hr.trans hrs
  apply Summable.of_norm_bounded (f := fun a => modeMap a k r s)
    (indexMajorant (Real.exp ((k*r)^2/2+k*s)/(s*angularMeasure.real Set.univ)) (r/s) 3)
    (indexMajorant_summable _ _ 3 (by positivity) (div_pos hr hs) ((div_lt_one hs).mpr hrs))
  intro a
  exact modeMap_bound a k r s hk hr hs

end OQ14.ScalarGreenAngularBound

#print axioms OQ14.ScalarGreenAngularBound.polynomial_geometric_summable

#print axioms OQ14.ScalarGreenAngularBound.indexMajorant_summable

#print axioms OQ14.ScalarGreenAngularBound.angular_product_bound

#print axioms OQ14.ScalarGreenAngularBound.modeMap_bound

#print axioms OQ14.ScalarGreenAngularBound.actual_modes_summable
