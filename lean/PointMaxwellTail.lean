import SphereMagneticKernel
import MaxwellPlaneTail

/-! Actual point Maxwell columns and their mixed-frequency plane tails. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PointMaxwellTail
open MeasureTheory Metric Set MaxwellPlaneTail MaxwellRadiation ScalarRadiation GreenKernel
open SphereMagneticKernel (magneticDyadic)
open Maxwell (Vector conjugate dot)
open WeakCurl (next previous)
open scoped ComplexConjugate Topology
abbrev Space := FourierL2.Space

def polarization (j : Fin 3) : Vector := fun a => if a=j then 1 else 0

def leadingE (k : ℝ) (x y : Space) (j : Fin 3) : Vector := fun i =>
  (k : ℂ)^2*phi k (x-y)*DyadicRadiation.transverse x i j

def leadingH (k : ℝ) (x y : Space) (j : Fin 3) : Vector := fun i =>
  ((k : ℂ)^2*phi k (x-y))*crossProduct (direction x) (polarization j) i

private theorem leadingH_component (k : ℝ) (x y : Space) (i j : Fin 3) :
    leadingH k x y j i = (k : ℂ)^2*phi k (x-y)*
      (unitCoordinate (next i) x*(if previous i=j then 1 else 0)-
        unitCoordinate (previous i) x*(if next i=j then 1 else 0)) := by
  rw [leadingH, cross_component]
  rfl

theorem leading_identity (k : ℝ) (x y : Space) (hx : x ≠ 0) (i j : Fin 3) :
    crossProduct (leadingH k x y j) (direction x) i = leadingE k x y j i := by
  change crossProduct (fun a => ((k : ℂ)^2*phi k (x-y))*
    crossProduct (direction x) (polarization j) a) (direction x) i = _
  rw [cross_const_left, cross_cross_same, direction_dot x hx, one_mul]
  fin_cases j <;> fin_cases i <;>
    simp [dot, polarization, leadingE, DyadicRadiation.transverse, direction, Fin.ext_iff]
  all_goals ring_nf
  all_goals simp

theorem electric_error (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖DyadicKernel.dyadic k (x-y) i j-leadingE k x y j i‖ ≤ electricErrorConstant k R/‖x‖^2 := by
  convert DyadicRadiation.dyadic_source_error k R hR x y hx hx₂ hy i j using 1
  unfold electricErrorConstant
  ring

private theorem leading_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) (a : ℂ) (ha : ‖a‖ ≤ 2) :
    ‖(k : ℂ)^2*phi k (x-y)*a‖ ≤ leadingConstant k/‖x‖ := by
  have hp : 0 < ‖x‖ := by linarith [norm_nonneg x]
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (k^2*((4*Real.pi)⁻¹*(2/‖x‖)))*2 := mul_le_mul
      (mul_le_mul_of_nonneg_left (phi_source_bound k R hR x y hx hy) (sq_nonneg k)) ha
      (norm_nonneg _) (by positivity)
    _ ≤ leadingConstant k/‖x‖ := by
      unfold leadingConstant
      have hn : 0 ≤ k^2/(Real.pi*‖x‖) := by positivity
      convert (show k^2/(Real.pi*‖x‖) ≤ 3*(k^2/(Real.pi*‖x‖)) by linarith) using 1 <;> ring

theorem leading_electric_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖leadingE k x y j i‖ ≤ leadingConstant k/‖x‖ :=
  leading_bound k R hR x y hx hy _ (DyadicRadiation.transverse_norm_bound x i j)

theorem leading_magnetic_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖leadingH k x y j i‖ ≤ leadingConstant k/‖x‖ := by
  have ha : ∀ a, ‖polarization j a‖ ≤ 1 := by intro a; unfold polarization; split_ifs <;> norm_num
  have hb := cross_direction_bound (polarization j) x 1 (by norm_num) ha i
  have he : crossProduct (direction x) (polarization j) i =
      -crossProduct (polarization j) (direction x) i := by rw [cross_component, cross_component]; ring
  apply leading_bound k R hR x y hx hy _
  simpa only [he, norm_neg, mul_one] using hb

theorem magnetic_error (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖magneticDyadic k (x-y) i j-leadingH k x y j i‖ ≤ magneticErrorConstant k R/‖x‖^2 := by
  let e := fun a : Fin 3 => phiGradient k (x-y) a-Complex.I*(k : ℂ)*unitCoordinate a x*phi k (x-y)
  have he : magneticDyadic k (x-y) i j-leadingH k x y j i =
      -(Complex.I*(k : ℂ))*(e (next i)*(if previous i=j then 1 else 0)-
        e (previous i)*(if next i=j then 1 else 0)) := by
    rw [leadingH_component]
    unfold magneticDyadic e
    split_ifs <;> ring_nf
    all_goals norm_num [Complex.I_sq]
    all_goals ring
  have hb (a : Fin 3) : ‖e a‖ ≤ (2 * |k| * R+1)/(Real.pi*‖x‖^2) :=
    source_kernel_outgoing_bound k R hR x y hx hy a
  have hd (a b : Fin 3) : ‖(if a=b then 1 else 0 : ℂ)‖ ≤ 1 := by split_ifs <;> norm_num
  rw [he, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ |k| * (‖e (next i)*(if previous i=j then 1 else 0 : ℂ)‖+
        ‖e (previous i)*(if next i=j then 1 else 0 : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg k)
    _ ≤ |k| * (((2 * |k| * R+1)/(Real.pi*‖x‖^2))*1+
        ((2 * |k| * R+1)/(Real.pi*‖x‖^2))*1) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg k)
      simp only [norm_mul]
      exact add_le_add (mul_le_mul (hb _) (hd _ _) (norm_nonneg _) (by positivity))
        (mul_le_mul (hb _) (hd _ _) (norm_nonneg _) (by positivity))
    _ = _ := by unfold magneticErrorConstant; ring

theorem magnetic_bound (k R : ℝ) (hR : 0 ≤ R) (x y : Space)
    (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hy : y ∈ closedBall 0 R) (i j : Fin 3) :
    ‖magneticDyadic k (x-y) i j‖ ≤ (leadingConstant k+magneticErrorConstant k R)/‖x‖ := by
  have he := magnetic_error k R hR x y hx hy i j
  have hl := leading_magnetic_bound k R hR x y hx hy i j
  have hn := norm_add_le (magneticDyadic k (x-y) i j-leadingH k x y j i) (leadingH k x y j i)
  rw [sub_add_cancel] at hn
  have hp : 0 < ‖x‖ := by linarith
  have hC : 0 ≤ magneticErrorConstant k R := by unfold magneticErrorConstant; positivity
  have hd : magneticErrorConstant k R/‖x‖^2 ≤ magneticErrorConstant k R/‖x‖ :=
    div_le_div_of_nonneg_left hC hp (by nlinarith)
  exact (hn.trans (add_le_add (he.trans hd) hl)).trans_eq (by ring)

theorem leading_normal_cross_zero (k l : ℝ) (x y z : Space) (hx : x ≠ 0)
    (hp : x 2=0) (j m : Fin 3) :
    crossProduct (leadingE k x y j) (conjugate (leadingH l x z m)) 2 = 0 := by
  change leadingE k x y j 0*conj (leadingH l x z m 1)-leadingE k x y j 1*conj (leadingH l x z m 0)=0
  rw [← leading_identity k x y hx 0 j, ← leading_identity k x y hx 1 j]
  simp [cross_apply, leadingH, direction, unitCoordinate, hp]
  ring

def tailConstant (k l R : ℝ) : ℝ :=
  2*(electricErrorConstant k R*(leadingConstant l+magneticErrorConstant l R)+
    leadingConstant k*magneticErrorConstant l R)

theorem flux_tail (k l R : ℝ) (hR : 0 ≤ R) (x y z : Space)
    (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (hp : x 2=0)
    (hy : y ∈ closedBall 0 R) (hz : z ∈ closedBall 0 R) (j m : Fin 3) :
    ‖crossProduct (fun i => DyadicKernel.dyadic k (x-y) i j)
      (conjugate (fun i => magneticDyadic l (x-z) i m)) 2‖ ≤ tailConstant k l R/‖x‖^3 := by
  have h := cross_perturbation_bound
    (fun i => DyadicKernel.dyadic k (x-y) i j) (fun i => magneticDyadic l (x-z) i m)
    (leadingE k x y j) (leadingH l x z m)
    (leadingConstant k/‖x‖) ((leadingConstant l+magneticErrorConstant l R)/‖x‖)
    (electricErrorConstant k R/‖x‖^2) (magneticErrorConstant l R/‖x‖^2)
    (by unfold leadingConstant; positivity)
    (by unfold leadingConstant magneticErrorConstant; positivity)
    (by unfold electricErrorConstant; positivity) (by unfold magneticErrorConstant; positivity)
    (fun i => leading_electric_bound k R hR x y hx hy i j)
    (fun i => magnetic_bound l R hR x z hx hx₂ hz i m)
    (fun i => electric_error k R hR x y hx hx₂ hy i j)
    (fun i => magnetic_error l R hR x z hx hz i m)
    (leading_normal_cross_zero k l x y z (norm_pos_iff.mp (by linarith)) hp j m)
  exact h.trans_eq (by unfold tailConstant; field_simp; ring)

end OQ14.PointMaxwellTail
#print axioms OQ14.PointMaxwellTail.leading_identity
#print axioms OQ14.PointMaxwellTail.electric_error
#print axioms OQ14.PointMaxwellTail.leading_electric_bound
#print axioms OQ14.PointMaxwellTail.leading_magnetic_bound
#print axioms OQ14.PointMaxwellTail.magnetic_error
#print axioms OQ14.PointMaxwellTail.magnetic_bound
#print axioms OQ14.PointMaxwellTail.leading_normal_cross_zero
#print axioms OQ14.PointMaxwellTail.flux_tail
