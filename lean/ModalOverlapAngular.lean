import ModalOverlapRadial
import ConicalAngularTrial
import ComplexPolarIntegration
import SphereHarmonicAddition
import ModalVolumeData
import KernelReciprocity
import ModalOverlapBoundary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace OQ14.ModalOverlapAngular
open Complex MeasureTheory Set Metric OQ14.Maxwell OQ14.AngularPower OQ14.ConicalAngularTrial
open scoped Topology
abbrev Space := Maxwell.Space

def area : ℂ := (angularMeasure.real Set.univ : ℂ)

theorem area_ne_zero : area ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt SphereHarmonicAddition.area_pos)

theorem integral_square : (∫ n : Sphere, ((ConicalAngularTrial.coordinate 2 n : ℂ)^2) ∂angularMeasure) = area/3 := by
  have h := unweighted_balance 2
  have hi := continuous_integrable _ ((coordinate_continuous 2).pow 2)
  have hreal : (∫ n : Sphere, ConicalAngularTrial.coordinate 2 n ^ 2 ∂angularMeasure) = angularMeasure.real Set.univ/3 := by
    rw [integral_sub (integrable_const _) (hi.const_mul _), integral_const_mul] at h
    simp only [integral_const, smul_eq_mul, mul_one] at h
    change angularMeasure.real Set.univ - 3 * (∫ n : Sphere, ConicalAngularTrial.coordinate 2 n ^ 2 ∂angularMeasure) = 0 at h
    linarith

  have hc := integral_ofReal (𝕜 := ℂ) (μ := angularMeasure) (f := fun n : Sphere => ConicalAngularTrial.coordinate 2 n ^ 2)
  rw [hreal] at hc
  push_cast at hc
  simpa [area] using hc

theorem integral_affine_square (c d : ℂ) :
    (∫ n : Sphere, c + d*((ConicalAngularTrial.coordinate 2 n : ℂ)^2) ∂angularMeasure) =
      area*(c+d/3) := by
  have hi : Integrable (fun n : Sphere => ((ConicalAngularTrial.coordinate 2 n : ℂ)^2)) angularMeasure :=
    ((Complex.continuous_ofReal.comp (coordinate_continuous 2)).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [integral_add (integrable_const _) (hi.const_mul _), integral_const_mul, integral_square]
  simp only [integral_const, smul_eq_mul]
  change area*c+d*(area/3)=_
  ring
def rayDot (a b : ℂ) (r : ℝ) (n : Sphere) : ℂ :=
  ∑ j : Fin 3, ModalOrigin.centerE a (r • (n : Space)) j * ModalOrigin.centerE b (r • (n : Space)) j

theorem rayDot_formula (a b : ℂ) (r : ℝ) (hr : 0 ≤ r) (n : Sphere) :
    rayDot a b r n = ModalOrigin.centerA a r * ModalOrigin.centerA b r +
      ((r : ℂ)^2 * (ModalOrigin.centerA a r * ModalOrigin.centerB b r +
        ModalOrigin.centerA b r * ModalOrigin.centerB a r) + (r : ℂ)^4 *
        ModalOrigin.centerB a r * ModalOrigin.centerB b r) * ((ConicalAngularTrial.coordinate 2 n : ℂ)^2) := by
  have hn : ‖r • (n : Space)‖ = r := by simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, AngularPower.sphere_norm]
  have hs : ((n : Space) 0 : ℂ)^2 + ((n : Space) 1 : ℂ)^2 + ((n : Space) 2 : ℂ)^2 = 1 := by
    have h := coordinate_squares n
    simp only [Fin.sum_univ_three, ConicalAngularTrial.coordinate] at h
    exact_mod_cast h
  unfold rayDot ModalOrigin.centerE ModalDipole.axisField
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one, hn, PiLp.smul_apply, smul_eq_mul, ofReal_mul, ConicalAngularTrial.coordinate]
  linear_combination ((r : ℂ)^4 * ModalOrigin.centerB a r * ModalOrigin.centerB b r * ((n : Space) 2 : ℂ)^2)*hs

theorem angular_average (a b : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    (∫ n : Sphere, rayDot a b r n ∂angularMeasure) =
      area*(ModalOrigin.centerA a r * ModalOrigin.centerA b r +
        ((r : ℂ)^2 * (ModalOrigin.centerA a r * ModalOrigin.centerB b r +
          ModalOrigin.centerA b r * ModalOrigin.centerB a r) + (r : ℂ)^4 *
            ModalOrigin.centerB a r * ModalOrigin.centerB b r)/3) := by
  simp_rw [rayDot_formula a b r hr]
  exact integral_affine_square _ _
def ballDot (a b : ℂ) : Space → ℂ :=
  (closedBall (0 : Space) 1).indicator (fun x => ∑ j : Fin 3, ModalOrigin.centerE a x j * ModalOrigin.centerE b x j)

theorem ballDot_integrable (a b : ℂ) : Integrable (ballDot a b) := by
  apply (integrable_indicator_iff measurableSet_closedBall).mpr
  apply ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) 1)
  apply Continuous.continuousOn
  apply continuous_finset_sum
  intro j _
  exact (ModalOrigin.centerE_continuous a j).mul (ModalOrigin.centerE_continuous b j)

theorem ballDot_integral (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hab : b^2-a^2 ≠ 0) :
    (∫ x, ballDot a b x) = area * ModalOverlapRadial.regularizedPrimitive a b 1 := by
  rw [ComplexPolarIntegration.integral_polar_complex _ (ballDot_integrable a b)]
  have hp : (fun r : ℝ => (r^2 : ℂ) * (∫ n : Sphere, ballDot a b (r • (n : Space)) ∂angularMeasure))
      =ᵐ[volume.restrict (Set.Ioi 0)] (fun r => Set.Ioc (0 : ℝ) 1 |>.indicator
        (fun r => area * ModalOverlapRadial.physicalRadial a b r) r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hr' : 0 < r := hr
    by_cases h1 : r ≤ 1
    · have hm (n : Sphere) : r • (n : Space) ∈ closedBall (0 : Space) 1 := by
        simpa [mem_closedBall, dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr', sphere_norm] using h1
      have he : (fun n : Sphere => ballDot a b (r • (n : Space))) = rayDot a b r := by
        funext n
        simp [ballDot,hm n,rayDot]
      rw [he, angular_average a b r hr'.le]
      simp only [indicator_of_mem (show r ∈ Set.Ioc (0 : ℝ) 1 from ⟨hr,h1⟩)]
      unfold ModalOverlapRadial.physicalRadial
      ring
    · have hm (n : Sphere) : r • (n : Space) ∉ closedBall (0 : Space) 1 := by
        simpa [mem_closedBall, dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hr', sphere_norm] using h1
      have he : (fun n : Sphere => ballDot a b (r • (n : Space))) = 0 := by
        funext n; simp [ballDot,hm n]
      rw [he]
      simp [h1]
  rw [integral_congr_ae hp, integral_indicator measurableSet_Ioc]
  have he : (volume.restrict (Set.Ioi (0 : ℝ))).restrict (Set.Ioc (0 : ℝ) 1) = volume.restrict (Set.Ioc 0 1) := by
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    ext r
    simp only [mem_inter_iff,mem_Ioi,mem_Ioc]
    tauto
  rw [he, integral_const_mul]
  rw [← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rw [ModalOverlapRadial.physicalRadial_integral a b ha hb hab]
theorem overlap_eq (n : ℝ) (hn : 1 < n) (k : ℂ) (hk : k ≠ 0) :
    KernelReciprocity.vectorPair (ModalVolumeData.incident n hn k) (ModalVolumeData.numerator n hn k) =
      ((n^2-1 : ℝ) : ℂ) * (I/(n : ℂ)) *
        (area * ModalOverlapRadial.regularizedPrimitive k ((n : ℂ)*k) 1) := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hn2 : ((n : ℂ)^2-1) ≠ 0 := by
    apply sub_ne_zero.mpr
    have h : n^2 ≠ 1 := by nlinarith
    exact_mod_cast h
  have hi (j : Fin 3) : Integrable ((closedBall (0 : Space) 1).indicator
      (fun x => ModalOrigin.centerE k x j * ModalOrigin.centerE ((n : ℂ)*k) x j)) := by
    apply (integrable_indicator_iff measurableSet_closedBall).mpr
    exact ((ModalOrigin.centerE_continuous k j).mul (ModalOrigin.centerE_continuous ((n : ℂ)*k) j)).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Space) 1)
  rw [KernelReciprocity.vectorPair_actual]
  have he (j : Fin 3) : (∫ x : Space, ModalVolumeData.incident n hn k (VectorFourier.coordinateMap x) j *
      ModalVolumeData.numerator n hn k (VectorFourier.coordinateMap x) j) =
      ((n^2-1 : ℝ) : ℂ) * (I/(n : ℂ)) * ∫ x, (closedBall (0 : Space) 1).indicator
        (fun x => ModalOrigin.centerE k x j * ModalOrigin.centerE ((n : ℂ)*k) x j) x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ModalVolumeData.incident_actual n hn k j, ModalVolumeData.numerator_actual n hn k j,
      OQ14.RadialInterface.ae_regular 1] with x hf hu hx
    rw [hf,hu,ModalWeightedMode.coefficient_value]
    by_cases hin : ‖x‖ < 1
    · have hcl : x ∈ closedBall (0 : Space) 1 := by simpa using hin.le
      rw [if_pos hin,indicator_of_mem hcl]
      have hsq : (Real.sqrt (n^2-1) : ℂ)^2 = ((n^2-1 : ℝ) : ℂ) := by
        rw [← ofReal_pow, Real.sq_sqrt (by nlinarith : 0 ≤ n^2-1)]
      linear_combination (ModalOrigin.centerE k x j * (I/(n : ℂ)) * ModalOrigin.centerE ((n : ℂ)*k) x j)*hsq
    · have hcl : x ∉ closedBall (0 : Space) 1 := by
        intro hh
        have hle : ‖x‖ ≤ 1 := by simpa using hh
        exact hin (lt_of_le_of_ne hle hx.2)
      simp [hin,hcl]
  simp_rw [he]
  rw [← Finset.mul_sum, ← integral_finset_sum _ (fun j _ => hi j)]
  have hsum : (fun x => ∑ j : Fin 3, (closedBall (0 : Space) 1).indicator
      (fun x => ModalOrigin.centerE k x j * ModalOrigin.centerE ((n : ℂ)*k) x j) x) = ballDot k ((n : ℂ)*k) := by
    funext x
    by_cases hx : x ∈ closedBall (0 : Space) 1 <;> simp [ballDot,hx]
  rw [hsum, ballDot_integral k ((n : ℂ)*k) hk (mul_ne_zero hn0 hk)]
  have heq : ((n : ℂ)*k)^2-k^2 = ((n : ℂ)^2-1)*k^2 := by ring
  rw [heq]
  exact mul_ne_zero hn2 (pow_ne_zero 2 hk)
theorem overlap_nonzero (n : ℝ) (hn : 1 < n) (k : ℂ) (hk : k ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) k = 0) :
    KernelReciprocity.vectorPair (ModalVolumeData.incident n hn k) (ModalVolumeData.numerator n hn k) ≠ 0 := by
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hn2 : ((n : ℂ)^2-1) ≠ 0 := by
    apply sub_ne_zero.mpr
    have h : n^2 ≠ 1 := by nlinarith
    exact_mod_cast h
  have hw := ModalOverlapBoundary.regular_boundary_wronskian_ne_zero (n : ℂ) k hn0 hk hd
  rw [overlap_eq n hn k hk, ModalOverlapRadial.special_endpoint (n : ℂ) k hn0 hk hn2]
  have he : ((n^2-1 : ℝ) : ℂ) * (I/(n : ℂ)) *
      (area * ((2/3)*((n : ℂ)*k)/((n : ℂ)^2-1) *
        ((n : ℂ)*ModalAlgebra.psi 1 ((n : ℂ)*k)*ModalAlgebra.psiD 1 k-
          ModalAlgebra.psi 1 k*ModalAlgebra.psiD 1 ((n : ℂ)*k)))) =
      (2/3)*I*k*area*((n : ℂ)*ModalAlgebra.psi 1 ((n : ℂ)*k)*ModalAlgebra.psiD 1 k-
          ModalAlgebra.psi 1 k*ModalAlgebra.psiD 1 ((n : ℂ)*k)) := by
    push_cast
    field_simp [hn0,hn2]
    ring
  rw [he]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hk) area_ne_zero) hw
end OQ14.ModalOverlapAngular
#print axioms OQ14.ModalOverlapAngular.integral_square









#print axioms OQ14.ModalOverlapAngular.angular_average




#print axioms OQ14.ModalOverlapAngular.ballDot_integral



#print axioms OQ14.ModalOverlapAngular.overlap_eq



#print axioms OQ14.ModalOverlapAngular.overlap_nonzero

#print axioms OQ14.ModalOverlapAngular.area_ne_zero
#print axioms OQ14.ModalOverlapAngular.integral_affine_square
#print axioms OQ14.ModalOverlapAngular.rayDot_formula
#print axioms OQ14.ModalOverlapAngular.ballDot_integrable
