import DynamicConvolution
import StaticNewton

/-!
# Concrete small-volume dynamic operator and invertibility

The localized dyadic remainder is identified with the actual material-source
integrals. Its norm bound is derived from the actual kernel's L1 mass, and is
then combined with the identified static volume inverse.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.DynamicVolume

open MeasureTheory Metric
open scoped InnerProductSpace

abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Coefficient := StaticCoefficient.Coefficient

def source (c : Coefficient) (u : VectorL2) (j : Fin 3) (y : Space) : ℂ :=
  (Real.sqrt (c.value (VectorFourier.coordinateMap y)) : ℂ) *
    u (VectorFourier.coordinateMap y) j

theorem source_integrable (c : Coefficient) (u : VectorL2) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (j : Fin 3) : Integrable (source c u j) :=
  (StaticNewton.material_source_integrable c u (closedBall 0 R) (isCompact_closedBall 0 R) hc j).congr
    (StaticNewton.material_source_ae c u j)

theorem source_zero (c : Coefficient) (u : VectorL2) (R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (j : Fin 3) (y : Space) (hy : y ∉ closedBall 0 R) : source c u j y = 0 := by
  simp [source, hc y hy]

theorem kernel_source_eq (c : Coefficient) (u : VectorL2) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i j : Fin 3) (x y : Space) (hx : x ∈ closedBall 0 R) :
    DynamicConvolution.kernel k (2*R) i j (x-y) * source c u j y =
      DyadicKernel.remainder k (x-y) i j * source c u j y := by
  by_cases hy : y ∈ closedBall (0 : Space) R
  · have hxy : x-y ∈ closedBall (0 : Space) (2*R) := by
      have hx' : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hx
      have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
      have hn := norm_sub_le x y
      simp only [mem_closedBall, dist_zero_right]
      linarith
    simp [DynamicConvolution.kernel, hxy]
  · rw [source_zero c u R hc j y hy]
    simp

theorem remainder_source_integrable_ae (c : Coefficient) (u : VectorL2) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i j : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), x ∈ closedBall 0 R →
      Integrable (fun y => DyadicKernel.remainder k (x-y) i j * source c u j y) := by
  have h := (source_integrable c u R hc j).ae_convolution_exists
    (ContinuousLinearMap.mul ℂ ℂ) (DynamicConvolution.kernel_integrable k (2*R) i j)
  filter_upwards [h] with x hx hxb
  apply hx.congr
  filter_upwards with y
  change source c u j y * DynamicConvolution.kernel k (2*R) i j (x-y) = _
  rw [mul_comm, kernel_source_eq c u k R hc i j x y hxb]

def weightedRemainder (c : Coefficient) (k R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  StaticCoefficient.sqrtMultiplier c ∘L DynamicConvolution.operator k (2*R) ∘L
    StaticCoefficient.sqrtMultiplier c

def errorBound (c : Coefficient) (k R : ℝ) : ℝ :=
  9 * DynamicConvolution.entryMass k (2*R) * c.bound

theorem errorBound_nonnegative (c : Coefficient) (k R : ℝ) : 0 ≤ errorBound c k R :=
  mul_nonneg (mul_nonneg (by norm_num) (DynamicConvolution.entryMass_nonnegative k (2*R)))
    (StaticCoefficient.bound_nonnegative c)

theorem weightedRemainder_norm (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R) (u : VectorL2) :
    ‖weightedRemainder c k R u‖ ≤ errorBound c k R * ‖u‖ := by
  change ‖StaticCoefficient.sqrtMultiplier c
    (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u))‖ ≤ _
  calc
    _ ≤ Real.sqrt c.bound *
        ‖DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u)‖ :=
      StaticCoefficient.applySqrt_norm c _
    _ ≤ Real.sqrt c.bound * ((9 * DynamicConvolution.entryMass k (2*R)) *
        ‖StaticCoefficient.sqrtMultiplier c u‖) :=
      mul_le_mul_of_nonneg_left
        (DynamicConvolution.operator_norm k (2*R) (by linarith) _)
        (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt c.bound * ((9 * DynamicConvolution.entryMass k (2*R)) *
        (Real.sqrt c.bound * ‖u‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (StaticCoefficient.applySqrt_norm c u)
          (mul_nonneg (by norm_num) (DynamicConvolution.entryMass_nonnegative k (2*R))))
        (Real.sqrt_nonneg _)
    _ = errorBound c k R * ‖u‖ := by
      have hs := Real.sq_sqrt (StaticCoefficient.bound_nonnegative c)
      unfold errorBound
      calc
        _ = (Real.sqrt c.bound)^2 *
            ((9 * DynamicConvolution.entryMass k (2*R)) * ‖u‖) := by ring
        _ = _ := by rw [hs]; ring

theorem weightedRemainder_norm_le (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R) :
    ‖weightedRemainder c k R‖ ≤ errorBound c k R :=
  ContinuousLinearMap.opNorm_le_bound _ (errorBound_nonnegative c k R)
    (weightedRemainder_norm c k R hR)

theorem truncated_source_convolution (c : Coefficient) (u : VectorL2) (k R : ℝ)
    (i j : Fin 3) (x : Space) :
    HeatFourier.convolution (DynamicConvolution.kernel k (2*R) i j)
      (DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u)) x =
      ∫ y, DynamicConvolution.kernel k (2*R) i j (x-y) * source c u j y := by
  change MeasureTheory.convolution (DynamicConvolution.kernel k (2*R) i j)
    (DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u))
    (ContinuousLinearMap.mul ℂ ℂ) volume x = _
  rw [MeasureTheory.convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards [StaticNewton.material_source_ae c u j] with y hy
  rw [DynamicConvolution.component_apply, hy]
  rfl

/-- The weighted operator has the literal, untruncated dynamic dyadic integral
on the material support. Its defining truncation introduces no approximation. -/
theorem weightedRemainder_actual (c : Coefficient) (u : VectorL2) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => weightedRemainder c k R u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x-y) i j * source c u j y := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c
      (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u)))
  have hd := DynamicConvolution.operator_ae_convolution k (2*R)
    (StaticCoefficient.sqrtMultiplier c u)
    (StaticNewton.material_source_integrable c u (closedBall 0 R) (isCompact_closedBall 0 R) hc) i
  filter_upwards [hs, hd] with x hx hy
  change (StaticCoefficient.sqrtMultiplier c
    (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u)))
    (VectorFourier.coordinateMap x) i = _
  rw [hx]
  change (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
    (DynamicConvolution.operator k (2*R) (StaticCoefficient.sqrtMultiplier c u))
      (VectorFourier.coordinateMap x) i = _
  rw [hy]
  by_cases hxb : x ∈ closedBall (0 : Space) R
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [truncated_source_convolution]
    apply integral_congr_ae
    filter_upwards with y
    exact kernel_source_eq c u k R hc i j x y hxb
  · simp [hc x hxb]

def volumeBlock (c : Coefficient) (k R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  StaticNewton.volumeBlock c - weightedRemainder c k R

theorem volumeBlock_actual (c : Coefficient) (u : VectorL2) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => volumeBlock c k R u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => u (VectorFourier.coordinateMap x) i -
        (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
          (StaticNewton.response c u (VectorFourier.coordinateMap x) i +
            ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x-y) i j * source c u j y) := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticNewton.volumeBlock_ae c u)
  have hd := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_sub (StaticNewton.volumeBlock c u) (weightedRemainder c k R u))
  filter_upwards [hs, hd, weightedRemainder_actual c u k R hc i] with x hs hd hq
  change (StaticNewton.volumeBlock c u - weightedRemainder c k R u)
    (VectorFourier.coordinateMap x) i = _
  rw [hd]
  simp only [Pi.sub_apply, hs, Pi.smul_apply, smul_eq_mul]
  change u (VectorFourier.coordinateMap x) i -
    (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
      StaticNewton.response c u (VectorFourier.coordinateMap x) i -
    weightedRemainder c k R u (VectorFourier.coordinateMap x) i = _
  rw [hq]
  ring

theorem volumeBlock_isUnit (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : errorBound c k R < 1) : IsUnit (volumeBlock c k R) := by
  unfold volumeBlock
  rw [StaticNewton.volumeBlock_eq]
  exact StaticCoefficient.weightedBlock_perturbation_isUnit c _
    ((weightedRemainder_norm_le c k R hR).trans_lt hsmall)

theorem volumeBlock_inverse_bound (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : errorBound c k R < 1) :
    ‖Ring.inverse (volumeBlock c k R)‖ ≤ (1 - errorBound c k R)⁻¹ := by
  unfold volumeBlock
  rw [StaticNewton.volumeBlock_eq]
  have hn := weightedRemainder_norm_le c k R hR
  apply (StaticCoefficient.weightedBlock_perturbation_inverse c _
    (hn.trans_lt hsmall)).trans
  simpa only [one_div] using one_div_le_one_div_of_le
    (sub_pos.mpr hsmall) (sub_le_sub_left hn 1)

theorem existsUnique_solution (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : errorBound c k R < 1) (f : VectorL2) :
    ∃! u : VectorL2, volumeBlock c k R u = f := by
  have hunit := volumeBlock_isUnit c k R hR hsmall
  have hs := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel (volumeBlock c k R) hunit)
  change volumeBlock c k R (Ring.inverse (volumeBlock c k R) f) = f at hs
  refine ⟨Ring.inverse (volumeBlock c k R) f, hs, ?_⟩
  intro u hu
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1 (hu.trans hs.symm)

theorem solution_norm_bound (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : errorBound c k R < 1) (u f : VectorL2) (hsol : volumeBlock c k R u = f) :
    ‖u‖ ≤ (1 - errorBound c k R)⁻¹ * ‖f‖ := by
  have hunit := volumeBlock_isUnit c k R hR hsmall
  have hs := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L u)
    (Ring.inverse_mul_cancel (volumeBlock c k R) hunit)
  change Ring.inverse (volumeBlock c k R) (volumeBlock c k R u) = u at hs
  rw [hsol] at hs
  rw [← hs]
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    (mul_le_mul_of_nonneg_right (volumeBlock_inverse_bound c k R hR hsmall) (norm_nonneg f))

end OQ14.DynamicVolume

#print axioms OQ14.DynamicVolume.source_integrable
#print axioms OQ14.DynamicVolume.source_zero
#print axioms OQ14.DynamicVolume.kernel_source_eq
#print axioms OQ14.DynamicVolume.remainder_source_integrable_ae
#print axioms OQ14.DynamicVolume.errorBound_nonnegative
#print axioms OQ14.DynamicVolume.weightedRemainder_norm
#print axioms OQ14.DynamicVolume.weightedRemainder_norm_le
#print axioms OQ14.DynamicVolume.truncated_source_convolution
#print axioms OQ14.DynamicVolume.weightedRemainder_actual
#print axioms OQ14.DynamicVolume.volumeBlock_actual
#print axioms OQ14.DynamicVolume.volumeBlock_isUnit
#print axioms OQ14.DynamicVolume.volumeBlock_inverse_bound
#print axioms OQ14.DynamicVolume.existsUnique_solution
#print axioms OQ14.DynamicVolume.solution_norm_bound
