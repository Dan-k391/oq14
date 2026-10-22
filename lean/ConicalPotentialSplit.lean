import ConicalSpatialMaxwell
import ElectricPotentialDecomposition

/-! Actual conical scalar potential and a uniform continuous quadratic-frequency correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalPotentialSplit
open MeasureTheory Metric OQ14.ConicalStaticVolume OQ14.ConicalDynamicVolume
  OQ14.ConicalSpatialMaxwell OQ14.DynamicSource

abbrev Space := FourierL2.Space
def potential (p : Data) (k : ℝ) : Space → ℂ :=
  ElectricPotentialDecomposition.potential k (source p k)
def correction (p : Data) (k : ℝ) : Maxwell.Field :=
  ElectricPotentialDecomposition.correction k (source p k)

theorem frequencyRadius_le_one (p : Data) :
    DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut ≤ 1 := by
  have h := DynamicStaticLimit.size_nonnegative (coefficient p) p.cutoff.rOut
  unfold DynamicStaticLimit.frequencyRadius
  exact (inv_le_one₀ (by positivity)).mpr (by linarith)

theorem solutionConstant_nonnegative (p : Data) : 0 ≤ solutionConstant p := by
  have h := DynamicStaticLimit.size_nonnegative (coefficient p) p.cutoff.rOut
  unfold solutionConstant forcingConstant
  positivity

theorem solution_norm_bound (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    ‖solution p k‖ ≤ ‖weightedElectric p‖+solutionConstant p := by
  have hk1 := hk.trans (frequencyRadius_le_one p)
  have hk2 : k^2 ≤ 1 := by nlinarith [sq_abs k,abs_nonneg k]
  calc
    _ ≤ ‖solution p k-weightedElectric p‖+‖weightedElectric p‖ := by
      simpa only [sub_add_cancel] using norm_add_le (solution p k-weightedElectric p) (weightedElectric p)
    _ ≤ solutionConstant p*k^2+‖weightedElectric p‖ := add_le_add_right (solution_difference_bound p k hk) _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hk2 (solutionConstant_nonnegative p)]

def sourceBound (p : Data) : ℝ :=
  Real.sqrt p.contrast*(‖weightedElectric p‖+solutionConstant p)+‖annularSource p‖

theorem totalSource_norm_bound (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    ‖totalSource p k‖ ≤ sourceBound p := by
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  exact (StaticCoefficient.applySqrt_norm (coefficient p) _).trans
    (mul_le_mul_of_nonneg_left (solution_norm_bound p k hk) (Real.sqrt_nonneg _))

theorem potential_weak_gradient (p : Data) (k : ℝ) (i : Fin 3) (f : Test) :
    (∫ x, potential p k x*(testPartial i f).val x)=
      -(∫ x, (ConicalSpatialMaxwell.electric p k x i-correction p k x i)*f.val x) :=
  ElectricPotentialDecomposition.potential_weak_partial k (totalSource p k) (source p k)
    (source_integrable p k) (source_compact p k) (source_ae p k) i f

theorem potential_memLp (p : Data) (k R : ℝ) :
    MemLp (potential p k) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  ElectricPotentialDecomposition.potential_memLp_ball k R p.cutoff.rOut (totalSource p k) (source p k)
    (source_integrable p k) (source_zero_outer p k) (source_ae p k)

theorem gradient_memLp (p : Data) (k R : ℝ) (i : Fin 3) :
    MemLp (fun x => ConicalSpatialMaxwell.electric p k x i-correction p k x i) 2
      (volume.restrict (closedBall (0 : Space) R)) :=
  ElectricPotentialDecomposition.gradient_memLp_ball k R p.cutoff.rOut (totalSource p k) (source p k)
    (source_integrable p k) (source_zero_outer p k) (source_ae p k) i

theorem correction_continuous (p : Data) (k : ℝ) (i : Fin 3) : Continuous (fun x => correction p k x i) :=
  ElectricPotentialDecomposition.correction_continuous k p.cutoff.rOut (totalSource p k) (source p k)
    (source_zero_outer p k) (source_ae p k) i

theorem correction_bound (p : Data) (k R : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut)
    (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) R) :
    ‖correction p k x i‖ ≤ k^2*sourceBound p*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖ := by
  apply (ElectricPotentialDecomposition.correction_bound k R p.cutoff.rOut (totalSource p k) (source p k)
    (source_zero_outer p k) (source_ae p k) i x hx).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
  exact (DynamicConvolution.component_norm i (totalSource p k)).trans (totalSource_norm_bound p k hk)

end OQ14.ConicalPotentialSplit

#print axioms OQ14.ConicalPotentialSplit.frequencyRadius_le_one
#print axioms OQ14.ConicalPotentialSplit.solutionConstant_nonnegative
#print axioms OQ14.ConicalPotentialSplit.solution_norm_bound
#print axioms OQ14.ConicalPotentialSplit.totalSource_norm_bound
#print axioms OQ14.ConicalPotentialSplit.potential_weak_gradient
#print axioms OQ14.ConicalPotentialSplit.potential_memLp
#print axioms OQ14.ConicalPotentialSplit.gradient_memLp
#print axioms OQ14.ConicalPotentialSplit.correction_continuous
#print axioms OQ14.ConicalPotentialSplit.correction_bound
