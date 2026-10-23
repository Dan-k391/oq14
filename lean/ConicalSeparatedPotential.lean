import ConicalSeparatedMaxwell

/-! Actual weak scalar potential and uniform quadratic correction for the separated conical family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalSeparatedPotential
open MeasureTheory Metric OQ14.ConicalStaticVolume OQ14.ConicalSeparatedSource
  OQ14.ConicalSeparatedDynamic OQ14.ConicalSeparatedMaxwell OQ14.DynamicSource

abbrev Space := Maxwell.Space

def potential (p : Data) (a k : ℝ) : Space → ℂ := ElectricPotentialDecomposition.potential k (source p a k)
def correction (p : Data) (a k : ℝ) : Maxwell.Field := ElectricPotentialDecomposition.correction k (source p a k)

theorem frequencyRadius_le_one (p : Data) (a : ℝ) :
    DynamicStaticLimit.frequencyRadius (material p a) a ≤ 1 := by
  have h := DynamicStaticLimit.size_nonnegative (material p a) a
  unfold DynamicStaticLimit.frequencyRadius
  exact (inv_le_one₀ (by positivity)).mpr (by linarith)

def incidentBound (p : Data) (a : ℝ) : ℝ :=
  ‖ConicalSeparatedSource.staticIncident p a‖+63*(a+p.cutoff.rOut)^2*‖ConicalSeparatedSource.forcing p a‖

theorem incident_norm_bound (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a) : ‖incident p a k‖ ≤ incidentBound p a := by
  have hk1 := hk.trans (frequencyRadius_le_one p a)
  have hk2 : k^2 ≤ 1 := by nlinarith [sq_abs k,abs_nonneg k]
  calc
    _ ≤ ‖incident p a k-ConicalSeparatedSource.staticIncident p a‖+‖ConicalSeparatedSource.staticIncident p a‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (incident p a k-ConicalSeparatedSource.staticIncident p a) (ConicalSeparatedSource.staticIncident p a)
    _ ≤ (63*(a+p.cutoff.rOut)^2*‖ConicalSeparatedSource.forcing p a‖)*k^2+
        ‖ConicalSeparatedSource.staticIncident p a‖ := add_le_add_right (incident_difference_bound p a k ha) _
    _ ≤ _ := by
      have hc : 0 ≤ 63*(a+p.cutoff.rOut)^2*‖ConicalSeparatedSource.forcing p a‖ := by positivity
      have hm := mul_le_mul_of_nonneg_left hk2 hc
      unfold incidentBound
      linarith

theorem solution_norm_bound (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a) :
    ‖solution p a k‖ ≤ 2*Real.sqrt p.contrast*incidentBound p a := by
  apply ((Ring.inverse (DynamicVolume.volumeBlock (material p a) k a)).le_opNorm _).trans
  apply (mul_le_mul_of_nonneg_right (DynamicStaticLimit.inverse_norm_two (material p a) k a ha hk)
    (norm_nonneg _)).trans
  have hw := (StaticCoefficient.applySqrt_norm (material p a) (incident p a k)).trans
    (mul_le_mul_of_nonneg_left (incident_norm_bound p a k ha hk) (Real.sqrt_nonneg _))
  change ‖weightedForcing p a k‖ ≤ Real.sqrt p.contrast*incidentBound p a at hw
  exact (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

def sourceBound (p : Data) (a : ℝ) : ℝ :=
  Real.sqrt p.contrast*(2*Real.sqrt p.contrast*incidentBound p a)+‖ConicalSeparatedSource.forcing p a‖

theorem totalSource_norm_bound (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a) :
    ‖totalSource p a k‖ ≤ sourceBound p a := by
  apply (norm_sub_le _ _).trans
  apply add_le_add_right
  exact (StaticCoefficient.applySqrt_norm (material p a) _).trans
    (mul_le_mul_of_nonneg_left (solution_norm_bound p a k ha hk) (Real.sqrt_nonneg _))

theorem potential_weak_gradient (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) (f : Test) :
    (∫ x, potential p a k x*(testPartial i f).val x)=
      -(∫ x, (electric p a k x i-correction p a k x i)*f.val x) :=
  ElectricPotentialDecomposition.potential_weak_partial k (totalSource p a k) (source p a k)
    (source_integrable p a k hai) (source_compact p a k hai) (source_ae p a k) i f

theorem potential_memLp (p : Data) (a k R : ℝ) (hai : a < p.cutoff.rIn) :
    MemLp (potential p a k) 2 (volume.restrict (closedBall (0 : Space) R)) :=
  ElectricPotentialDecomposition.potential_memLp_ball k R p.cutoff.rOut (totalSource p a k) (source p a k)
    (source_integrable p a k hai) (source_zero_outer p a k hai) (source_ae p a k)

theorem gradient_memLp (p : Data) (a k R : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    MemLp (fun x => electric p a k x i-correction p a k x i) 2
      (volume.restrict (closedBall (0 : Space) R)) :=
  ElectricPotentialDecomposition.gradient_memLp_ball k R p.cutoff.rOut (totalSource p a k) (source p a k)
    (source_integrable p a k hai) (source_zero_outer p a k hai) (source_ae p a k) i

theorem correction_continuous (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    Continuous (fun x => correction p a k x i) :=
  ElectricPotentialDecomposition.correction_continuous k p.cutoff.rOut (totalSource p a k) (source p a k)
    (source_zero_outer p a k hai) (source_ae p a k) i

theorem correction_bound (p : Data) (a k R : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a)
    (i : Fin 3) (x : Space) (hx : x ∈ closedBall (0 : Space) R) :
    ‖correction p a k x i‖ ≤ k^2*sourceBound p a*‖ScalarPotentialBound.cutoff 0 (R+p.cutoff.rOut)‖ := by
  apply (ElectricPotentialDecomposition.correction_bound k R p.cutoff.rOut (totalSource p a k) (source p a k)
    (source_zero_outer p a k hai) (source_ae p a k) i x hx).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
  exact (DynamicConvolution.component_norm i (totalSource p a k)).trans (totalSource_norm_bound p a k ha hk)

end OQ14.ConicalSeparatedPotential

#print axioms OQ14.ConicalSeparatedPotential.frequencyRadius_le_one
#print axioms OQ14.ConicalSeparatedPotential.incident_norm_bound
#print axioms OQ14.ConicalSeparatedPotential.solution_norm_bound
#print axioms OQ14.ConicalSeparatedPotential.totalSource_norm_bound
#print axioms OQ14.ConicalSeparatedPotential.potential_weak_gradient
#print axioms OQ14.ConicalSeparatedPotential.potential_memLp
#print axioms OQ14.ConicalSeparatedPotential.gradient_memLp
#print axioms OQ14.ConicalSeparatedPotential.correction_continuous
#print axioms OQ14.ConicalSeparatedPotential.correction_bound
