import ConicalStaticVolume
import DynamicStaticLimit

/-! Actual frequency-dependent annular forcing and the conical volume solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalDynamicVolume
open OQ14.ConicalStaticVolume OQ14.NewtonL2 Filter
open scoped Topology

abbrev VectorL2 := VectorFourier.VectorL2

def response (p : Data) (k : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  newtonOperator+DynamicConvolution.operator k (2*p.cutoff.rOut)

def incident (p : Data) (k : ℝ) : VectorL2 := -response p k (annularSource p)
def forcing (p : Data) (k : ℝ) : VectorL2 := StaticCoefficient.sqrtMultiplier (coefficient p) (incident p k)
def solution (p : Data) (k : ℝ) : VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock (coefficient p) k p.cutoff.rOut) (forcing p k)
def totalSource (p : Data) (k : ℝ) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (coefficient p) (solution p k)-annularSource p
def field (p : Data) (k : ℝ) : VectorL2 := response p k (totalSource p k)

theorem remainder_norm (p : Data) (k : ℝ) :
    ‖DynamicConvolution.operator k (2*p.cutoff.rOut)‖ ≤ 252*p.cutoff.rOut^2*k^2 := by
  apply (DynamicConvolution.operator_norm_le k (2*p.cutoff.rOut) (by linarith [p.cutoff.rOut_pos])).trans_eq
  unfold DynamicConvolution.entryMass
  rw [DynamicVolume.unitBall_volume]
  field_simp [Real.pi_ne_zero]
  ring

theorem response_tendsto (p : Data) : Tendsto (response p) (𝓝 0) (𝓝 newtonOperator) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : ∀ k : ℝ, ‖response p k-newtonOperator‖ ≤ 252*p.cutoff.rOut^2*k^2 := by
    intro k
    simpa only [response,add_sub_cancel_left] using remainder_norm p k
  have hl : Tendsto (fun k : ℝ => 252*p.cutoff.rOut^2*k^2) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 0) (𝓝 0)).pow 2)
  exact squeeze_zero (fun _ => norm_nonneg _) he hl

def forcingConstant (p : Data) : ℝ :=
  Real.sqrt p.contrast*252*p.cutoff.rOut^2*‖annularSource p‖

theorem forcing_difference (p : Data) (k : ℝ) :
    forcing p k-staticForcing p= -StaticCoefficient.sqrtMultiplier (coefficient p)
      (DynamicConvolution.operator k (2*p.cutoff.rOut) (annularSource p)) := by
  simp only [forcing,incident,response,staticForcing,staticIncident,ContinuousLinearMap.add_apply,
    map_neg,map_add]
  abel

theorem forcing_difference_bound (p : Data) (k : ℝ) :
    ‖forcing p k-staticForcing p‖ ≤ forcingConstant p*k^2 := by
  rw [forcing_difference,norm_neg]
  apply (StaticCoefficient.applySqrt_norm (coefficient p) _).trans
  have hh := (ContinuousLinearMap.le_opNorm (DynamicConvolution.operator k (2*p.cutoff.rOut))
    (annularSource p)).trans (mul_le_mul_of_nonneg_right (remainder_norm p k) (norm_nonneg _))
  apply (mul_le_mul_of_nonneg_left hh (Real.sqrt_nonneg _)).trans_eq
  change Real.sqrt p.contrast*((252*p.cutoff.rOut^2*k^2)*‖annularSource p‖)=_
  unfold forcingConstant
  ring

theorem forcing_tendsto (p : Data) : Tendsto (forcing p) (𝓝 0) (𝓝 (staticForcing p)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hl : Tendsto (fun k : ℝ => forcingConstant p*k^2) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 0) (𝓝 0)).pow 2)
  exact squeeze_zero (fun _ => norm_nonneg _) (forcing_difference_bound p) hl

def solutionConstant (p : Data) : ℝ :=
  2*forcingConstant p+2*DynamicStaticLimit.size (coefficient p) p.cutoff.rOut*‖staticForcing p‖

theorem solution_difference_bound (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    ‖solution p k-weightedElectric p‖ ≤ solutionConstant p*k^2 := by
  rw [← static_inverse p]
  apply (DynamicStaticLimit.solution_comparison (coefficient p) k p.cutoff.rOut
    p.cutoff.rOut_pos.le hk (forcing p k) (staticForcing p)).trans
  apply (add_le_add_right (mul_le_mul_of_nonneg_left (forcing_difference_bound p k)
    (by norm_num : (0 : ℝ) ≤ 2)) _).trans_eq
  unfold solutionConstant
  ring

theorem solution_tendsto (p : Data) : Tendsto (solution p) (𝓝 0) (𝓝 (weightedElectric p)) := by
  have h := isBoundedBilinearMap_apply.continuous.tendsto
    (Ring.inverse (StaticNewton.volumeBlock (coefficient p)),staticForcing p) |>.comp
      ((DynamicStaticLimit.inverse_tendsto (coefficient p) p.cutoff.rOut p.cutoff.rOut_pos.le).prodMk_nhds
        (forcing_tendsto p))
  simpa only [solution,static_inverse] using h

theorem solution_equation (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    DynamicVolume.volumeBlock (coefficient p) k p.cutoff.rOut (solution p k)=forcing p k := by
  have he := DynamicStaticLimit.error_small (coefficient p) k p.cutoff.rOut hk
  have hu := DynamicVolume.volumeBlock_isUnit (coefficient p) k p.cutoff.rOut p.cutoff.rOut_pos.le (by linarith)
  exact congrArg (fun T : VectorL2 →L[ℂ] VectorL2 => T (forcing p k))
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock (coefficient p) k p.cutoff.rOut) hu)

theorem field_weighted (p : Data) (k : ℝ)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    StaticCoefficient.sqrtMultiplier (coefficient p) (field p k)=solution p k := by
  have he := solution_equation p k hk
  change solution p k-StaticCoefficient.sqrtMultiplier (coefficient p)
    (newtonOperator (StaticCoefficient.sqrtMultiplier (coefficient p) (solution p k)))-
      StaticCoefficient.sqrtMultiplier (coefficient p)
        (DynamicConvolution.operator k (2*p.cutoff.rOut)
          (StaticCoefficient.sqrtMultiplier (coefficient p) (solution p k)))=forcing p k at he
  simp only [forcing,incident,response,ContinuousLinearMap.add_apply,map_neg,map_add] at he
  simp only [field,totalSource,response,ContinuousLinearMap.add_apply,map_sub,map_add]
  rw [sub_eq_iff_eq_add,sub_eq_iff_eq_add] at he
  exact (by abel : _ = _).trans he.symm

theorem static_source_response (p : Data) :
    newtonOperator (materialSource p-annularSource p)=electric p := by
  have he := static_field_equation p
  rw [map_sub]
  rw [sub_eq_iff_eq_add] at he
  exact (by abel : _ = _).trans he.symm

theorem field_tendsto (p : Data) : Tendsto (field p) (𝓝 0) (𝓝 (electric p)) := by
  have hs := ((StaticCoefficient.sqrtMultiplier (coefficient p)).continuous.tendsto _).comp (solution_tendsto p)
  have ht := isBoundedBilinearMap_apply.continuous.tendsto
    (newtonOperator,materialSource p-annularSource p) |>.comp
      ((response_tendsto p).prodMk_nhds (hs.sub_const (annularSource p)))
  change Tendsto (field p) (𝓝 0) (𝓝 (newtonOperator (materialSource p-annularSource p))) at ht
  rwa [static_source_response] at ht

end OQ14.ConicalDynamicVolume

#print axioms OQ14.ConicalDynamicVolume.remainder_norm
#print axioms OQ14.ConicalDynamicVolume.response_tendsto
#print axioms OQ14.ConicalDynamicVolume.forcing_difference
#print axioms OQ14.ConicalDynamicVolume.forcing_difference_bound
#print axioms OQ14.ConicalDynamicVolume.forcing_tendsto
#print axioms OQ14.ConicalDynamicVolume.solution_difference_bound
#print axioms OQ14.ConicalDynamicVolume.solution_tendsto
#print axioms OQ14.ConicalDynamicVolume.solution_equation
#print axioms OQ14.ConicalDynamicVolume.field_weighted
#print axioms OQ14.ConicalDynamicVolume.static_source_response
#print axioms OQ14.ConicalDynamicVolume.field_tendsto
