import ModalAxialSymbol

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalAxialStatic
open Complex MeasureTheory OQ14.Maxwell OQ14.ModalAxialRotation OQ14.ModalAxialFourier
  OQ14.ModalAxialSymbol OQ14.ModalWeightedMode

theorem action_fourier_symm (θ : ℝ) (F : VectorFourier.VectorL2) :
    action θ (VectorFourier.fourier.symm F) = VectorFourier.fourier.symm (action θ F) := by
  apply VectorFourier.fourier.injective
  rw [LinearIsometryEquiv.apply_symm_apply, ← action_fourier,
    LinearIsometryEquiv.apply_symm_apply]

theorem action_projection (θ : ℝ) (F : VectorFourier.VectorL2) :
    action θ (VectorFourier.physicalProjection F) = VectorFourier.physicalProjection (action θ F) := by
  unfold VectorFourier.physicalProjection
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [action_fourier_symm, action_multiplier, action_fourier]

theorem sqrtMultiplier_comm (n : ℝ) (hn : 1 < n) (θ : ℝ) (F : VectorFourier.VectorL2) :
    action θ (StaticCoefficient.sqrtMultiplier (coefficient n hn) F) =
      StaticCoefficient.sqrtMultiplier (coefficient n hn) (action θ F) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae (coefficient n hn) F)
  have hs' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae (coefficient n hn) (action θ F))
  have hr := (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae hs
  filter_upwards [action_ae θ (StaticCoefficient.sqrtMultiplier (coefficient n hn) F) i,
    hr, hs', action_ae θ F i] with x h1 h2 h3 h4
  rw [h1, h3]
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [h4]
  simp_rw [h2]
  simp only [PiLp.smul_apply, smul_eq_mul]
  have hm : (coefficient n hn).value (VectorFourier.coordinateMap (rotation (-θ) x)) =
      (coefficient n hn).value (VectorFourier.coordinateMap x) := material_invariant n hn (-θ) x
  rw [hm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem static_volume_comm (n : ℝ) (hn : 1 < n) (θ : ℝ) (F : VectorFourier.VectorL2) :
    action θ (StaticNewton.volumeBlock (coefficient n hn) F) =
      StaticNewton.volumeBlock (coefficient n hn) (action θ F) := by
  rw [StaticNewton.volumeBlock_eq]
  unfold StaticCoefficient.weightedBlock
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply, map_add]
  rw [sqrtMultiplier_comm n hn, action_projection, sqrtMultiplier_comm n hn]

#print axioms OQ14.ModalAxialStatic.action_projection
#print axioms OQ14.ModalAxialStatic.sqrtMultiplier_comm
#print axioms OQ14.ModalAxialStatic.static_volume_comm
end OQ14.ModalAxialStatic


