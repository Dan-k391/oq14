import Packet05GraphSlope

/-! Graph slope derivatives have no normal component. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphSlopeNormal
open OQ14.ConicalJunctionPhysical OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphSlope
open OQ14.Maxwell (basis)

theorem slope_factor (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (i : Fin 3) :
    OQ14.Packet05GraphSlope.slope g i = (fun q : Plane => fderiv ℝ g q (horizontalLinear.toContinuousLinearMap (basis i))) ∘ horizontalLinear.toContinuousLinearMap := by
  funext x
  unfold OQ14.Packet05GraphSlope.slope
  rw [liftedHeight_fderiv g hg]
  rfl

theorem slope_normal_derivative (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (i : Fin 3) (x : Space) : fderiv ℝ (OQ14.Packet05GraphSlope.slope g i) x (basis 2) = 0 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  let S : Plane → ℝ := fun q => fderiv ℝ g q (horizontalLinear.toContinuousLinearMap (basis i))
  have hS : ContDiff ℝ 1 S := by
    exact (hg.contDiff_fderiv_apply (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
  rw [slope_factor g hg1 i]
  change fderiv ℝ (S ∘ horizontalLinear.toContinuousLinearMap) x (basis 2) = 0
  rw [fderiv_comp x (hS.differentiable (by norm_num) _)
    (horizontalLinear.toContinuousLinearMap.differentiable x)]
  simp only [ContinuousLinearMap.comp_apply, horizontalLinear.toContinuousLinearMap.fderiv,
    OQ14.Packet05GraphSmooth.horizontal_basis_normal, map_zero]

end OQ14.Packet05GraphSlopeNormal
#print axioms OQ14.Packet05GraphSlopeNormal.slope_factor
#print axioms OQ14.Packet05GraphSlopeNormal.slope_normal_derivative
