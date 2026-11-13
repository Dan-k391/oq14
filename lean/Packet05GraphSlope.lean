import Packet05GraphTestChain

/-! Graph slopes are smooth tangential functions, invariant along vertical
fibers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphSlope
open OQ14.ConicalJunctionPhysical OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphSmooth
open OQ14.Maxwell (basis)

def slope (g : Plane → ℝ) (i : Fin 3) (x : Space) : ℝ :=
  fderiv ℝ (liftedHeight g) x (basis i)

theorem liftedHeight_fderiv (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (x : Space) :
    fderiv ℝ (liftedHeight g) x =
      (fderiv ℝ g (horizontal x)).comp horizontalLinear.toContinuousLinearMap := by
  change fderiv ℝ (g ∘ horizontalLinear.toContinuousLinearMap) x = _
  rw [fderiv_comp x (hg.differentiable (by norm_num) _)
    (horizontalLinear.toContinuousLinearMap.differentiable x), horizontalLinear.toContinuousLinearMap.fderiv]
  rfl

theorem slope_normal_invariant (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (i : Fin 3) (x : Space) (t : ℝ) : slope g i (x + t • basis 2) = slope g i x := by
  unfold slope
  rw [liftedHeight_fderiv g hg, liftedHeight_fderiv g hg, horizontal_normal_invariant]

theorem slope_continuous (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (i : Fin 3) :
    Continuous (slope g i) := by
  exact ((liftedHeight_contDiff g hg).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem slope_contDiff (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (i : Fin 3) :
    ContDiff ℝ 1 (slope g i) := by
  exact ((liftedHeight_contDiff g hg).contDiff_fderiv_apply (by norm_num)).comp
    (contDiff_id.prodMk contDiff_const)

end OQ14.Packet05GraphSlope
#print axioms OQ14.Packet05GraphSlope.liftedHeight_fderiv
#print axioms OQ14.Packet05GraphSlope.slope_normal_invariant
#print axioms OQ14.Packet05GraphSlope.slope_continuous
#print axioms OQ14.Packet05GraphSlope.slope_contDiff
