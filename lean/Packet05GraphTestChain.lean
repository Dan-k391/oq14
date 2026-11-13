import Packet05GraphNormalWeakDerivative

/-! Exact tangential chain rule on smooth inverse-chart tests, retaining the
slope term that creates the variable-coefficient transmission matrix. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphTestChain
open OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
  OQ14.Packet05GraphSmooth OQ14.Packet05GraphNormalWeakDerivative
open OQ14.Maxwell (basis dcoord)

theorem inverseGraphMap_derivative (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (x : Space) (i : Fin 3) :
    fderiv ℝ (inverseGraphMap (liftedHeight g)) x (basis i) =
      basis i - (fderiv ℝ (liftedHeight g) x (basis i)) • basis 2 := by
  have hd := (hasFDerivAt_id x).sub
    (((liftedHeight_contDiff g hg).differentiable (by norm_num) x).hasFDerivAt.smul_const (basis 2))
  change HasFDerivAt (inverseGraphMap (liftedHeight g)) _ x at hd
  rw [hd.fderiv]
  simp

theorem inverseTest_partial (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (φ : Test)
    (x : Space) (i : Fin 3) :
    dcoord (inverseTest g hg φ).function x i =
      dcoord φ.function (inverseGraphMap (liftedHeight g) x) i -
        (fderiv ℝ (liftedHeight g) x (basis i) : ℂ) *
          dcoord φ.function (inverseGraphMap (liftedHeight g) x) 2 := by
  change fderiv ℝ (φ.function ∘ inverseGraphMap (liftedHeight g)) x (basis i) = _
  rw [fderiv_comp x (φ.regular.differentiable (by norm_num) _)
    ((inverseGraphMap_contDiff g hg).differentiable (by norm_num) x)]
  simp only [ContinuousLinearMap.comp_apply, inverseGraphMap_derivative g hg x i,
    map_sub, map_smul, Complex.real_smul]
  rfl

end OQ14.Packet05GraphTestChain
#print axioms OQ14.Packet05GraphTestChain.inverseGraphMap_derivative
#print axioms OQ14.Packet05GraphTestChain.inverseTest_partial
