import Packet05GraphPullback

/-! Smooth physical graph shears have the expected normal derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphSmooth
open OQ14.ConicalJunctionPhysical OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphChartMap
open OQ14.Maxwell (basis)

theorem liftedHeight_contDiff (g : Plane → ℝ) {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (liftedHeight g) := by
  exact hg.comp horizontalLinear.toContinuousLinearMap.contDiff

theorem graphMap_contDiff (g : Plane → ℝ) {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (graphMap (liftedHeight g)) := by
  exact contDiff_id.add ((liftedHeight_contDiff g hg).smul contDiff_const)

theorem inverseGraphMap_contDiff (g : Plane → ℝ) {n : WithTop ℕ∞} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (inverseGraphMap (liftedHeight g)) := by
  exact contDiff_id.sub ((liftedHeight_contDiff g hg).smul contDiff_const)

theorem horizontal_basis_normal : horizontalLinear.toContinuousLinearMap (basis 2) = 0 := by
  ext i
  fin_cases i <;> simp [horizontalLinear, horizontal, basis, EuclideanSpace.single_apply]

theorem liftedHeight_normal_derivative (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (x : Space) :
    fderiv ℝ (liftedHeight g) x (basis 2) = 0 := by
  rw [show liftedHeight g = g ∘ horizontalLinear.toContinuousLinearMap by rfl]
  rw [fderiv_comp x (hg.differentiable (by norm_num) _) (horizontalLinear.toContinuousLinearMap.differentiable x)]
  change (fderiv ℝ g (horizontal x)) ((fderiv ℝ (⇑horizontalLinear.toContinuousLinearMap) x) (basis 2)) = 0
  rw [horizontalLinear.toContinuousLinearMap.fderiv, horizontal_basis_normal]
  simp

theorem graphMap_normal_derivative (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (x : Space) :
    fderiv ℝ (graphMap (liftedHeight g)) x (basis 2) = basis 2 := by
  rw [(graph_map_has_fderiv _ x _ ((liftedHeight_contDiff g hg).differentiable (by norm_num) x).hasFDerivAt).fderiv]
  simp [liftedHeight_normal_derivative g hg x]

theorem inverseGraphMap_normal_derivative (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (x : Space) :
    fderiv ℝ (inverseGraphMap (liftedHeight g)) x (basis 2) = basis 2 := by
  have hd := (hasFDerivAt_id x).sub (((liftedHeight_contDiff g hg).differentiable (by norm_num) x).hasFDerivAt.smul_const (basis 2))
  change HasFDerivAt (inverseGraphMap (liftedHeight g)) _ x at hd
  rw [hd.fderiv]
  simp [liftedHeight_normal_derivative g hg x]

end OQ14.Packet05GraphSmooth
#print axioms OQ14.Packet05GraphSmooth.liftedHeight_contDiff
#print axioms OQ14.Packet05GraphSmooth.graphMap_contDiff
#print axioms OQ14.Packet05GraphSmooth.inverseGraphMap_contDiff
#print axioms OQ14.Packet05GraphSmooth.horizontal_basis_normal
#print axioms OQ14.Packet05GraphSmooth.liftedHeight_normal_derivative
#print axioms OQ14.Packet05GraphSmooth.graphMap_normal_derivative
#print axioms OQ14.Packet05GraphSmooth.inverseGraphMap_normal_derivative
