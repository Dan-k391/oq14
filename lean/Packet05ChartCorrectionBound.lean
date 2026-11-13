import Packet05QuantitativeChartBranches

/-! Signed chart and cutoff preserve a uniform physical correction bound. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05ChartCorrectionBound
open Maxwell ConicalGradientGraph Packet05ChartBasis Packet05ChartElectricIdentity
  Packet05ChartCorrectionContinuous Packet05GraphChartMap Packet05PhysicalGraphChart
abbrev Plane := ConicalSmoothJunction.Plane
abbrev Space := Maxwell.Space

theorem chart_correction_bound (up : Bool) (i : Fin 3) (g : Plane → ℝ)
    (χ : ContDiffBump (0 : Space)) (W : Field) (T : Set Space) (X : ℝ)
    (hW : ∀ y j, inverseGraphMap (liftedHeight g) (Packet05ChartLinearEquiv.orientedLinear up i y) ∈ T →
      ‖W y j‖ ≤ X) (j : Fin 3) (x : Space) (hx : x ∈ T) :
    ‖chartCorrection up i g χ W j x‖ ≤ X := by
  let y := inverseOriented up i (graphMap (liftedHeight g) x)
  have hy : inverseGraphMap (liftedHeight g) (Packet05ChartLinearEquiv.orientedLinear up i y) = x := by
    change inverseGraphMap (liftedHeight g) (Packet05ChartLinearEquiv.orientedLinear up i
      (inverseOriented up i (graphMap (liftedHeight g) x))) = x
    change inverseGraphMap (liftedHeight g) (Packet05ChartOrientation.reflectNormal up
      (Packet07BoundaryCoordinates.swap i (inverseOriented up i (graphMap (liftedHeight g) x)))) = x
    rw [inverse_oriented_right]
    exact graph_map_left_inverse _ (liftedHeight_normal_invariant g) x
  have hw := hW y (Equiv.swap i 2 j) (hy ▸ hx)
  have hb : ‖bump χ y‖ ≤ 1 := by
    simpa only [bump,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg χ.nonneg] using χ.le_one
  have hx0 : 0 ≤ X := (norm_nonneg _).trans hw
  have hprod := mul_le_mul hb hw (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  change ‖(chartSign up j : ℂ) * bump χ y * W y (Equiv.swap i 2 j)‖ ≤ X
  rw [norm_mul,norm_mul]
  cases up
  · by_cases hj : j = 2 <;> simpa [chartSign,hj] using hprod
  · simpa [chartSign] using hprod

end OQ14.Packet05ChartCorrectionBound
#print axioms OQ14.Packet05ChartCorrectionBound.chart_correction_bound
