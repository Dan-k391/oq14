import Packet05ScalarEnergyBound
import WeakPoynting.InteriorTestDensity

/-! Explicit cutoff-gradient bound for the H¹ test in the scalar energy
identity; no regularity beyond the existing weak derivatives is assumed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarCutoffBound
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.Packet05ScalarCutoffTesting

theorem cutoffDerivative_norm (χ : Test) (u : L2Scalar) (G : Fin 3 → L2Scalar)
    (i : Fin 3) (a b : ℝ)
    (ha : ∀ x, ‖χ.function x‖ ≤ a) (hb : ∀ x, ‖dcoord χ.function x i‖ ≤ b) :
    ‖cutoffDerivative χ u G i‖ ≤ a*‖G i‖ + b*‖u‖ := by
  unfold cutoffDerivative
  exact (norm_add_le _ _).trans (add_le_add
    (InteriorTestDensity.scaleL2_norm_le χ.function χ.regular.continuous χ.compact (G i) ha)
    (InteriorTestDensity.scaleL2_norm_le (fun x => dcoord χ.function x i)
      (partial_continuous χ.regular i) (χ.compact.fderiv_apply ℝ (basis i)) u hb))

end OQ14.Packet05ScalarCutoffBound
#print axioms OQ14.Packet05ScalarCutoffBound.cutoffDerivative_norm
