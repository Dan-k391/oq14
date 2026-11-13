import Packet05ScalarCutoffTransfer
import Packet05ScalarCutoffTesting
import WeakPoynting.Energy

/-! Exact square-cutoff product rule in L², including the factor two in the
cutoff cross term. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarSquareCutoff
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05ScalarCutoffTesting

def cutoffGradient (ζ : RealTest Set.univ) (u : L2Scalar) (i : Fin 3) : L2Scalar :=
  scaleL2 (fun x => dcoord ζ.complexTest.function x i)
    (partial_continuous ζ.complexTest.regular i)
    (ζ.complexTest.compact.fderiv_apply ℝ (basis i)) u

theorem square_cutoff_scale (ζ : RealTest Set.univ) (u : L2Scalar) :
    scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
      (squareTest ζ).complexTest.compact u = cutScalar ζ (cutScalar ζ u) := by
  apply Lp.ext
  filter_upwards [scaleL2_ae (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
    (squareTest ζ).complexTest.compact u, cutScalar_ae ζ (cutScalar ζ u), cutScalar_ae ζ u] with x h1 h2 h3
  rw [h1,h2,h3]
  simp [squareTest, RealTest.complexTest, Complex.ofReal_pow, pow_two, mul_assoc]

theorem square_cutoff_derivative_scale (ζ : RealTest Set.univ) (u : L2Scalar) (i : Fin 3) :
    scaleL2 (fun x => dcoord (squareTest ζ).complexTest.function x i)
      (partial_continuous (squareTest ζ).complexTest.regular i)
      ((squareTest ζ).complexTest.compact.fderiv_apply ℝ (basis i)) u =
    (2 : ℂ) • cutScalar ζ (cutoffGradient ζ u i) := by
  apply Lp.ext
  filter_upwards [scaleL2_ae (fun x => dcoord (squareTest ζ).complexTest.function x i)
      (partial_continuous (squareTest ζ).complexTest.regular i)
      ((squareTest ζ).complexTest.compact.fderiv_apply ℝ (basis i)) u,
    cutScalar_ae ζ (cutoffGradient ζ u i),
    scaleL2_ae (fun x => dcoord ζ.complexTest.function x i)
      (partial_continuous ζ.complexTest.regular i) (ζ.complexTest.compact.fderiv_apply ℝ (basis i)) u,
    Lp.coeFn_smul (2 : ℂ) (cutScalar ζ (cutoffGradient ζ u i))] with x h1 h2 h3 h4
  rw [h1,h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h2]
  change _ = (2 : ℂ) * ((ζ.function x : ℂ) * scaleL2 _ _ _ u x)
  rw [h3, realTest_partial, realTest_partial, squareTest_partial]
  push_cast
  simp only [WeakEnergy.gradient]
  ring

theorem square_cutoff_derivative (ζ : RealTest Set.univ) (u : L2Scalar)
    (Q : Fin 3 → L2Scalar) (i : Fin 3) :
    cutoffDerivative (squareTest ζ).complexTest.toTest u Q i =
      cutScalar ζ (cutScalar ζ (Q i)) + (2 : ℂ) • cutScalar ζ (cutoffGradient ζ u i) := by
  unfold cutoffDerivative
  rw [square_cutoff_scale, square_cutoff_derivative_scale]

end OQ14.Packet05ScalarSquareCutoff
#print axioms OQ14.Packet05ScalarSquareCutoff.square_cutoff_scale
#print axioms OQ14.Packet05ScalarSquareCutoff.square_cutoff_derivative_scale
#print axioms OQ14.Packet05ScalarSquareCutoff.square_cutoff_derivative
