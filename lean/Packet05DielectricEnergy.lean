import Packet05GraphL2Coercivity
import Packet05FlatWeight
import WeakPoynting.Poynting

/-! The genuine binary dielectric contributes a positive Hermitian L²
energy, uniformly bounded below by the unweighted norm. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DielectricEnergy
open MeasureTheory OQ14.WeakCurl OQ14.WeakGreen OQ14.WeakPower OQ14.DivCurl
  OQ14.Packet05FlatWeight
open scoped ComplexConjugate

theorem dielectric_energy_lower (d : ℝ) (hd : 0 ≤ d) (u : L2Scalar) :
    ‖u‖^2 ≤ (scalarProduct (mulWeight d hd u) (conjScalar u)).re := by
  have hi := scalarProduct_integrable (mulWeight d hd u) (conjScalar u)
  rw [scalarProduct_integral, ← RCLike.re_eq_complex_re, ← integral_re hi, scalar_norm_squared]
  apply integral_mono_ae (scalar_normSq_integrable u) hi.re
  filter_upwards [mulWeight_ae d hd u, conjScalar_ae u] with x hw hc
  rw [hw,hc]
  have hε := (FlatDifferenceCoercivity.dielectric_bounds d hd x).1
  have hz : 0 ≤ Complex.normSq (u x) := Complex.normSq_nonneg _
  have he : ((weight d x * u x) * conj (u x)).re =
      FlatDifferenceCoercivity.dielectric d x * Complex.normSq (u x) := by
    simp [weight, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    <;> ring
  change Complex.normSq (u x) ≤ ((weight d x * u x) * conj (u x)).re
  rw [he]
  nlinarith

end OQ14.Packet05DielectricEnergy
#print axioms OQ14.Packet05DielectricEnergy.dielectric_energy_lower
