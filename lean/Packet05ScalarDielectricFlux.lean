import Packet05ScalarCutoffTesting
import Packet05FlatWeight

/-! Exact tangential difference rule for the positive dielectric jump times a
smooth matrix: the coefficient commutator remains an explicit L² field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarDielectricFlux
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator
  OQ14.Packet05ScalarTransmissionCommutator

def flux (A : Fin 3 → Fin 3 → Test) (C : L2Vector) (d : ℝ) (hd : 0 ≤ d) : L2Vector :=
  fun j => mulWeight d hd (matrixField A C j)

theorem dielectric_flux_quotient (A : Fin 3 → Fin 3 → Test) (C : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    quotient (flux A C d hd j) i h = mulWeight d hd
      (matrixField A (fun l => quotient (C l) i h) j + matrixResidual A C i j h hh b hb) := by
  have hw := quotient_commutes_invariant_weight (flux A C d hd) (matrixField A C)
    (weight d) i h (weight_tangential d i hi h) (fun j => mulWeight_ae d hd _) j
  have he := matrix_quotient_decomposition A C i j h hh b hb
  apply Lp.ext
  filter_upwards [hw, mulWeight_ae d hd
    (matrixField A (fun l => quotient (C l) i h) j + matrixResidual A C i j h hh b hb)] with x hx hy
  change quotient (flux A C d hd j) i h x = _ at hx
  rw [hx, hy]
  change weight d x * quotient (matrixField A C j) i h x = _
  rw [he]

end OQ14.Packet05ScalarDielectricFlux
#print axioms OQ14.Packet05ScalarDielectricFlux.dielectric_flux_quotient
