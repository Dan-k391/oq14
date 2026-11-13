import Packet05ActualGraphForcing
import Packet05GraphMetricCompact

/-! A binary weighted forcing has its actual normal derivative on each open
constant phase, even though it jumps across the interface. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05BinaryPhaseDerivative
open MeasureTheory Set OQ14.WeakCurl OQ14.DivCurlCompact OQ14.Packet05FlatWeight
  OQ14.Packet05RegionalPartial OQ14.Packet05ActualCorrectionH2

theorem binary_phase_partial (V : Set Maxwell.Space) (d : ℝ) (hd : 0 ≤ d)
    (ε : ℂ) (hphase : ∀ x ∈ V, weight d x = ε)
    (u Du : L2Scalar) (i : Fin 3) (hu : HasWeakPartial u Du i) :
    HasPartialOn V (mulWeight d hd u) (ε • Du) i := by
  apply partial_on_of_ae_eq V _ (ε • u) _ i
    (global_partial_on V _ _ i (weak_partial_smul ε u Du i hu))
  filter_upwards [mulWeight_ae d hd u, Lp.coeFn_smul ε u] with x hw hs hx
  rw [hw, hs, hphase x hx]
  rfl

end OQ14.Packet05BinaryPhaseDerivative
#print axioms OQ14.Packet05BinaryPhaseDerivative.binary_phase_partial
