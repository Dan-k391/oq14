import Packet05LocalPartialProduct

/-! Divide a regional weak derivative by a smooth nonvanishing coefficient
using an explicitly localized reciprocal; no derivative is assumed for u. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalReciprocalDerivative
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05LocalPartialProduct

theorem local_reciprocal_weak_partial (V W : Set Space) (A r χ : Test)
    (hrV : tsupport r.function ⊆ V) (hχW : tsupport χ.function ⊆ W)
    (hrecip : ∀ x ∈ W, r.function x * A.function x = 1)
    (u D : L2Scalar) (i : Fin 3)
    (hD : HasPartialOn V (scaleL2 A.function A.regular.continuous A.compact u) D i) :
    ∃ Du : L2Scalar, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact u) Du i := by
  let p := scaleL2 A.function A.regular.continuous A.compact u
  let rp := scaleL2 r.function r.regular.continuous r.compact p
  let Dr := scaleL2 r.function r.regular.continuous r.compact D +
    scaleL2 (fun x => dcoord r.function x i) (partial_continuous r.regular i)
      (r.compact.fderiv_apply ℝ (basis i)) p
  have hrp : HasWeakPartial rp Dr i := local_cutoff_weak_partial V r hrV p D i hD
  have heq : ∀ᵐ x ∂volume, x ∈ W → u x = rp x := by
    filter_upwards [scaleL2_ae A.function A.regular.continuous A.compact u,
      scaleL2_ae r.function r.regular.continuous r.compact p] with x ha hr hx
    change u x = scaleL2 r.function r.regular.continuous r.compact p x
    rw [hr]
    change u x = r.function x * scaleL2 A.function A.regular.continuous A.compact u x
    rw [ha, ← mul_assoc, hrecip x hx, one_mul]
  have hu : HasPartialOn W u Dr i := partial_on_of_ae_eq W u rp Dr i (global_partial_on W rp Dr i hrp) heq
  exact ⟨_,local_cutoff_weak_partial W χ hχW u Dr i hu⟩

end OQ14.Packet05LocalReciprocalDerivative
#print axioms OQ14.Packet05LocalReciprocalDerivative.local_reciprocal_weak_partial
