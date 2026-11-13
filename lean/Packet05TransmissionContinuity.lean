import Packet05LocalizedAnisotropic
import Packet05FlatTransmissionH1
import Packet05LocalDerivative

/-! Continuity of a cutoff transmission vector from its differentiated
Maxwell transmission fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05TransmissionContinuity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05FlatTransmissionH1
  OQ14.Packet05LocalizedAnisotropic

theorem weight_scale_commute (d : ℝ) (hd : 0 ≤ d) (χ : Test) (u : L2Scalar) :
    Packet05FlatWeight.mulWeight d hd (scaleL2 χ.function χ.regular.continuous χ.compact u) =
      scaleL2 χ.function χ.regular.continuous χ.compact (Packet05FlatWeight.mulWeight d hd u) := by
  apply Lp.ext
  filter_upwards [Packet05FlatWeight.mulWeight_ae d hd
      (scaleL2 χ.function χ.regular.continuous χ.compact u),
    scaleL2_ae χ.function χ.regular.continuous χ.compact u,
    Packet05FlatWeight.mulWeight_ae d hd u,
    scaleL2_ae χ.function χ.regular.continuous χ.compact (Packet05FlatWeight.mulWeight d hd u)]
    with x h1 h2 h3 h4
  rw [h1, h2, h4, h3]
  ring

/-- The explicit first and differentiated transmission graphs suffice for
continuous representatives of all three localized transmission components. -/
theorem cutoff_transmission_continuous (F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (D : Fin 3 → Fin 3 → L2Scalar)
    (hD : ∀ i j, HasWeakPartial (transmissionComponent d hd F j) (D i j) i)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hT : ∀ i, i ≠ 2 → ∃ (DE : L2Vector) (G : Fin 3 → Fin 3 → L2Scalar),
      (∀ j, HasWeakPartial (F j) (DE j) i) ∧
      (∀ t j, HasWeakPartial (transmissionComponent d hd
        (fun j => scaleL2 χ.function χ.regular.continuous χ.compact (DE j)) j) (G t j) t)) :
    ∀ j, ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact
        (transmissionComponent d hd F j) x) =ᵐ[volume] f := by
  intro j
  apply cutoff_continuous_of_tangential_h1 (transmissionComponent d hd F j)
    (fun i => D i j) (fun i => hD i j) χ hχ2
  intro i hi t
  obtain ⟨DE,G,hDE,hG⟩ := hT i hi
  by_cases hj : j = 2
  · subst j
    have hw : D i 2 = Packet05FlatWeight.mulWeight d hd (DE 2) := by
      apply Packet05LocalDerivative.weighted_partial_eq d hd (F 2) (DE 2) (D i 2) i (hDE 2)
      simpa [transmissionComponent] using hD i 2
    refine ⟨G t 2, ?_⟩
    rw [hw, ← weight_scale_commute]
    simpa [transmissionComponent] using hG t 2
  · have he : D i j = DE j := by
      apply Packet05LocalDerivative.weak_partial_unique (F j) (D i j) (DE j) i
      · simpa [transmissionComponent, hj] using hD i j
      · exact hDE j
    refine ⟨G t j, ?_⟩
    rw [he]
    simpa [transmissionComponent, hj] using hG t j

end OQ14.Packet05TransmissionContinuity
#print axioms OQ14.Packet05TransmissionContinuity.weight_scale_commute
#print axioms OQ14.Packet05TransmissionContinuity.cutoff_transmission_continuous
