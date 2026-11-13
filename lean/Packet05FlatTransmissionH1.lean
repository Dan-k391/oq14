import Packet05TangentialRegularity

/-! Full first-order transmission regularity in the natural flat-interface
variables: tangential E and dielectric-weighted normal E. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FlatTransmissionH1
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05TangentialRegularity
open scoped Topology

def transmissionComponent (d : ℝ) (hd : 0 ≤ d) (F : L2Vector) (j : Fin 3) : L2Scalar :=
  if j = 2 then Packet05FlatWeight.mulWeight d hd (F j) else F j

/-- All nine global L² weak partials of the physically continuous
transmission variables are derived from the actual regional Maxwell field. -/
theorem actual_flat_transmission_h1 {Ω : Set Space}
    (hΩ : IsOpen Ω) (c : Space) (r R : ℝ) (hrR : r < R)
    (κ : DomainCurl.Test Ω) (hκ2 : ContDiff ℝ 2 κ.function)
    (hSΩ : Metric.ball c R ⊆ Ω)
    (hκ : ∀ x ∈ Metric.ball c R, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hvκ : ∀ x, ‖κ.function x‖ ≤ A) (hdκ : ∀ l x, ‖dcoord κ.function x l‖ ≤ B)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ : WeakConservation.RealTest (Metric.ball c r))
    (hζ2 : ContDiff ℝ 2 ζ.complexTest.function) (η : DomainCurl.Test (Metric.ball c r))
    (hη : ∀ x ∈ tsupport ζ.function, η.function x = 1)
    (hζ : ∀ x, ‖ζ.function x‖ ≤ 1) (L C D : ℝ) (hC : 0 ≤ C)
    (hgrad : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ x) ≤ L^2)
    (hηbound : ∀ x, ‖η.function x‖ ≤ C)
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D) :
    ∃ G : Fin 3 → Fin 3 → L2Scalar,
      ∀ i j, HasWeakPartial (transmissionComponent d hd
        (fun j => scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
          ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)) j) (G i j) i := by
  let F : L2Vector := fun j => scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous
    ζ.complexTest.compact ((LocalPower.cutExtend hΩ κ E).val.1 j)
  have ht := actual_ball_electric_tangential_weak_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  have hn := actual_ball_electric_normal_tangential_components hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  have hw := actual_ball_weighted_electric_tangential_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder
  have hwn := actual_ball_weighted_electric_normal_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ hζ2 η hη hζ L C D hC hgrad hηbound hζder
  have hall : ∀ i j, ∃ v, HasWeakPartial (transmissionComponent d hd F j) v i := by
    intro i j
    by_cases hi : i = 2
    · subst i
      by_cases hj : j = 2
      · subst j
        simpa [transmissionComponent, F] using hwn
      · simpa [transmissionComponent, F, hj] using hn j hj
    · by_cases hj : j = 2
      · subst j
        simpa [transmissionComponent, F] using hw i hi 2
      · simpa [transmissionComponent, F, hj] using ht i hi j
  classical
  choose G hG using hall
  exact ⟨G, hG⟩

end OQ14.Packet05FlatTransmissionH1
#print axioms OQ14.Packet05FlatTransmissionH1.actual_flat_transmission_h1
