import FlatNestedMaxwellForcing
import MaxwellQuotientEnergy

/-! The actual flat-interface source and the independently controlled
lower-order magnetic difference quotients on a common cutoff. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FlatActualForcing
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.CurlCutoff OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCurlCutoffSource

theorem actual_flat_forcing_and_magnetic_quotient
    {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function) (η : Test)
    (hη : ∀ x ∈ tsupport χ.function, η.function x = 1)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hv : ∀ x, ‖χ.function x‖ ≤ A)
    (hder : ∀ l x, ‖dcoord χ.function x l‖ ≤ B)
    (hder2 : ∀ l m x, ‖dcoord (fun y => dcoord χ.function y l) x m‖ ≤ C) :
    (∃ (W : DomainCurl.HCurl Ω) (u : WeakCurl.HCurl) (Wext Cext : L2Vector),
      (∀ j, (fun x => Wext j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => W.val.1 j x) ∧
      (∀ j, (fun x => Cext j x) =ᵐ[DomainCurl.regionMeasure Ω] fun x => H.val.2 j x) ∧
      (∀ j, (fun x => u.val.2 j x) =ᵐ[DomainCurl.regionMeasure Ω]
        fun x => χ.function x * (k^2 : ℂ) * H.val.1 j x + source χ.toTest hχ Wext j x) ∧
      ∀ i j, i ≠ 2 → ∀ h : ℝ, h ≠ 0 →
        ‖quotient (source χ.toTest hχ Wext j) i h‖ ≤
          B * (‖quotient (NestedCurlCutoffSource.localize η Cext (previous j)) i h‖ +
            ‖quotient (NestedCurlCutoffSource.localize η Cext (next j)) i h‖) +
          3*C*(‖NestedCurlCutoffSource.localize η Wext (previous j)‖ +
            ‖NestedCurlCutoffSource.localize η Wext (next j)‖)) ∧
    ∀ i j (h : ℝ), h ≠ 0 →
      ‖quotient (extendVector Ω hΩ.measurableSet (multiply Ω χ.toTest H.val.1) j) i h‖ ≤
        3 * (3 * (A * (|k| * (1+d) * ‖E.val.1‖) + 2 * B * ‖H.val.1‖)^2 +
          (3 * B * ‖H.val.1‖)^2 + 1) := by
  constructor
  · exact FlatNestedMaxwellForcing.actual_nested_forcing hΩ χ hχ η hη k d hd E H hM B C hB hder hder2
  · apply MaxwellQuotientEnergy.cutoff_quotient_energy hΩ χ hχ hA hB (by linarith) hv hder k hk _ E H hM
    filter_upwards with x
    rw [abs_of_nonneg (le_trans (by norm_num) (FlatDifferenceCoercivity.dielectric_bounds d hd x).1)]
    exact (FlatDifferenceCoercivity.dielectric_bounds d hd x).2

end OQ14.Packet05FlatActualForcing
#print axioms OQ14.Packet05FlatActualForcing.actual_flat_forcing_and_magnetic_quotient
