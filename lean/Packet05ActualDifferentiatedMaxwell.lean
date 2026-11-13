import Packet05DifferentiatedCurl
import Packet05ActualPhaseDerivatives

/-! Connect differentiated local Maxwell equations to the actual regional
fields, rather than to arbitrary replacement fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ActualDifferentiatedMaxwell
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.CurlCutoff OQ14.DivCurlCompact OQ14.DivCurlRegularity
  OQ14.Packet05DifferentiatedCurl OQ14.Packet05TangentialRegularity
open scoped Topology

theorem nested_cutoff_field (Ω S : Set Space) (hΩ : IsOpen Ω)
    (κ χ : DomainCurl.Test Ω) (hχS : tsupport χ.function ⊆ S) (hSΩ : S ⊆ Ω)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (E : DomainCurl.HCurl Ω) (j : Fin 3) :
    (LocalPower.cutExtend hΩ χ E).val.1 j =
      scaleL2 χ.function χ.regular.continuous χ.compact ((LocalPower.cutExtend hΩ κ E).val.1 j) := by
  apply Lp.ext
  have hp := extendScalar_ae Ω hΩ.measurableSet (multiply Ω χ.toTest E.val.1 j)
  have hm := (ae_restrict_iff' hΩ.measurableSet).mp
    (mulL2_ae Ω χ.function χ.regular.continuous χ.compact (E.val.1 j))
  have he := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ κ E j)
  filter_upwards [hp, hm, he, scaleL2_ae χ.function χ.regular.continuous χ.compact
    ((LocalPower.cutExtend hΩ κ E).val.1 j)] with x hp hm he hs
  change extendScalar Ω hΩ.measurableSet (multiply Ω χ.toTest E.val.1 j) x = _
  rw [hp, hs]
  by_cases hx : x ∈ tsupport χ.function
  · have hxS := hχS hx
    have hxΩ := hSΩ hxS
    have hκx : κ.function x = 1 := (hκ x hxS).self_of_nhds
    rw [Set.indicator_of_mem hxΩ]
    change mulL2 Ω χ.function χ.regular.continuous χ.compact (E.val.1 j) x = _
    rw [hm hxΩ, he hxΩ, hκx]
    simp
  · have hz : χ.function x = 0 := image_eq_zero_of_nmem_tsupport hx
    by_cases hxΩ : x ∈ Ω
    · rw [Set.indicator_of_mem hxΩ]
      change mulL2 Ω χ.function χ.regular.continuous χ.compact (E.val.1 j) x = _
      rw [hm hxΩ, hz]
      simp
    · simp [hxΩ, hz]

theorem actual_cutoff_local_maxwell {Ω U : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hUΩ : U ⊆ Ω)
    (hχ : ∀ x ∈ U, χ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (k d : ℝ) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H) :
    (∀ j, ∀ᵐ x ∂volume, x ∈ U →
      (LocalPower.cutExtend hΩ χ E).val.2 j x =
        (Complex.I*(k : ℂ)) * (LocalPower.cutExtend hΩ χ H).val.1 j x) ∧
    (∀ j, ∀ᵐ x ∂volume, x ∈ U →
      (LocalPower.cutExtend hΩ χ H).val.2 j x = -(Complex.I*(k : ℂ)) *
        Packet05FlatWeight.mulWeight d hd ((LocalPower.cutExtend hΩ χ E).val.1 j) x) := by
  constructor
  · intro j
    have hc := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_curl_ae hΩ χ E j)
    have hh := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ χ H j)
    have hm := (ae_restrict_iff' hΩ.measurableSet).mp hM.1
    filter_upwards [hc, hh, hm] with x hc hh hm hx
    have hχx : χ.function x = 1 := (hχ x hx).self_of_nhds
    have hdχ : ∀ l, dcoord χ.function x l = 0 := by
      intro l
      simp [dcoord, (hχ x hx).fderiv_eq]
    rw [hc (hUΩ hx), hh (hUΩ hx), hχx, hdχ, hdχ]
    simpa using hm (hUΩ hx) j
  · intro j
    have hc := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_curl_ae hΩ χ H j)
    have he := (ae_restrict_iff' hΩ.measurableSet).mp (LocalPower.cutExtend_field_ae hΩ χ E j)
    have hm := (ae_restrict_iff' hΩ.measurableSet).mp hM.2
    filter_upwards [hc, he, hm, Packet05FlatWeight.mulWeight_ae d hd ((LocalPower.cutExtend hΩ χ E).val.1 j)]
      with x hc he hm hw hx
    have hχx : χ.function x = 1 := (hχ x hx).self_of_nhds
    have hdχ : ∀ l, dcoord χ.function x l = 0 := by
      intro l
      simp [dcoord, (hχ x hx).fderiv_eq]
    rw [hc (hUΩ hx), hw, he (hUΩ hx), hχx, hdχ, hdχ]
    simp only [one_mul, zero_mul, add_zero, sub_zero]
    rw [hm (hUΩ hx) j]
    simp only [Packet05FlatWeight.weight]
    ring

/-- Actual flat-interface Maxwell fields possess tangentially differentiated
Maxwell equations on every region where the inner cutoff equals one. -/
theorem actual_tangential_differentiated_maxwell {Ω U : Set Space}
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
    (hζder : ∀ l x, ‖dcoord ζ.complexTest.function x l‖ ≤ D)
    (hUopen : IsOpen U) (hU : U ⊆ Metric.ball c r)
    (hζunit : ∀ x ∈ U, ζ.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (i : Fin 3) (hi : i ≠ 2) :
    ∃ DE DH DW : L2Vector,
      (∀ j, HasWeakPartial
        (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
          ((LocalPower.cutExtend hΩ κ E).val.1 j)) (DE j) i) ∧
      (∀ j, HasWeakPartial
        (Packet05FlatWeight.mulWeight d hd
          (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
            ((LocalPower.cutExtend hΩ κ E).val.1 j))) (DW j) i) ∧
      (∀ j, DW j = Packet05FlatWeight.mulWeight d hd (DE j)) ∧
      (∀ (φ : Test), ContDiff ℝ 2 φ.function → tsupport φ.function ⊆ U → ∀ j,
        weakCurl φ j DE = (Complex.I*(k : ℂ)) * valuePair φ (DH j) ∧
        weakCurl φ j DH = -(Complex.I*(k : ℂ)) * valuePair φ (DW j)) ∧
      (∃ E' H' : DomainCurl.HCurl U,
        (∀ j, (fun x => E'.val.1 j x) =ᵐ[DomainCurl.regionMeasure U] fun x => DE j x) ∧
        (∀ j, (fun x => H'.val.1 j x) =ᵐ[DomainCurl.regionMeasure U] fun x => DH j x) ∧
        WeakConservation.WeakMaxwell k (fun _ => 1)
          (FlatDifferenceCoercivity.dielectric d) E' H') := by
  have hball : Metric.ball c r ⊆ Metric.ball c R := Metric.ball_subset_ball hrR.le
  let χ : DomainCurl.Test Ω := ⟨ζ.complexTest.toTest, ζ.complexTest.inside.trans (hball.trans hSΩ)⟩
  have hχS : tsupport χ.function ⊆ Metric.ball c R := ζ.complexTest.inside.trans hball
  have hχ2 : ContDiff ℝ 2 χ.function := hζ2
  have hUΩ : U ⊆ Ω := hU.trans (hball.trans hSΩ)
  let e := LocalPower.cutExtend hΩ χ E
  let h := LocalPower.cutExtend hΩ χ H
  let w : L2Vector := fun j => Packet05FlatWeight.mulWeight d hd (e.val.1 j)
  have hnest (j : Fin 3) : e.val.1 j =
      scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact
        ((LocalPower.cutExtend hΩ κ E).val.1 j) :=
    nested_cutoff_field Ω (Metric.ball c R) hΩ κ χ hχS hSΩ hκ E j
  have hEt := actual_ball_electric_tangential_weak_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder i hi
  have hWt := actual_ball_weighted_electric_tangential_derivative hΩ c r R hrR κ hκ2 hSΩ hκ
    A B hA hB hvκ hdκ k d hk hd E H hM ζ η hη hζ L C D hC hgrad hηbound hζder i hi
  have hEexist : ∀ j, ∃ v, HasWeakPartial (e.val.1 j) v i := by
    intro j
    rw [hnest j]
    exact hEt j
  have hWexist : ∀ j, ∃ v, HasWeakPartial (w j) v i := by
    intro j
    change ∃ v, HasWeakPartial (Packet05FlatWeight.mulWeight d hd (e.val.1 j)) v i
    rw [hnest j]
    exact hWt j
  classical
  choose DE hDE using hEexist
  choose DW hDW using hWexist
  obtain ⟨G, hG, _⟩ := LocalRegularity.maxwell_cutoff_magnetic_regularity
    hΩ χ hχ2 k hk _ E H hM
  let DH : L2Vector := fun j => G (i,j)
  have hDH : ∀ j, HasWeakPartial (h.val.1 j) (DH j) i := fun j => hG (i,j)
  have hloc := actual_cutoff_local_maxwell hΩ χ hUΩ hζunit k d hd E H hM
  have hconstitutive : ∀ j, DW j = Packet05FlatWeight.mulWeight d hd (DE j) := fun j =>
    Packet05LocalDerivative.weighted_partial_eq d hd (e.val.1 j) (DE j) (DW j) i (hDE j) (hDW j)
  have hpairs : ∀ (φ : Test), ContDiff ℝ 2 φ.function → tsupport φ.function ⊆ U → ∀ j,
      weakCurl φ j DE = (Complex.I*(k : ℂ)) * valuePair φ (DH j) ∧
      weakCurl φ j DH = -(Complex.I*(k : ℂ)) * valuePair φ (DW j) := by
    intro φ hφ hφU j
    exact differentiated_local_maxwell_pairing U e.val.1 e.val.2 h.val.1 h.val.2 w
      DE DH DW k i e.property h.property hDE hDH hDW hloc.1 hloc.2 φ hφ hφU j
  refine ⟨DE, DH, DW, ?_, ?_, hconstitutive, hpairs, ?_⟩
  · intro j
    rw [← hnest j]
    exact hDE j
  · intro j
    rw [← hnest j]
    exact hDW j
  · exact regional_maxwell_of_differentiated_pairings hUopen DE DH DW k d hd hconstitutive hpairs

end OQ14.Packet05ActualDifferentiatedMaxwell
#print axioms OQ14.Packet05ActualDifferentiatedMaxwell.nested_cutoff_field
#print axioms OQ14.Packet05ActualDifferentiatedMaxwell.actual_cutoff_local_maxwell
#print axioms OQ14.Packet05ActualDifferentiatedMaxwell.actual_tangential_differentiated_maxwell
