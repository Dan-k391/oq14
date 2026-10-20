import SmallVolumeMaxwell
import WeakPoynting.RegionalCurlUpgrade

/-! # Actual dielectric volume fields in regional H(curl)

The smooth-test equations are upgraded using interior test approximation.
The resulting graph representatives agree with the constructed spatial fields.
The final existence statement uses the proved small-volume inverse.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaterialHCurl

open MeasureTheory Metric OQ14.Maxwell OQ14.MaterialMaxwell
open scoped Topology

theorem coefficient_mul_memLp (Ω : Set Space) (ε : Space → ℝ)
    (hε : Measurable ε) (M : ℝ) (hb : ∀ x, ‖ε x‖ ≤ M)
    (f : Space → ℂ) (hf : MemLp f 2 (DomainCurl.regionMeasure Ω)) :
    MemLp (fun x => (ε x : ℂ) * f x) 2 (DomainCurl.regionMeasure Ω) := by
  apply hf.of_le_mul
  · exact ((Complex.continuous_ofReal.measurable.comp hε).aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)

def electricCurl (k : ℝ) (H : Field) : Field :=
  fun x j => Complex.I * (k : ℂ) * H x j

def magneticCurl (k : ℝ) (ε : Space → ℝ) (E : Field) : Field :=
  fun x j => -(Complex.I * (k : ℂ)) * ((ε x : ℂ) * E x j)

theorem testMaxwell_electric_curl {Ω : Set Space} (hΩ : IsOpen Ω)
    (k : ℝ) (ε : Space → ℝ) (E H : Field)
    (hE : ∀ j, MemLp (fun x => E x j) 2 (DomainCurl.regionMeasure Ω))
    (hH : ∀ j, MemLp (fun x => H x j) 2 (DomainCurl.regionMeasure Ω))
    (hMax : TestMaxwell k ε E H) :
    DomainCurl.HasWeakCurl Ω (DomainCurl.fieldToL2 Ω E hE)
      (DomainCurl.fieldToL2 Ω (electricCurl k H)
        (fun j => (hH j).const_mul (Complex.I * (k : ℂ)))) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hΩ
  intro f hf hc _ j
  let g : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz f hf hc, hc⟩
  have hh := (hMax j g).1
  simp only [MagneticResponse.curlPair, fieldPair, DynamicSource.testPartial,
    GradientProjection.pderivative_apply] at hh
  change (∫ x, E x (WeakCurl.next j) * dcoord f x (WeakCurl.previous j)) -
      (∫ x, E x (WeakCurl.previous j) * dcoord f x (WeakCurl.next j)) =
      Complex.I * (k : ℂ) * ∫ x, H x j * f x at hh
  simpa only [electricCurl, mul_assoc, integral_const_mul] using hh.symm

theorem testMaxwell_magnetic_curl {Ω : Set Space} (hΩ : IsOpen Ω)
    (k : ℝ) (ε : Space → ℝ) (E H : Field)
    (hH : ∀ j, MemLp (fun x => H x j) 2 (DomainCurl.regionMeasure Ω))
    (hD : ∀ j, MemLp (fun x => (ε x : ℂ) * E x j) 2 (DomainCurl.regionMeasure Ω))
    (hMax : TestMaxwell k ε E H) :
    DomainCurl.HasWeakCurl Ω (DomainCurl.fieldToL2 Ω H hH)
      (DomainCurl.fieldToL2 Ω (magneticCurl k ε E)
        (fun j => (hD j).const_mul (-(Complex.I * (k : ℂ))))) := by
  apply RegionalCurlUpgrade.fields_hasWeakCurl_of_global_smooth hΩ
  intro f hf hc _ j
  let g : DynamicSource.Test := ⟨FourierL2.compactSmoothSchwartz f hf hc, hc⟩
  have hh := (hMax j g).2
  simp only [MagneticResponse.curlPair, fieldPair, DynamicSource.testPartial,
    GradientProjection.pderivative_apply] at hh
  change (∫ x, H x (WeakCurl.next j) * dcoord f x (WeakCurl.previous j)) -
      (∫ x, H x (WeakCurl.previous j) * dcoord f x (WeakCurl.next j)) =
      -(Complex.I * (k : ℂ)) * ∫ x, (ε x : ℂ) * E x j * f x at hh
  simpa only [magneticCurl, mul_assoc, integral_const_mul] using hh.symm

/-- Regional graph fields and their Maxwell equations are constructed from
the actual spatial fields and smooth-test identities. -/
theorem exists_regional_fields {Ω : Set Space} (hΩ : IsOpen Ω)
    (k : ℝ) (ε : Space → ℝ) (E H : Field)
    (hE : ∀ j, MemLp (fun x => E x j) 2 (DomainCurl.regionMeasure Ω))
    (hH : ∀ j, MemLp (fun x => H x j) 2 (DomainCurl.regionMeasure Ω))
    (hD : ∀ j, MemLp (fun x => (ε x : ℂ) * E x j) 2 (DomainCurl.regionMeasure Ω))
    (hMax : TestMaxwell k ε E H) :
    ∃ e h : DomainCurl.HCurl Ω,
      (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω] fun x => E x j) ∧
      (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω] fun x => H x j) ∧
      WeakConservation.WeakMaxwell k (fun _ => 1) ε e h := by
  let hCE := fun j => (hH j).const_mul (Complex.I * (k : ℂ))
  let hCH := fun j => (hD j).const_mul (-(Complex.I * (k : ℂ)))
  let e : DomainCurl.HCurl Ω :=
    ⟨(DomainCurl.fieldToL2 Ω E hE, DomainCurl.fieldToL2 Ω (electricCurl k H) hCE),
      testMaxwell_electric_curl hΩ k ε E H hE hH hMax⟩
  let h : DomainCurl.HCurl Ω :=
    ⟨(DomainCurl.fieldToL2 Ω H hH, DomainCurl.fieldToL2 Ω (magneticCurl k ε E) hCH),
      testMaxwell_magnetic_curl hΩ k ε E H hH hD hMax⟩
  refine ⟨e, h, fun j => (hE j).coeFn_toLp, fun j => (hH j).coeFn_toLp, ?_, ?_⟩
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [(hCE j).coeFn_toLp, (hH j).coeFn_toLp] with x hc hh
    change (hCE j).toLp _ x = Complex.I * (k : ℂ) * (1 : ℂ) * (hH j).toLp _ x
    rw [hc, hh]
    simp only [mul_one]
  · apply ae_all_iff.mpr
    intro j
    filter_upwards [(hCH j).coeFn_toLp, (hE j).coeFn_toLp] with x hc he
    change (hCH j).toLp _ x = -Complex.I * (k : ℂ) * (ε x : ℂ) * (hE j).toLp _ x
    rw [hc, he]
    ring

theorem memLp_bounded_of_balls (f : Space → ℂ)
    (hf : ∀ R : ℝ, MemLp f 2 (volume.restrict (closedBall 0 R)))
    (Ω : Set Space) (hbΩ : Bornology.IsBounded Ω) :
    MemLp f 2 (DomainCurl.regionMeasure Ω) := by
  obtain ⟨R, hR⟩ := hbΩ.subset_closedBall (0 : Space)
  exact (hf R).mono_measure (Measure.restrict_mono hR le_rfl)

theorem dielectric_measurable (c : StaticCoefficient.Coefficient) :
    Measurable (dielectric c) :=
  measurable_const.add (c.measurable.comp VectorFourier.coordinateMap_preserving.measurable)

theorem dielectric_norm_bound (c : StaticCoefficient.Coefficient) (x : Space) :
    ‖dielectric c x‖ ≤ 1 + c.bound := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (by norm_num) (dielectric_bounds c x).1)]
  exact (dielectric_bounds c x).2

/-- Actual regional H(curl) Maxwell fields on every bounded open observation
region, including regions crossing the material interface. -/
theorem small_volume_hcurl_exists (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (hR : 0 ≤ R) (hsmall : 252 * c.bound * k^2 * R^2 < 1)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    ∃ u : VectorFourier.VectorL2,
      DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R) ∧
      ‖u‖ ≤ (1 - 252 * c.bound * k^2 * R^2)⁻¹ *
        ‖IncidentLocalization.datum c R Einc hc (hE R)‖ ∧
      ∀ Ω : Set Space, IsOpen Ω → Bornology.IsBounded Ω →
        ∃ e h : DomainCurl.HCurl Ω,
          (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
            fun x => MaterialField.total c k u Einc x j) ∧
          (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
            fun x => totalMagnetic c k u Hinc x j) ∧
          WeakConservation.WeakMaxwell k (fun _ => 1) (dielectric c) e h := by
  obtain ⟨u, hu, hn, hM, hEu, hHu⟩ :=
    SmallVolumeMaxwell.exists_small_volume_fields c k R hR hsmall hc Einc Hinc hE hH hMax
  refine ⟨u, hu, hn, ?_⟩
  intro Ω hΩ hbΩ
  have hEΩ := fun j => memLp_bounded_of_balls _ (fun T => hEu T j) Ω hbΩ
  have hHΩ := fun j => memLp_bounded_of_balls _ (fun T => hHu T j) Ω hbΩ
  exact exists_regional_fields hΩ k (dielectric c) _ _ hEΩ hHΩ
    (fun j => coefficient_mul_memLp Ω (dielectric c) (dielectric_measurable c)
      (1+c.bound) (dielectric_norm_bound c) _ (hEΩ j)) hM

end OQ14.MaterialHCurl

#print axioms OQ14.MaterialHCurl.coefficient_mul_memLp
#print axioms OQ14.MaterialHCurl.testMaxwell_electric_curl
#print axioms OQ14.MaterialHCurl.testMaxwell_magnetic_curl
#print axioms OQ14.MaterialHCurl.exists_regional_fields
#print axioms OQ14.MaterialHCurl.memLp_bounded_of_balls
#print axioms OQ14.MaterialHCurl.dielectric_measurable
#print axioms OQ14.MaterialHCurl.dielectric_norm_bound
#print axioms OQ14.MaterialHCurl.small_volume_hcurl_exists
