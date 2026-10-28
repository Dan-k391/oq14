import WeakPoynting.Translations
import MaxwellInverseCurlCurl

/-! Uniform L² difference-quotient bounds from actual local Maxwell H¹ fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaxwellDifferenceQuotient
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.DivCurlCompact OQ14.WeakTranslations

def quotient (u : L2Scalar) (i : Fin 3) (h : ℝ) : L2Scalar :=
  ((h : ℂ)⁻¹) • (translateL2 u (h • basis i) - u)

theorem quotient_bound {u : L2Scalar} (hu : CompactRepresentative u)
    {D : Fin 3 → L2Scalar} (hD : ∀ i, HasWeakPartial u (D i) i)
    (i : Fin 3) (h : ℝ) (hh : h ≠ 0) :
    ‖quotient u i h‖ ≤ ∑ j, ‖D j‖ := by
  have ht := weak_translation_bound hu hD (h • basis i)
  have hb : ‖basis i‖ = 1 := by simp [basis]
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  simp only [norm_smul, Real.norm_eq_abs, hb, mul_one] at ht
  unfold quotient
  rw [norm_smul, norm_inv, Complex.norm_real]
  apply (inv_mul_le_iff₀ hn).2
  simpa only [mul_comm, Real.norm_eq_abs] using ht

theorem maxwell_cutoff_quotients {Ω : Set Space} (hΩ : IsOpen Ω)
    (χ : DomainCurl.Test Ω) (hχ : ContDiff ℝ 2 χ.function)
    (k : ℝ) (hk : k ≠ 0) (ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) ε E H) :
    ∃ (F : L2Vector) (G : DivCurlRegularity.DerivativeIndex → L2Scalar),
      (∀ j, CompactRepresentative (F j)) ∧
      (∀ q, HasWeakPartial (F q.2) (G q) q.1) ∧
      (∀ j, (fun x => F j x) =ᵐ[DomainCurl.regionMeasure Ω]
        (fun x => χ.function x * H.val.1 j x)) ∧
      ∀ i j (h : ℝ), h ≠ 0 → ‖quotient (F j) i h‖ ≤ ∑ l, ‖G (l,j)‖ := by
  let F : L2Vector := CurlCutoff.extendVector Ω hΩ.measurableSet
    (CurlCutoff.multiply Ω χ.toTest H.val.1)
  obtain ⟨G,hG,_⟩ := LocalRegularity.maxwell_cutoff_magnetic_regularity hΩ χ hχ k hk ε E H hM
  have hcompact : ∀ j, CompactRepresentative (F j) :=
    LocalRegularity.cutoff_extend_compact hΩ χ H.val.1
  refine ⟨F,G,hcompact,hG,?_,?_⟩
  · intro j
    exact LocalPower.cutExtend_field_ae hΩ χ H j
  · intro i j h hh
    exact quotient_bound (hcompact j) (fun l => hG (l,j)) i h hh

end OQ14.MaxwellDifferenceQuotient
#print axioms OQ14.MaxwellDifferenceQuotient.quotient_bound
#print axioms OQ14.MaxwellDifferenceQuotient.maxwell_cutoff_quotients
