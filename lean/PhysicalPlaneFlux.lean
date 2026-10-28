import RestrictedTEActualCounting

/-! Physical signed passage and absolute real Poynting bypass. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.PhysicalPlaneFlux
open MeasureTheory

variable {P : Type*} [MeasurableSpace P]

def passage (μ : Measure P) (D : Set P) (F : P → ℂ) : ℝ :=
  (∫ q in D, F q ∂μ).re / 2

def bypass (μ : Measure P) (D : Set P) (F : P → ℂ) : ℝ :=
  ∫ q in Dᶜ, |(F q).re| / 2 ∂μ

theorem passage_eq (μ : Measure P) (D : Set P) (F : P → ℂ) :
    passage μ D F = RestrictedTEPassageTransfer.passage μ D F / 2 := rfl

theorem real_flux_integrable (μ : Measure P) (F : P → ℂ) (hF : Integrable F μ) :
    Integrable (fun q => (F q).re / 2) μ := hF.re.div_const 2

theorem absolute_flux_integrable (μ : Measure P) (F : P → ℂ) (hF : Integrable F μ) :
    Integrable (fun q => |(F q).re| / 2) μ := hF.re.abs.div_const 2

theorem passage_eq_integral (μ : Measure P) (D : Set P) (F : P → ℂ) (hF : Integrable F μ) :
    passage μ D F = ∫ q in D, (F q).re / 2 ∂μ := by
  rw [passage, integral_div]
  congr 1
  simpa only [RCLike.re_eq_complex_re] using (integral_re hF.integrableOn).symm

theorem bypass_le (μ : Measure P) (D : Set P) (F : P → ℂ) (hF : Integrable F μ) :
    bypass μ D F ≤ RestrictedTEPassageTransfer.bypass μ D F / 2 := by
  unfold bypass RestrictedTEPassageTransfer.bypass
  rw [← integral_div]
  exact integral_mono (absolute_flux_integrable μ F hF).integrableOn
    (hF.norm.div_const 2).integrableOn
    (fun q => div_le_div_of_nonneg_right (Complex.abs_re_le_norm (F q)) (by norm_num))

theorem counted_of_double (μ : Measure P) (D : Set P)
    (W : Submodule ℂ (SymmetricHarmonicJets.Index →₀ ℂ))
    (T : (SymmetricHarmonicJets.Index →₀ ℂ) →ₗ[ℂ] ChannelScatteringMap.Ambient)
    (F : (SymmetricHarmonicJets.Index →₀ ℂ) → P → ℂ) (τ η δ : ℝ)
    (hF : ∀ a ∈ W, Integrable (F a) μ)
    (hc : RestrictedTEActualCounting.IsCounted W T
      (fun a => RestrictedTEPassageTransfer.passage μ D (F a))
      (fun a => RestrictedTEPassageTransfer.bypass μ D (F a)) τ (2 * η) (2 * δ)) :
    RestrictedTEActualCounting.IsCounted W T
      (fun a => passage μ D (F a)) (fun a => bypass μ D (F a)) τ η δ := by
  intro a ha
  obtain ⟨h1, h2, h3⟩ := hc a ha
  refine ⟨h1, ?_, ?_⟩
  · change η * ‖T a‖ ^ 2 ≤ passage μ D (F a)
    rw [passage_eq]
    linarith
  · have hb := bypass_le μ D (F a) (hF a ha)
    linarith

end OQ14.PhysicalPlaneFlux

#print axioms OQ14.PhysicalPlaneFlux.passage_eq
#print axioms OQ14.PhysicalPlaneFlux.real_flux_integrable
#print axioms OQ14.PhysicalPlaneFlux.absolute_flux_integrable
#print axioms OQ14.PhysicalPlaneFlux.passage_eq_integral
#print axioms OQ14.PhysicalPlaneFlux.bypass_le
#print axioms OQ14.PhysicalPlaneFlux.counted_of_double
