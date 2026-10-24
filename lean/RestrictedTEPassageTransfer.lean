import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

/-! Elementary transfer of a whole-plane L1 flux error to passage and absolute-bypass thresholds.

Formal objects.  For a normal flux density `F : P → ℂ` on a measure space `P` (the observation plane) and a
section `D ⊆ P`, the passage is the real part of the signed section integral and the absolute bypass is the L1
mass outside the section:
`passage D F = (∫ q in D, F q).re` and `bypass D F = ∫ q in Dᶜ, ‖F q‖`.
The theorems below are pure integral inequalities; every threshold hypothesis is explicit. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.RestrictedTEPassageTransfer
open MeasureTheory

variable {P : Type*} [MeasurableSpace P] {μ : Measure P}

/-- Passage of a flux density through the section `D`. -/
def passage (μ : Measure P) (D : Set P) (F : P → ℂ) : ℝ := (∫ q in D, F q ∂μ).re

/-- Absolute bypass of a flux density outside the section `D`. -/
def bypass (μ : Measure P) (D : Set P) (F : P → ℂ) : ℝ := ∫ q in Dᶜ, ‖F q‖ ∂μ

theorem abs_passage_sub_le (D : Set P) (f g : P → ℂ) (hf : Integrable f μ) (hg : Integrable g μ) :
    |passage μ D f-passage μ D g|≤∫ q, ‖f q-g q‖ ∂μ := by
  have hsub : passage μ D f-passage μ D g=(∫ q in D, (f q-g q) ∂μ).re := by
    unfold passage
    rw [integral_sub hf.integrableOn hg.integrableOn,Complex.sub_re]
  rw [hsub]
  calc |(∫ q in D, (f q-g q) ∂μ).re|≤‖∫ q in D, (f q-g q) ∂μ‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ q in D, ‖f q-g q‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ q, ‖f q-g q‖ ∂μ :=
      setIntegral_le_integral (hf.sub hg).norm (Filter.Eventually.of_forall (fun q => norm_nonneg _))

theorem abs_bypass_sub_le (D : Set P) (f g : P → ℂ) (hf : Integrable f μ) (hg : Integrable g μ) :
    |bypass μ D f-bypass μ D g|≤∫ q, ‖f q-g q‖ ∂μ := by
  have hsub : bypass μ D f-bypass μ D g=∫ q in Dᶜ, (‖f q‖-‖g q‖) ∂μ := by
    unfold bypass
    rw [integral_sub hf.norm.integrableOn hg.norm.integrableOn]
  rw [hsub]
  calc |∫ q in Dᶜ, (‖f q‖-‖g q‖) ∂μ|=‖∫ q in Dᶜ, (‖f q‖-‖g q‖) ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ q in Dᶜ, ‖‖f q‖-‖g q‖‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ q in Dᶜ, ‖f q-g q‖ ∂μ := by
      apply integral_mono ((hf.norm.sub hg.norm).norm.integrableOn) (hf.sub hg).norm.integrableOn
      intro q
      simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (f q) (g q)
    _ ≤ ∫ q, ‖f q-g q‖ ∂μ :=
      setIntegral_le_integral (hf.sub hg).norm (Filter.Eventually.of_forall (fun q => norm_nonneg _))

section Transfer
variable {V : Type*}

/-- One-sided transfer: a uniform whole-plane L1 error `ε*n2 x` between an actual flux family `f` and a model
family `g` degrades a model passage lower bound `p0*n2 x` and a model bypass upper bound `p1*n2 x` by at most `ε`
(in units of `n2 x`). -/
theorem passage_bypass_transfer (n2 : V → ℝ) (D : Set P) (f g : V → P → ℂ)
    (hf : ∀ x, Integrable (f x) μ) (hg : ∀ x, Integrable (g x) μ) (p0 p1 ε : ℝ)
    (herr : ∀ x, (∫ q, ‖f x q-g x q‖ ∂μ)≤ε*n2 x)
    (hpass : ∀ x, p0*n2 x≤passage μ D (g x)) (hbyp : ∀ x, bypass μ D (g x)≤p1*n2 x) :
    ∀ x, (p0-ε)*n2 x≤passage μ D (f x) ∧ bypass μ D (f x)≤(p1+ε)*n2 x := by
  intro x
  have h1 := abs_passage_sub_le D (f x) (g x) (hf x) (hg x)
  have h2 := abs_bypass_sub_le D (f x) (g x) (hf x) (hg x)
  have h3 := herr x
  have h4 := hpass x
  have h5 := hbyp x
  constructor
  · have := (abs_le.mp (h1.trans h3)).1
    nlinarith
  · have := (abs_le.mp (h2.trans h3)).2
    nlinarith

/-- Two-sided transfer: if the model passage and the model bypass are both within `ε₁*n2 x` of `p0*n2 x`
and the L1 error is at most `ε*n2 x`, then the actual passage and the actual bypass are both within
`(ε₁+ε)*n2 x` of `p0*n2 x`. -/
theorem passage_bypass_two_sided (n2 : V → ℝ) (D : Set P) (f g : V → P → ℂ)
    (hf : ∀ x, Integrable (f x) μ) (hg : ∀ x, Integrable (g x) μ) (p0 ε₁ ε : ℝ)
    (herr : ∀ x, (∫ q, ‖f x q-g x q‖ ∂μ)≤ε*n2 x)
    (hpass : ∀ x, |passage μ D (g x)-p0*n2 x|≤ε₁*n2 x)
    (hbyp : ∀ x, |bypass μ D (g x)-p0*n2 x|≤ε₁*n2 x) :
    ∀ x, |passage μ D (f x)-p0*n2 x|≤(ε₁+ε)*n2 x ∧ |bypass μ D (f x)-p0*n2 x|≤(ε₁+ε)*n2 x := by
  intro x
  have h1 := abs_passage_sub_le D (f x) (g x) (hf x) (hg x)
  have h2 := abs_bypass_sub_le D (f x) (g x) (hf x) (hg x)
  have h3 := herr x
  constructor
  · calc |passage μ D (f x)-p0*n2 x|
        =|(passage μ D (f x)-passage μ D (g x))+(passage μ D (g x)-p0*n2 x)| := by ring_nf
      _ ≤ |passage μ D (f x)-passage μ D (g x)|+|passage μ D (g x)-p0*n2 x| := abs_add _ _
      _ ≤ (ε₁+ε)*n2 x := by nlinarith [hpass x]
  · calc |bypass μ D (f x)-p0*n2 x|
        =|(bypass μ D (f x)-bypass μ D (g x))+(bypass μ D (g x)-p0*n2 x)| := by ring_nf
      _ ≤ |bypass μ D (f x)-bypass μ D (g x)|+|bypass μ D (g x)-p0*n2 x| := abs_add _ _
      _ ≤ (ε₁+ε)*n2 x := by nlinarith [hbyp x]

/-- Counting inequalities with explicit strict margins: if the model passage and bypass are both within
`ε₁*n2 x` of `p0*n2 x`, the L1 error is at most `ε*n2 x`, and `η+ε₁+ε ≤ p0` and `p0+ε₁+ε ≤ δ`
(with `n2 x ≥ 0`), then the actual passage is at least `η*n2 x` and the actual bypass is at most `δ*n2 x`. -/
theorem counting_inequalities (n2 : V → ℝ) (hn : ∀ x, 0≤n2 x) (D : Set P) (f g : V → P → ℂ)
    (hf : ∀ x, Integrable (f x) μ) (hg : ∀ x, Integrable (g x) μ) (p0 ε₁ ε η δ : ℝ)
    (herr : ∀ x, (∫ q, ‖f x q-g x q‖ ∂μ)≤ε*n2 x)
    (hpass : ∀ x, |passage μ D (g x)-p0*n2 x|≤ε₁*n2 x)
    (hbyp : ∀ x, |bypass μ D (g x)-p0*n2 x|≤ε₁*n2 x)
    (hη : η+ε₁+ε≤p0) (hδ : p0+ε₁+ε≤δ) :
    ∀ x, η*n2 x≤passage μ D (f x) ∧ bypass μ D (f x)≤δ*n2 x := by
  intro x
  obtain ⟨h1,h2⟩ := passage_bypass_two_sided n2 D f g hf hg p0 ε₁ ε herr hpass hbyp x
  have h1' := (abs_le.mp h1).1
  have h2' := (abs_le.mp h2).2
  have hx := hn x
  constructor
  · nlinarith
  · nlinarith

end Transfer

end OQ14.RestrictedTEPassageTransfer
#print axioms OQ14.RestrictedTEPassageTransfer.abs_passage_sub_le
#print axioms OQ14.RestrictedTEPassageTransfer.abs_bypass_sub_le
#print axioms OQ14.RestrictedTEPassageTransfer.passage_bypass_transfer
#print axioms OQ14.RestrictedTEPassageTransfer.passage_bypass_two_sided
#print axioms OQ14.RestrictedTEPassageTransfer.counting_inequalities
