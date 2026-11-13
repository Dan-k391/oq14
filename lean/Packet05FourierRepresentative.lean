import NewtonL1L2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! A genuinely continuous representative follows from an integrable inverse
L² Fourier transform.  This is an embedding step, not an assertion that an
interface field already has that integrability. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05FourierRepresentative
open MeasureTheory
open scoped FourierTransform

theorem continuous_of_integrable_inverse_fourier (u : FourierL2.ScalarL2)
    (h : Integrable ((FourierL2.fourierEquiv.symm u) : FourierL2.Space → ℂ)) :
    ∃ f : FourierL2.Space → ℂ, Continuous f ∧ (u : FourierL2.Space → ℂ) =ᵐ[volume] f := by
  let v := FourierL2.fourierEquiv.symm u
  refine ⟨𝓕 (v : FourierL2.Space → ℂ), NewtonL1L2.ordinary_fourier_continuous h, ?_⟩
  have he := NewtonL1L2.fourierEquiv_ae_integral v h
  simpa [v] using he

/-- The three-dimensional H² Fourier weight gives L¹, hence an actual
continuous representative.  The weight hypothesis is stated explicitly. -/
theorem continuous_of_weighted_inverse_fourier (u : FourierL2.ScalarL2)
    (hweight : MemLp (fun x : FourierL2.Space =>
      (((1 + ‖x‖^2 : ℝ) : ℂ) * (FourierL2.fourierEquiv.symm u) x)) 2 volume) :
    ∃ f : FourierL2.Space → ℂ, Continuous f ∧ (u : FourierL2.Space → ℂ) =ᵐ[volume] f := by
  let v := FourierL2.fourierEquiv.symm u
  have hinv : Integrable (fun x : FourierL2.Space => (1 + ‖x‖^2) ^ (-(4 : ℝ)/2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    norm_num [FourierL2.Space]
  let q : FourierL2.Space → ℂ := fun x => (((1 + ‖x‖^2 : ℝ)⁻¹ : ℝ) : ℂ)
  have hqcont : Continuous q := by
    apply Complex.continuous_ofReal.comp
    apply Continuous.inv₀
    · fun_prop
    · intro x
      positivity
  have hq : MemLp q 2 volume := by
    apply (memLp_two_iff_integrable_sq_norm hqcont.aestronglyMeasurable).mpr
    convert hinv using 1
    ext x
    have hp : 0 ≤ (1 + ‖x‖^2 : ℝ) := by positivity
    simp only [q, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_nonneg hp,
      show (-(4 : ℝ)/2) = -(2 : ℝ) by norm_num, Real.rpow_neg hp,
      Real.rpow_natCast, inv_pow]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
  have hp := hq.integrable_mul hweight
  apply continuous_of_integrable_inverse_fourier u
  change Integrable (v : FourierL2.Space → ℂ)
  apply hp.congr
  filter_upwards with x
  change q x * (((1 + ‖x‖^2 : ℝ) : ℂ) * v x) = v x
  have hn : ((1 + ‖x‖^2 : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  simp only [q, Complex.ofReal_inv]
  push_cast at hn
  field_simp [hn]

end OQ14.Packet05FourierRepresentative
#print axioms OQ14.Packet05FourierRepresentative.continuous_of_integrable_inverse_fourier
#print axioms OQ14.Packet05FourierRepresentative.continuous_of_weighted_inverse_fourier
