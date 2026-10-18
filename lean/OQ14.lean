import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Stable operator core for the OQ14 research manuscript

This file does not formalize a Maxwell equation, a dielectric realization,
or the unresolved uniform approximation theorem. All physical-bridge
hypotheses remain visibly outside these theorems.
-/

noncomputable section
set_option autoImplicit false

namespace OQ14

section Approximation

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Strict approximation below a lower transmission threshold excludes a
nonzero vector from the approximating operator's kernel. -/
theorem approximation_kernel_trivial
    (U R : E →L[𝕜] F) (α : ℝ)
    (hU : ∀ x, α * ‖x‖ ≤ ‖U x‖) (hgap : ‖U - R‖ < α)
    (x : E) (hx : R x = 0) : x = 0 := by
  by_contra hne
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hne
  have hbound := (U - R).le_opNorm x
  simp only [ContinuousLinearMap.sub_apply, hx, sub_zero] at hbound
  have hstrict := mul_lt_mul_of_pos_right hgap hpos
  exact (not_lt_of_ge ((hU x).trans hbound)) hstrict

/-- The approximation is injective; this statement needs no compactness. -/
theorem approximation_injective
    (U R : E →L[𝕜] F) (α : ℝ)
    (hU : ∀ x, α * ‖x‖ ≤ ‖U x‖) (hgap : ‖U - R‖ < α) :
    Function.Injective R := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply approximation_kernel_trivial U R α hU hgap
  simp only [map_sub, hxy, sub_self]

/-- With finite-dimensional range, the approximation criterion really
forces the domain to be finite-dimensional, not merely finrank zero. -/
theorem finiteDimensional_of_approximation
    (U R : E →L[𝕜] F) (α : ℝ)
    (hU : ∀ x, α * ‖x‖ ≤ ‖U x‖) (hgap : ‖U - R‖ < α)
    [FiniteDimensional 𝕜 (LinearMap.range R.toLinearMap)] :
    FiniteDimensional 𝕜 E := by
  let e : E ≃ₗ[𝕜] LinearMap.range R.toLinearMap :=
    LinearEquiv.ofInjective R.toLinearMap
      (approximation_injective U R α hU hgap)
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- The manuscript's finite-rank dimension conclusion, with every
approximation hypothesis explicit. -/
theorem finite_rank_channel_bound
    (U R : E →L[𝕜] F) (α : ℝ) (M : ℕ)
    (hU : ∀ x, α * ‖x‖ ≤ ‖U x‖) (hgap : ‖U - R‖ < α)
    [FiniteDimensional 𝕜 (LinearMap.range R.toLinearMap)]
    (hrank : Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ M) :
    Module.finrank 𝕜 E ≤ M := by
  have heq := LinearMap.finrank_range_of_inj
    (f := R.toLinearMap) (approximation_injective U R α hU hgap)
  exact heq ▸ hrank

/-- Power-normalized form of the finite-rank theorem: a strict error below
sqrt(tau) and a rank-M approximation force genuine finite dimension at most M. -/
theorem finite_rank_power_channel_bound
    (U R : E →L[𝕜] F) (τ : ℝ) (M : ℕ) (hτ : 0 ≤ τ)
    (hpower : ∀ x, τ * ‖x‖ ^ 2 ≤ ‖U x‖ ^ 2)
    (hgap : ‖U - R‖ < Real.sqrt τ)
    [FiniteDimensional 𝕜 (LinearMap.range R.toLinearMap)]
    (hrank : Module.finrank 𝕜 (LinearMap.range R.toLinearMap) ≤ M) :
    FiniteDimensional 𝕜 E ∧ Module.finrank 𝕜 E ≤ M := by
  have hlower : ∀ x, Real.sqrt τ * ‖x‖ ≤ ‖U x‖ := by
    intro x
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg τ) (norm_nonneg x))
      (norm_nonneg (U x))).mp
    simpa only [mul_pow, Real.sq_sqrt hτ] using hpower x
  exact ⟨finiteDimensional_of_approximation U R (Real.sqrt τ) hlower hgap,
    finite_rank_channel_bound U R (Real.sqrt τ) M hlower hgap hrank⟩

end Approximation

section Perturbation

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- An operator within e of a linear isometry has a uniform lower bound
on every coherent input, not only on chosen basis vectors. -/
theorem isometry_perturbation_lower_bound
    (T : E →L[𝕜] F) (U : E →ₗᵢ[𝕜] F) (e : ℝ)
    (herror : ‖U.toContinuousLinearMap - T‖ ≤ e) (x : E) :
    (1 - e) * ‖x‖ ≤ ‖T x‖ := by
  have hnorm := norm_sub_norm_le (U x) (T x)
  rw [U.norm_map] at hnorm
  have hbound := (U.toContinuousLinearMap - T).le_opNorm x
  have hbound' : ‖U x - T x‖ ≤ e * ‖x‖ := by
    exact hbound.trans (mul_le_mul_of_nonneg_right herror (norm_nonneg x))
  nlinarith

/-- The strict square-root margin certifies the power threshold. -/
theorem isometry_perturbation_power_threshold
    (T : E →L[𝕜] F) (U : E →ₗᵢ[𝕜] F) (e τ : ℝ)
    (hτ : 0 ≤ τ) (herror : ‖U.toContinuousLinearMap - T‖ ≤ e)
    (hmargin : e < 1 - Real.sqrt τ) (x : E) (hx : x ≠ 0) :
    τ * ‖x‖ ^ 2 < ‖T x‖ ^ 2 := by
  have hlower := isometry_perturbation_lower_bound T U e herror x
  have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hsqrt := Real.sqrt_nonneg τ
  have hsquare := Real.sq_sqrt hτ
  have hstrict : Real.sqrt τ * ‖x‖ < ‖T x‖ := by
    nlinarith
  have hnonneg : 0 ≤ Real.sqrt τ * ‖x‖ := mul_nonneg hsqrt (norm_nonneg x)
  have hpowers := (sq_lt_sq₀ hnonneg (norm_nonneg (T x))).2 hstrict
  simpa only [mul_pow, hsquare] using hpowers

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A contractive output compression cannot conceal the certified
power lower bound of a near-isometric compressed operator. -/
theorem compression_power_threshold
    (T : E →L[𝕜] F) (C : F →L[𝕜] G) (U : E →ₗᵢ[𝕜] G)
    (e τ : ℝ) (hτ : 0 ≤ τ) (hC : ‖C‖ ≤ 1)
    (herror : ‖U.toContinuousLinearMap - C.comp T‖ ≤ e)
    (hmargin : e < 1 - Real.sqrt τ) (x : E) (hx : x ≠ 0) :
    τ * ‖x‖ ^ 2 < ‖T x‖ ^ 2 := by
  have hcompressed := isometry_perturbation_power_threshold
    (C.comp T) U e τ hτ herror hmargin x hx
  have hcontract : ‖C (T x)‖ ≤ ‖T x‖ := by
    calc
      ‖C (T x)‖ ≤ ‖C‖ * ‖T x‖ := C.le_opNorm (T x)
      _ ≤ 1 * ‖T x‖ := mul_le_mul_of_nonneg_right hC (norm_nonneg _)
      _ = ‖T x‖ := one_mul _
  simp only [ContinuousLinearMap.comp_apply] at hcompressed
  nlinarith [norm_nonneg (C (T x)), norm_nonneg (T x)]

end Perturbation

section Bypass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
open scoped InnerProductSpace

/-- Pointwise Cauchy--Schwarz/operator-norm control of a real quadratic
flux form. Hermitian symmetry is not needed for this inequality. -/
theorem quadratic_flux_norm_bound (A : E →L[ℂ] E) (x : E) :
    |(⟪x, A x⟫_ℂ).re| ≤ ‖A‖ * ‖x‖ ^ 2 := by
  calc
    |(⟪x, A x⟫_ℂ).re| ≤ ‖⟪x, A x⟫_ℂ‖ := Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖A x‖ := norm_inner_le_norm x (A x)
    _ ≤ ‖x‖ * (‖A‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
    _ = ‖A‖ * ‖x‖ ^ 2 := by ring

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- The continuum absolute-bypass integration certificate, for every
coherent vector, with integrability assumptions stated explicitly.
No Maxwell-to-flux representation is assumed as an axiom. -/
theorem absolute_bypass_certificate
    (A : Ω → E →L[ℂ] E) (δ : ℝ)
    (hnorm : Integrable (fun s => ‖A s‖) μ)
    (hflux : ∀ x : E, Integrable (fun s => (⟪x, A s x⟫_ℂ).re) μ)
    (hbudget : (∫ s, ‖A s‖ ∂μ) ≤ δ) (x : E) :
    (∫ s, |(⟪x, A s x⟫_ℂ).re| ∂μ) ≤ δ * ‖x‖ ^ 2 := by
  calc
    (∫ s, |(⟪x, A s x⟫_ℂ).re| ∂μ) ≤
        ∫ s, ‖A s‖ * ‖x‖ ^ 2 ∂μ :=
      integral_mono (hflux x).abs (hnorm.mul_const _)
        (fun s => quadratic_flux_norm_bound (A s) x)
    _ = (∫ s, ‖A s‖ ∂μ) * ‖x‖ ^ 2 := integral_mul_const _ _
    _ ≤ δ * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right hbudget (sq_nonneg _)

end Bypass

end OQ14

#print axioms OQ14.approximation_kernel_trivial
#print axioms OQ14.approximation_injective
#print axioms OQ14.finiteDimensional_of_approximation
#print axioms OQ14.finite_rank_channel_bound
#print axioms OQ14.finite_rank_power_channel_bound
#print axioms OQ14.isometry_perturbation_lower_bound
#print axioms OQ14.isometry_perturbation_power_threshold
#print axioms OQ14.compression_power_threshold
#print axioms OQ14.quadratic_flux_norm_bound
#print axioms OQ14.absolute_bypass_certificate
