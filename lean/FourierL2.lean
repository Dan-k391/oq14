import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.NormedSpace.OperatorNorm.Completeness
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Euclidean Fourier L2 foundations

This file develops Parseval directly from the actual Fourier integral and
Schwartz inversion. Density follows from the annihilator theorem for compact
smooth tests. The norm-preserving extension is then proved onto, giving the
actual scalar Plancherel equivalence, with agreement on Schwartz functions.
The convention is mathlib's exp(-2*pi*i*inner x xi) Fourier kernel.
No Plancherel equivalence or density statement is supplied as an assumption.
Vector lifting and the Newton-kernel identification are separate steps.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.FourierL2

open MeasureTheory SchwartzMap
open scoped FourierTransform SchwartzMap InnerProductSpace ComplexConjugate ContDiff

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev ScalarL2 := Lp ℂ 2 (volume : Measure Space)

theorem fourier_conj (f : Space → ℂ) (ξ : Space) :
    𝓕 (fun x => conj (f x)) ξ = conj (𝓕 f (-ξ)) := by
  rw [Real.fourierIntegral_eq', Real.fourierIntegral_eq', ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_right, smul_eq_mul, map_mul, ← Complex.exp_conj,
    Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem fourier_mul_integral_flip (f g : Space → ℂ)
    (hf : Integrable f) (hg : Integrable g) :
    (∫ ξ, (𝓕 f ξ) * g ξ) = ∫ x, f x * (𝓕 g x) := by
  have he : (innerₗ Space).flip = innerₗ Space := by
    ext x y
    exact real_inner_comm x y
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ Space)
    (μ := volume) (ν := volume)
    Real.continuous_fourierChar (by exact continuous_inner) hf hg
  simpa only [Real.fourierIntegral, he, smul_eq_mul] using h

theorem fourier_conj_fourier (f : 𝓢(Space, ℂ)) (x : Space) :
    𝓕 (fun ξ => conj (𝓕 f ξ)) x = conj (f x) := by
  rw [fourier_conj, ← Real.fourierIntegralInv_eq_fourierIntegral_neg]
  rw [Continuous.fourier_inversion f.continuous f.integrable
    (SchwartzMap.fourierTransformCLM ℂ f).integrable]

theorem schwartz_parseval_integral (f g : 𝓢(Space, ℂ)) :
    (∫ ξ, conj (𝓕 f ξ) * 𝓕 g ξ) = ∫ x, conj (f x) * g x := by
  have h := fourier_mul_integral_flip g (fun ξ => conj (𝓕 f ξ))
    g.integrable (Complex.conjCLE.toContinuousLinearMap.integrable_comp
      (SchwartzMap.fourierTransformCLM ℂ f).integrable)
  simpa only [fourier_conj_fourier, mul_comm] using h

def embed : 𝓢(Space, ℂ) →L[ℂ] ScalarL2 :=
  SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure Space)

theorem embed_ae (f : 𝓢(Space, ℂ)) : embed f =ᵐ[volume] f :=
  f.coeFn_toLp 2 volume

theorem embed_inner (f g : 𝓢(Space, ℂ)) :
    ⟪embed f, embed g⟫_ℂ = ∫ x, conj (f x) * g x := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [embed_ae f, embed_ae g] with x hf hg
  rw [hf, hg]
  simp [mul_comm]

theorem schwartz_parseval_inner (f g : 𝓢(Space, ℂ)) :
    ⟪embed (SchwartzMap.fourierTransformCLE ℂ f),
      embed (SchwartzMap.fourierTransformCLE ℂ g)⟫_ℂ =
        ⟪embed f, embed g⟫_ℂ := by
  rw [embed_inner, embed_inner]
  exact schwartz_parseval_integral f g

theorem schwartz_parseval_norm (f : 𝓢(Space, ℂ)) :
    ‖embed (SchwartzMap.fourierTransformCLE ℂ f)‖ = ‖embed f‖ := by
  have h := congrArg Complex.re (schwartz_parseval_inner f f)
  have hs (x : ScalarL2) : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  rw [hs, hs] at h
  nlinarith [norm_nonneg (embed (SchwartzMap.fourierTransformCLE ℂ f)),
    norm_nonneg (embed f)]

/-- Every actual compactly supported smooth function is a Schwartz function. -/
def compactSmoothSchwartz (f : Space → ℂ) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) : 𝓢(Space, ℂ) where
  toFun := f
  smooth' := hf
  decay' := by
    intro k n
    have hd : Continuous (iteratedFDeriv ℝ n f) :=
      hf.continuous_iteratedFDeriv (mod_cast le_top)
    have hs : HasCompactSupport (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖) :=
      (hc.iteratedFDeriv n).norm.mul_left
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous
      ((continuous_norm.pow k).mul hd.norm)
    refine ⟨C, fun x => ?_⟩
    have hnonneg : 0 ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ :=
      mul_nonneg (pow_nonneg (norm_nonneg x) k) (norm_nonneg _)
    simpa only [Real.norm_of_nonneg hnonneg] using hC x

def schwartzRange : Submodule ℂ ScalarL2 := LinearMap.range embed.toLinearMap

theorem schwartzRange_orthogonal_bot : schwartzRangeᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  rw [Submodule.mem_bot]
  apply Lp.ext
  have hz : ∀ᵐ x ∂(volume : Measure Space), f x = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp f).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    intro φ hφ hc
    let ψ : 𝓢(Space, ℂ) := compactSmoothSchwartz (fun x => (φ x : ℂ))
      (Complex.ofRealCLM.contDiff.comp hφ)
      (hc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp))
    have hm : ⟪embed ψ, f⟫_ℂ = 0 :=
      (schwartzRange.mem_orthogonal f).mp hf (embed ψ) ⟨ψ, rfl⟩
    rw [MeasureTheory.L2.inner_def] at hm
    calc
      (∫ x, φ x • f x) = ∫ x, ⟪embed ψ x, f x⟫_ℂ := by
        apply integral_congr_ae
        filter_upwards [embed_ae ψ] with x hx
        rw [hx]
        change φ x • f x = ⟪(φ x : ℂ), f x⟫_ℂ
        simp [Complex.real_smul, mul_comm]
      _ = 0 := hm
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 (volume : Measure Space)] with x hx hzero
  exact hx.trans hzero.symm

theorem embed_denseRange : DenseRange embed := by
  have ht := (Submodule.topologicalClosure_eq_top_iff (K := schwartzRange)).mpr
    schwartzRange_orthogonal_bot
  have hc := congrArg (fun U : Submodule ℂ ScalarL2 => (U : Set ScalarL2)) ht
  dsimp only at hc
  rw [Submodule.topologicalClosure_coe, Submodule.top_coe] at hc
  rw [denseRange_iff_closure_range]
  exact hc

/-- The Schwartz space, now viewed with its actual L2 range norm. -/
def rangeEquiv : 𝓢(Space, ℂ) ≃ₗ[ℂ] schwartzRange :=
  LinearEquiv.ofInjective embed.toLinearMap
    (SchwartzMap.injective_toLp 2 (volume : Measure Space))

theorem embed_rangeEquiv_symm (v : schwartzRange) :
    embed (rangeEquiv.symm v) = (v : ScalarL2) :=
  LinearEquiv.ofInjective_symm_apply embed.toLinearMap v

def rangeFourierLinear : schwartzRange →ₗ[ℂ] ScalarL2 :=
  embed.toLinearMap.comp
    ((SchwartzMap.fourierTransformCLE ℂ).toLinearMap.comp rangeEquiv.symm.toLinearMap)

theorem rangeFourier_norm (v : schwartzRange) : ‖rangeFourierLinear v‖ = ‖v‖ := by
  change ‖embed (SchwartzMap.fourierTransformCLE ℂ (rangeEquiv.symm v))‖ = ‖v‖
  rw [schwartz_parseval_norm, embed_rangeEquiv_symm]
  rfl

def rangeFourier : schwartzRange →L[ℂ] ScalarL2 :=
  rangeFourierLinear.mkContinuous 1 (fun v => by simp [rangeFourier_norm])

theorem range_inclusion_dense : DenseRange schwartzRange.subtypeL := by
  apply embed_denseRange.mono
  rintro x ⟨f, rfl⟩
  exact ⟨rangeEquiv f, rfl⟩

/-- Fourier transform extended from its actual integral on the dense Schwartz range. -/
def transform : ScalarL2 →L[ℂ] ScalarL2 :=
  rangeFourier.extend schwartzRange.subtypeL range_inclusion_dense
    isometry_subtype_coe.isUniformInducing

theorem transform_range (v : schwartzRange) :
    transform (v : ScalarL2) = rangeFourier v :=
  ContinuousLinearMap.extend_eq _ _ _ _ v

theorem transform_embed (f : 𝓢(Space, ℂ)) :
    transform (embed f) = embed (SchwartzMap.fourierTransformCLE ℂ f) := by
  have h := transform_range (rangeEquiv f)
  simpa only [rangeEquiv, LinearEquiv.ofInjective_apply, rangeFourier,
    LinearMap.mkContinuous_apply, rangeFourierLinear, LinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using h

theorem transform_norm (f : ScalarL2) : ‖transform f‖ = ‖f‖ := by
  refine range_inclusion_dense.induction_on f
    (isClosed_eq transform.continuous.norm continuous_norm) ?_
  intro v
  change ‖transform (v : ScalarL2)‖ = ‖(v : ScalarL2)‖
  rw [transform_range]
  exact rangeFourier_norm v

def transformIsometry : ScalarL2 →ₗᵢ[ℂ] ScalarL2 where
  toLinearMap := transform.toLinearMap
  norm_map' := transform_norm

theorem transform_surjective : Function.Surjective transformIsometry := by
  have hd : DenseRange transformIsometry := by
    apply embed_denseRange.mono
    rintro x ⟨f, rfl⟩
    refine ⟨embed ((SchwartzMap.fourierTransformCLE ℂ).symm f), ?_⟩
    change transform (embed ((SchwartzMap.fourierTransformCLE ℂ).symm f)) = embed f
    rw [transform_embed, ContinuousLinearEquiv.apply_symm_apply]
  have hc : IsClosed (Set.range transformIsometry) :=
    transformIsometry.isometry.antilipschitz.isClosed_range
      transformIsometry.isometry.uniformContinuous
  intro f
  have hf := hd f
  rw [hc.closure_eq] at hf
  exact hf

/-- The actual Plancherel equivalence on complex L2 of Euclidean three-space. -/
def fourierEquiv : ScalarL2 ≃ₗᵢ[ℂ] ScalarL2 :=
  LinearIsometryEquiv.ofSurjective transformIsometry transform_surjective

theorem fourierEquiv_embed (f : 𝓢(Space, ℂ)) :
    fourierEquiv (embed f) = embed (SchwartzMap.fourierTransformCLE ℂ f) :=
  transform_embed f

theorem fourierEquiv_symm_embed (f : 𝓢(Space, ℂ)) :
    fourierEquiv.symm (embed f) = embed ((SchwartzMap.fourierTransformCLE ℂ).symm f) := by
  apply fourierEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply, fourierEquiv_embed,
    ContinuousLinearEquiv.apply_symm_apply]

theorem fourierEquiv_ae_integral (f : 𝓢(Space, ℂ)) :
    fourierEquiv (embed f) =ᵐ[volume] fun ξ => 𝓕 f ξ := by
  rw [fourierEquiv_embed]
  exact embed_ae (SchwartzMap.fourierTransformCLE ℂ f)

theorem fourierEquiv_inner (f g : ScalarL2) :
    ⟪fourierEquiv f, fourierEquiv g⟫_ℂ = ⟪f, g⟫_ℂ :=
  fourierEquiv.inner_map_map f g

theorem fourierEquiv_norm (f : ScalarL2) : ‖fourierEquiv f‖ = ‖f‖ :=
  fourierEquiv.norm_map f

theorem fourierEquiv_unique (U : ScalarL2 →L[ℂ] ScalarL2)
    (hU : ∀ f : 𝓢(Space, ℂ), U (embed f) = embed (SchwartzMap.fourierTransformCLE ℂ f)) :
    U = fourierEquiv.toContinuousLinearEquiv.toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  change U f = fourierEquiv f
  refine embed_denseRange.induction_on f
    (isClosed_eq U.continuous fourierEquiv.continuous) ?_
  intro g
  rw [hU, fourierEquiv_embed]

end OQ14.FourierL2

#print axioms OQ14.FourierL2.fourier_conj
#print axioms OQ14.FourierL2.fourier_mul_integral_flip
#print axioms OQ14.FourierL2.fourier_conj_fourier
#print axioms OQ14.FourierL2.schwartz_parseval_integral
#print axioms OQ14.FourierL2.embed_ae
#print axioms OQ14.FourierL2.embed_inner
#print axioms OQ14.FourierL2.schwartz_parseval_inner
#print axioms OQ14.FourierL2.schwartz_parseval_norm
#print axioms OQ14.FourierL2.schwartzRange_orthogonal_bot
#print axioms OQ14.FourierL2.embed_denseRange
#print axioms OQ14.FourierL2.embed_rangeEquiv_symm
#print axioms OQ14.FourierL2.rangeFourier_norm
#print axioms OQ14.FourierL2.range_inclusion_dense
#print axioms OQ14.FourierL2.transform_range
#print axioms OQ14.FourierL2.transform_embed
#print axioms OQ14.FourierL2.transform_norm
#print axioms OQ14.FourierL2.transform_surjective
#print axioms OQ14.FourierL2.fourierEquiv_embed
#print axioms OQ14.FourierL2.fourierEquiv_symm_embed
#print axioms OQ14.FourierL2.fourierEquiv_ae_integral
#print axioms OQ14.FourierL2.fourierEquiv_inner
#print axioms OQ14.FourierL2.fourierEquiv_norm
#print axioms OQ14.FourierL2.fourierEquiv_unique
