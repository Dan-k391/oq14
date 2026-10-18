import VectorFourier
import Maxwell

/-!
# Differential meaning of the physical longitudinal projection

Directional derivatives are the actual Frechet derivatives of Schwartz fields.
Fourier differentiation is derived from the ordinary Fourier integral theorem.
The projection statements concern these actual derivatives and L2 fields.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace OQ14.GradientProjection

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate FourierTransform SchwartzMap ContDiff

abbrev Space := FourierL2.Space
abbrev Frequency := VectorFourier.Frequency
abbrev Vector := VectorFourier.Vector
abbrev VectorL2 := VectorFourier.VectorL2

def pderivative (i : Fin 3) (f : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  SchwartzMap.pderivCLM ℂ (Maxwell.basis i) f

theorem pderivative_apply (i : Fin 3) (f : 𝓢(Space, ℂ)) (x : Space) :
    pderivative i f x = Maxwell.dcoord f x i := rfl

theorem fourier_pderivative (i : Fin 3) (f : 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (pderivative i f) ξ = (2 * Real.pi * Complex.I) * (ξ i : ℂ) * 𝓕 f ξ := by
  have hi : Integrable (fderiv ℝ (f : Space → ℂ)) :=
    (SchwartzMap.fderivCLM ℂ f).integrable
  have he : 𝓕 (pderivative i f) ξ = 𝓕 (fderiv ℝ (f : Space → ℂ)) ξ (Maxwell.basis i) :=
    (Real.fourierIntegral_continuousLinearMap_apply hi).symm
  rw [he, Real.fourierIntegral_fderiv f.integrable f.differentiable hi]
  simp only [VectorFourier.fourierSMulRight_apply, ContinuousLinearMap.neg_apply,
    innerSL_apply, Maxwell.basis, EuclideanSpace.inner_single_right, conj_trivial,
    one_mul, neg_smul, smul_neg, neg_neg, smul_eq_mul, Complex.real_smul]
  ring

def gradient (f : 𝓢(Space, ℂ)) : VectorL2 :=
  VectorFourier.schwartzVector (fun i => pderivative i f)

theorem gradient_ae (f : 𝓢(Space, ℂ)) (i : Fin 3) :
    (fun x => gradient f x i) =ᵐ[volume]
      fun x => Maxwell.gradient f (VectorFourier.coordinateMap.symm x) i :=
  VectorFourier.schwartzVector_ae (fun i => pderivative i f) i

theorem fourier_gradient (f : 𝓢(Space, ℂ)) :
    VectorFourier.fourier (gradient f) =ᵐ[volume]
      fun ξ => ((2 * Real.pi * Complex.I) * 𝓕 f (VectorFourier.coordinateMap.symm ξ)) •
        LongitudinalProjection.complexify ξ := by
  have h : ∀ᵐ ξ ∂(volume : Measure Frequency), ∀ i : Fin 3,
      VectorFourier.fourier (gradient f) ξ i =
        𝓕 (pderivative i f) (VectorFourier.coordinateMap.symm ξ) :=
    ae_all_iff.mpr (fun i => VectorFourier.fourier_ae_integral (fun i => pderivative i f) i)
  filter_upwards [h] with ξ hξ
  apply PiLp.ext
  intro i
  rw [hξ i, fourier_pderivative]
  change (2 * Real.pi * Complex.I) * (ξ i : ℂ) * 𝓕 f (VectorFourier.coordinateMap.symm ξ) =
    ((2 * Real.pi * Complex.I) * 𝓕 f (VectorFourier.coordinateMap.symm ξ)) * (ξ i : ℂ)
  ring

theorem symbol_longitudinal (ξ : Frequency) (c : ℂ) :
    LongitudinalProjection.symbol ξ (c • LongitudinalProjection.complexify ξ) =
      c • LongitudinalProjection.complexify ξ := by
  apply (Submodule.orthogonalProjection_eq_self_iff).mpr
  exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)

theorem physicalProjection_gradient (f : 𝓢(Space, ℂ)) :
    VectorFourier.physicalProjection (gradient f) = gradient f := by
  apply VectorFourier.fourier.injective
  rw [VectorFourier.physicalProjection_intertwine]
  apply Lp.ext
  filter_upwards [LongitudinalProjection.multiplier_ae (VectorFourier.fourier (gradient f)),
    fourier_gradient f] with ξ hm hg
  rw [hm, hg]
  exact symbol_longitudinal ξ _

theorem transverse_orthogonal_gradient (F : VectorL2) (f : 𝓢(Space, ℂ)) :
    ⟪F - VectorFourier.physicalProjection F, gradient f⟫_ℂ = 0 := by
  rw [inner_sub_left, VectorFourier.physicalProjection_symmetric,
    physicalProjection_gradient, sub_self]

def divergence (f : Fin 3 → 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  pderivative 0 (f 0) + pderivative 1 (f 1) + pderivative 2 (f 2)

theorem divergence_apply (f : Fin 3 → 𝓢(Space, ℂ)) (x : Space) :
    divergence f x = Maxwell.divergence (fun y i => f i y) x := rfl

theorem fourier_divergence (f : Fin 3 → 𝓢(Space, ℂ)) (ξ : Space) :
    𝓕 (divergence f) ξ = (2 * Real.pi * Complex.I) *
      (∑ i : Fin 3, (ξ i : ℂ) * 𝓕 (f i) ξ) := by
  change SchwartzMap.fourierTransformCLM ℂ (divergence f) ξ = _
  simp only [divergence, map_add, SchwartzMap.add_apply,
    SchwartzMap.fourierTransformCLM_apply, fourier_pderivative]
  simp only [Fin.sum_univ_three]
  ring

theorem fourier_divergence_zero (f : Fin 3 → 𝓢(Space, ℂ))
    (hf : divergence f = 0) (ξ : Space) :
    (∑ i : Fin 3, (ξ i : ℂ) * 𝓕 (f i) ξ) = 0 := by
  have h0 : SchwartzMap.fourierTransformCLM ℂ (divergence f) = 0 := by rw [hf, map_zero]
  have hξ := congrArg (fun g : 𝓢(Space, ℂ) => g ξ) h0
  change 𝓕 (divergence f) ξ = 0 at hξ
  rw [fourier_divergence] at hξ
  have hn : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
  exact (mul_eq_zero.mp hξ).resolve_left hn

theorem physicalProjection_divergenceFree (f : Fin 3 → 𝓢(Space, ℂ))
    (hf : divergence f = 0) :
    VectorFourier.physicalProjection (VectorFourier.schwartzVector f) = 0 := by
  apply VectorFourier.fourier.injective
  rw [VectorFourier.physicalProjection_intertwine, map_zero]
  apply Lp.ext
  have h : ∀ᵐ ξ ∂(volume : Measure Frequency), ∀ i : Fin 3,
      VectorFourier.fourier (VectorFourier.schwartzVector f) ξ i =
        𝓕 (f i) (VectorFourier.coordinateMap.symm ξ) :=
    ae_all_iff.mpr (fun i => VectorFourier.fourier_ae_integral f i)
  filter_upwards [LongitudinalProjection.multiplier_ae
    (VectorFourier.fourier (VectorFourier.schwartzVector f)), h,
    Lp.coeFn_zero Vector 2 (volume : Measure Frequency)] with ξ hm hξ hz
  rw [hm, hz]
  apply PiLp.ext
  intro i
  rw [LongitudinalProjection.symbol_coordinate]
  simp only [hξ]
  have hd := fourier_divergence_zero f hf (VectorFourier.coordinateMap.symm ξ)
  change (∑ j : Fin 3, (ξ j : ℂ) * 𝓕 (f j) (VectorFourier.coordinateMap.symm ξ)) = 0 at hd
  rw [hd, zero_div, zero_mul]
  rfl

def curl (f : Fin 3 → 𝓢(Space, ℂ)) : Fin 3 → 𝓢(Space, ℂ) :=
  ![pderivative 1 (f 2) - pderivative 2 (f 1),
    pderivative 2 (f 0) - pderivative 0 (f 2),
    pderivative 0 (f 1) - pderivative 1 (f 0)]

theorem curl_apply (f : Fin 3 → 𝓢(Space, ℂ)) (x : Space) (i : Fin 3) :
    curl f i x = Maxwell.curl (fun y j => f j y) x i := by
  fin_cases i <;> rfl

theorem divergence_curl (f : Fin 3 → 𝓢(Space, ℂ)) : divergence (curl f) = 0 := by
  apply DFunLike.ext
  intro x
  rw [divergence_apply]
  have he : (fun y i => curl f i y) = Maxwell.curl (fun y i => f i y) := by
    funext y i
    exact curl_apply f y i
  rw [he]
  exact Maxwell.divergence_curl (fun y i => f i y) (fun i => (f i).smooth 2) x

theorem physicalProjection_curl (f : Fin 3 → 𝓢(Space, ℂ)) :
    VectorFourier.physicalProjection (VectorFourier.schwartzVector (curl f)) = 0 :=
  physicalProjection_divergenceFree (curl f) (divergence_curl f)

theorem longitudinal_orthogonal_curl (F : VectorL2) (f : Fin 3 → 𝓢(Space, ℂ)) :
    ⟪VectorFourier.physicalProjection F, VectorFourier.schwartzVector (curl f)⟫_ℂ = 0 := by
  rw [VectorFourier.physicalProjection_symmetric, physicalProjection_curl, inner_zero_right]

end OQ14.GradientProjection

#print axioms OQ14.GradientProjection.pderivative_apply
#print axioms OQ14.GradientProjection.fourier_pderivative
#print axioms OQ14.GradientProjection.gradient_ae
#print axioms OQ14.GradientProjection.fourier_gradient
#print axioms OQ14.GradientProjection.symbol_longitudinal
#print axioms OQ14.GradientProjection.physicalProjection_gradient
#print axioms OQ14.GradientProjection.transverse_orthogonal_gradient
#print axioms OQ14.GradientProjection.divergence_apply
#print axioms OQ14.GradientProjection.fourier_divergence
#print axioms OQ14.GradientProjection.fourier_divergence_zero
#print axioms OQ14.GradientProjection.physicalProjection_divergenceFree
#print axioms OQ14.GradientProjection.curl_apply
#print axioms OQ14.GradientProjection.divergence_curl
#print axioms OQ14.GradientProjection.physicalProjection_curl
#print axioms OQ14.GradientProjection.longitudinal_orthogonal_curl
