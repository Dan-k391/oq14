import WeakPoynting.Energy
import GradientProjection

/-! # Genuine Schwartz div-curl energy identity

This is the analytic energy identity used to construct weak L2 derivatives
from compactly supported L2 curl and divergence. No H1 premise is used here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.DivCurl

open MeasureTheory OQ14.Maxwell OQ14.WeakEnergy Filter
open scoped Topology InnerProductSpace ComplexConjugate FourierTransform SchwartzMap

abbrev ScalarL2 := FourierL2.ScalarL2

theorem scalar_normSq_integrable (u : ScalarL2) : Integrable (fun x => Complex.normSq (u x)) := by
  apply (L2.integrable_inner (𝕜 := ℂ) u u).re.congr
  exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, Complex.normSq_apply])

theorem scalar_norm_squared (u : ScalarL2) : ‖u‖ ^ 2 = ∫ x, Complex.normSq (u x) := by
  have hi := L2.integrable_inner (𝕜 := ℂ) u u
  calc
    _ = (⟪u, u⟫_ℂ).re := by
      simpa only [RCLike.re_eq_complex_re] using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm
    _ = ∫ x, (inner (𝕜 := ℂ) (u x) (u x)).re := by
      rw [L2.inner_def, ← RCLike.re_eq_complex_re, ← integral_re hi]
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by simp [RCLike.inner_apply, Complex.normSq_apply])

theorem schwartz_normSq_integrable (f : 𝓢(Space, ℂ)) :
    Integrable (fun x => Complex.normSq (f x)) :=
  (scalar_normSq_integrable (FourierL2.embed f)).congr
    ((FourierL2.embed_ae f).mono (fun _ hx => congrArg Complex.normSq hx))

theorem schwartz_norm_squared (f : 𝓢(Space, ℂ)) :
    ‖FourierL2.embed f‖ ^ 2 = ∫ x, Complex.normSq (f x) := by
  rw [scalar_norm_squared]
  exact integral_congr_ae ((FourierL2.embed_ae f).mono (fun x hx => congrArg Complex.normSq hx))

theorem schwartz_fourier_norm_squared (f : 𝓢(Space, ℂ)) :
    ‖FourierL2.embed f‖ ^ 2 = ∫ ξ, Complex.normSq (𝓕 f ξ) := by
  rw [← FourierL2.schwartz_parseval_norm f, schwartz_norm_squared]
  rfl

theorem schwartz_family_fourier_energy {α : Type*} [Fintype α] (f : α → 𝓢(Space, ℂ)) :
    (∑ i, ‖FourierL2.embed (f i)‖ ^ 2) = ∫ ξ, ∑ i, Complex.normSq (𝓕 (f i) ξ) := by
  simp_rw [schwartz_fourier_norm_squared]
  exact (integral_finset_sum _ (fun i _ =>
    schwartz_normSq_integrable (SchwartzMap.fourierTransformCLE ℂ (f i)))).symm

theorem fourier_curl (f : Fin 3 → 𝓢(Space, ℂ)) (ξ : Space) (j : Fin 3) :
    𝓕 (GradientProjection.curl f j) ξ = (2 * Real.pi * Complex.I) *
      crossProduct (realLift (fun i => ξ i)) (fun i => 𝓕 (f i) ξ) j := by
  change SchwartzMap.fourierTransformCLM ℂ (GradientProjection.curl f j) ξ = _
  fin_cases j <;>
    simp [GradientProjection.curl, map_sub, SchwartzMap.fourierTransformCLM_apply,
      GradientProjection.fourier_pderivative, realLift, cross_apply] <;> ring

/-- Exact pointwise frequency algebra, including all longitudinal energy. -/
theorem frequency_energy (κ : ℂ) (ξ : Fin 3 → ℝ) (z : Vector) :
    (∑ p : Fin 3 × Fin 3, Complex.normSq (κ * (ξ p.1 : ℂ) * z p.2)) =
      (∑ j : Fin 3, Complex.normSq (κ * crossProduct (realLift ξ) z j)) +
        Complex.normSq (κ * dot (realLift ξ) z) := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_three, realLift, dot,
    cross_apply, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem schwartz_divcurl_energy (f : Fin 3 → 𝓢(Space, ℂ)) :
    (∑ p : Fin 3 × Fin 3, ‖FourierL2.embed (GradientProjection.pderivative p.1 (f p.2))‖ ^ 2) =
      (∑ j : Fin 3, ‖FourierL2.embed (GradientProjection.curl f j)‖ ^ 2) +
        ‖FourierL2.embed (GradientProjection.divergence f)‖ ^ 2 := by
  rw [schwartz_family_fourier_energy (fun p : Fin 3 × Fin 3 =>
      GradientProjection.pderivative p.1 (f p.2)),
    schwartz_family_fourier_energy (GradientProjection.curl f),
    schwartz_fourier_norm_squared (GradientProjection.divergence f)]
  have hc : Integrable (fun ξ => ∑ j : Fin 3, Complex.normSq (𝓕 (GradientProjection.curl f j) ξ)) :=
    integrable_finset_sum _ (fun j _ => schwartz_normSq_integrable
      (SchwartzMap.fourierTransformCLE ℂ (GradientProjection.curl f j)))
  have hd : Integrable (fun ξ => Complex.normSq (𝓕 (GradientProjection.divergence f) ξ)) :=
    schwartz_normSq_integrable (SchwartzMap.fourierTransformCLE ℂ (GradientProjection.divergence f))
  rw [← integral_add hc hd]
  apply integral_congr_ae
  exact Eventually.of_forall (fun ξ => by
    simp_rw [GradientProjection.fourier_pderivative, fourier_curl, GradientProjection.fourier_divergence]
    simpa only [dot, Fin.sum_univ_three, realLift] using
      frequency_energy (2 * Real.pi * Complex.I) (fun i => ξ i) (fun i => 𝓕 (f i) ξ))

end OQ14.DivCurl

#print axioms OQ14.DivCurl.scalar_norm_squared
#print axioms OQ14.DivCurl.schwartz_normSq_integrable
#print axioms OQ14.DivCurl.schwartz_family_fourier_energy
#print axioms OQ14.DivCurl.fourier_curl
#print axioms OQ14.DivCurl.frequency_energy
#print axioms OQ14.DivCurl.schwartz_divcurl_energy
