import ExteriorHelmholtz
import ModalDipole

/-! # Genuine Laplacians of radial harmonic tests -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.HelmholtzTestCalculus

open OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.ExteriorClassical
  OQ14.ModalDipole

def radial (ψ : ℝ → ℂ) (x : Space) : ℂ := ψ (‖x‖^2)

theorem radial_smooth (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (radial ψ) :=
  hψ.comp (contDiff_norm_sq ℝ)

theorem radial_partial (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x : Space) (i : Fin 3) :
    dcoord (radial ψ) x i = 2 * (x i : ℂ) * deriv ψ (‖x‖^2) := by
  have hd := (hψ.differentiable (by simp) (‖x‖^2)).hasDerivAt.hasFDerivAt.comp x
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hd.fderiv
  simpa [radial, dcoord, ContinuousLinearMap.comp_apply, basis,
    EuclideanSpace.inner_single_right, Complex.real_smul, mul_assoc] using hv

theorem radial_second_partial (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x : Space) (i : Fin 3) :
    dcoord (fun y => dcoord (radial ψ) y i) x i =
      2 * deriv ψ (‖x‖^2) + 4 * (x i : ℂ)^2 * deriv (deriv ψ) (‖x‖^2) := by
  have hψ' : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.mp hψ).2
  have hd := ((radial_smooth (deriv ψ) hψ').differentiable (by simp)).differentiableAt (x := x)
  have he : (fun y => dcoord (radial ψ) y i) =
      fun y => 2 * (y i : ℂ) * radial (deriv ψ) y :=
    funext (fun y => radial_partial ψ hψ y i)
  rw [he, partial_mul ((coordinate_differentiableAt x i).const_mul 2) hd,
    partial_const_mul (coordinate_differentiableAt x i),
    coordinate_partial, if_pos rfl, radial_partial (deriv ψ) hψ']
  simp only [radial]
  ring

theorem radial_laplacian (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Space) :
    laplacian (radial ψ) x =
      4 * (‖x‖^2 : ℝ) * deriv (deriv ψ) (‖x‖^2) + 6 * deriv ψ (‖x‖^2) := by
  simp only [laplacian, radial_second_partial ψ hψ, Fin.sum_univ_three]
  have hs := GreenKernel.coordinate_squares x
  push_cast
  linear_combination 4 * deriv (deriv ψ) (‖x‖^2) * hs

theorem second_partial_mul (f g : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x)
    (i : Fin 3) :
    dcoord (fun y => dcoord (fun z => f z * g z) y i) x i =
      f x * dcoord (fun y => dcoord g y i) x i +
      g x * dcoord (fun y => dcoord f y i) x i + 2 * dcoord f x i * dcoord g x i := by
  have hdf := hf.differentiableAt (by simp)
  have hdg := hg.differentiableAt (by simp)
  have hdf' := (partial_smooth hf i).differentiableAt (by simp)
  have hdg' := (partial_smooth hg i).differentiableAt (by simp)
  have hf1 : ContDiffAt ℝ 1 f x := hf.of_le (by simp)
  have hg1 : ContDiffAt ℝ 1 g x := hg.of_le (by simp)
  have he : (fun y => dcoord (fun z => f z * g z) y i) =ᶠ[nhds x]
      fun y => f y * dcoord g y i + g y * dcoord f y i := by
    filter_upwards [hf1.eventually (by norm_num), hg1.eventually (by norm_num)] with y hy hz
    exact partial_mul (hy.differentiableAt (by norm_num)) (hz.differentiableAt (by norm_num)) i
  have he' := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) he.fderiv_eq
  change dcoord _ x i = dcoord _ x i at he'
  rw [he', partial_add (hdf.mul hdg') (hdg.mul hdf'),
    partial_mul hdf hdg', partial_mul hdg hdf']
  ring

theorem laplacian_mul (f g : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    laplacian (fun y => f y * g y) x =
      f x * laplacian g x + g x * laplacian f x +
        2 * ∑ i : Fin 3, dcoord f x i * dcoord g x i := by
  simp only [laplacian, second_partial_mul f g x hf hg, Fin.sum_univ_three]
  ring

theorem radial_harmonic_laplacian (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (P : Space → ℂ) (x : Space) (hP : ContDiffAt ℝ (⊤ : ℕ∞) P x)
    (l : ℕ) (hH : laplacian P x = 0)
    (hEuler : (∑ i : Fin 3, (x i : ℂ) * dcoord P x i) = (l : ℂ) * P x) :
    laplacian (fun y => radial ψ y * P y) x =
      P x * (4 * (‖x‖^2 : ℝ) * deriv (deriv ψ) (‖x‖^2) +
        (4 * (l : ℂ) + 6) * deriv ψ (‖x‖^2)) := by
  rw [laplacian_mul _ _ x (radial_smooth ψ hψ).contDiffAt hP, hH,
    radial_laplacian ψ hψ, mul_zero, zero_add]
  simp only [radial_partial ψ hψ, Fin.sum_univ_three] at hEuler ⊢
  linear_combination 4 * deriv ψ (‖x‖^2) * hEuler

end OQ14.HelmholtzTestCalculus

#print axioms OQ14.HelmholtzTestCalculus.radial_smooth
#print axioms OQ14.HelmholtzTestCalculus.radial_partial
#print axioms OQ14.HelmholtzTestCalculus.radial_second_partial
#print axioms OQ14.HelmholtzTestCalculus.radial_laplacian
#print axioms OQ14.HelmholtzTestCalculus.second_partial_mul
#print axioms OQ14.HelmholtzTestCalculus.laplacian_mul
#print axioms OQ14.HelmholtzTestCalculus.radial_harmonic_laplacian
