import ExteriorHelmholtz

/-! # Actual spatial translation of scalar Helmholtz equations -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.HelmholtzTranslation
open Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz

def translated (c : Space) (u : Space → ℂ) (y : Space) : ℂ := u (c+y)

theorem translated_fderiv (c : Space) (u : Space → ℂ) (y : Space) :
    fderiv ℝ (translated c u) y = fderiv ℝ u (c+y) := by
  exact fderiv_comp_add_left c

theorem translated_second_fderiv (c : Space) (u : Space → ℂ) (y : Space) :
    fderiv ℝ (fderiv ℝ (translated c u)) y = fderiv ℝ (fderiv ℝ u) (c+y) := by
  rw [show fderiv ℝ (translated c u) = (fun z => fderiv ℝ u (c+z)) from
    funext (fun z => translated_fderiv c u z)]
  exact fderiv_comp_add_left c
theorem translated_partial (c : Space) (u : Space → ℂ) (y : Space) (i : Fin 3) :
    dcoord (translated c u) y i = dcoord u (c+y) i := by
  simp only [dcoord, translated_fderiv]

theorem translated_second_partial (c : Space) (u : Space → ℂ) (y : Space) (i j : Fin 3) :
    dcoord (fun z => dcoord (translated c u) z j) y i =
      dcoord (fun z => dcoord u z j) (c+y) i := by
  simp_rw [translated_partial]
  exact translated_partial c (fun z => dcoord u z j) y i

theorem translated_laplacian (c : Space) (u : Space → ℂ) (y : Space) :
    laplacian (translated c u) y = laplacian u (c+y) := by
  simp only [laplacian, translated_second_partial]

theorem translated_contDiffAt (c : Space) (u : Space → ℂ) (y : Space)
    (hu : ContDiffAt ℝ (⊤ : ℕ∞) u (c+y)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (translated c u) y :=
  hu.comp y (contDiffAt_const.add contDiffAt_id)

theorem translate_mem_ball (c y : Space) (L : ℝ) :
    c+y ∈ ball c L ↔ y ∈ ball (0 : Space) L := by
  simp only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero]

theorem translated_contDiffOn_ball (c : Space) (L : ℝ) (u : Space → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (ball c L)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (translated c u) (ball (0 : Space) L) := by
  exact hu.comp (contDiffOn_const.add contDiffOn_id)
    (fun y hy => (translate_mem_ball c y L).mpr hy)

theorem translated_helmholtz_residual (c : Space) (k : ℂ) (u : Space → ℂ) (y : Space) :
    laplacian (translated c u) y+k^2*translated c u y =
      laplacian u (c+y)+k^2*u (c+y) := by
  rw [translated_laplacian]
  rfl

theorem translated_helmholtz_ball (c : Space) (L : ℝ) (k : ℂ) (u : Space → ℂ)
    (hu : ∀ x ∈ ball c L, laplacian u x+k^2*u x=0) :
    ∀ y ∈ ball (0 : Space) L, laplacian (translated c u) y+k^2*translated c u y=0 := by
  intro y hy
  rw [translated_helmholtz_residual]
  exact hu (c+y) ((translate_mem_ball c y L).mpr hy)


theorem translated_zero_ball_iff (c : Space) (a : ℝ) (u : Space → ℂ) :
    (∀ y ∈ ball (0 : Space) a, translated c u y = 0) ↔
      (∀ x ∈ ball c a, u x = 0) := by
  constructor
  · intro hz x hx
    have he : c+(x-c)=x := by abel
    have hy : x-c ∈ ball (0 : Space) a := by
      apply (translate_mem_ball c (x-c) a).mp
      rwa [he]
    simpa only [translated, he] using hz (x-c) hy
  · intro hz y hy
    exact hz (c+y) ((translate_mem_ball c y a).mpr hy)
end OQ14.HelmholtzTranslation

#print axioms OQ14.HelmholtzTranslation.translated_fderiv
#print axioms OQ14.HelmholtzTranslation.translated_second_fderiv
#print axioms OQ14.HelmholtzTranslation.translated_partial
#print axioms OQ14.HelmholtzTranslation.translated_second_partial
#print axioms OQ14.HelmholtzTranslation.translated_laplacian
#print axioms OQ14.HelmholtzTranslation.translated_contDiffAt
#print axioms OQ14.HelmholtzTranslation.translate_mem_ball
#print axioms OQ14.HelmholtzTranslation.translated_contDiffOn_ball
#print axioms OQ14.HelmholtzTranslation.translated_helmholtz_residual
#print axioms OQ14.HelmholtzTranslation.translated_helmholtz_ball
#print axioms OQ14.HelmholtzTranslation.translated_zero_ball_iff

