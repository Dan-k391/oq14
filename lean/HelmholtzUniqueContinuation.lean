import HelmholtzBallContinuation
import HelmholtzTranslation
import LocalZeroPropagation

/-! # Unique continuation from the actual smooth Helmholtz equation

The local propagation property is derived from harmonic moments and translated
balls, then propagated across a connected open domain.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.HelmholtzUniqueContinuation

open Filter Metric Set OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.HelmholtzTranslation
open scoped Topology

theorem zero_on_ball (c : Space) (L : ℝ) (hL : 0 < L) (k : ℂ) (hk : k ≠ 0)
    (u : Space → ℂ) (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (ball c L))
    (heq : ∀ x ∈ ball c L, laplacian u x + k^2*u x = 0)
    (hzero : u =ᶠ[𝓝 c] 0) : ∀ x ∈ ball c L, u x = 0 := by
  have ht : translated c u =ᶠ[𝓝 (0 : Space)] 0 := by
    have hc : Tendsto (fun y : Space => c+y) (𝓝 0) (𝓝 c) := by
      have h : Continuous (fun y : Space => c+y) := continuous_const.add continuous_id
      simpa only [ContinuousAt, add_zero] using h.continuousAt (x := 0)
    exact hzero.comp_tendsto hc
  exact (translated_zero_ball_iff c L u).mp
    (HelmholtzBallContinuation.zero_on_ball_of_zero_neighborhood L hL k hk
      (translated c u) (translated_contDiffOn_ball c L u hu)
      (translated_helmholtz_ball c L k u heq) ht)

theorem zero_on_connected_open (Ω : Set Space) (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (k : ℂ) (hk : k ≠ 0) (u : Space → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (heq : ∀ x ∈ Ω, laplacian u x + k^2*u x = 0)
    (c : Space) (hc : c ∈ Ω) (hzero : u =ᶠ[𝓝 c] 0) :
    ∀ x ∈ Ω, u x = 0 := by
  apply LocalZeroPropagation.zero_on_of_germ Ω hΩ hconn u _ c hc hzero
  intro a _ r hr hb hz
  exact zero_on_ball a r hr k hk u (hu.mono hb) (fun x hx => heq x (hb hx)) hz

theorem zero_on_connected_open_of_ball (Ω : Set Space) (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (k : ℂ) (hk : k ≠ 0) (u : Space → ℂ)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u Ω)
    (heq : ∀ x ∈ Ω, laplacian u x + k^2*u x = 0)
    (c : Space) (hc : c ∈ Ω) (r : ℝ) (hr : 0 < r)
    (hzero : ∀ x ∈ ball c r, u x = 0) : ∀ x ∈ Ω, u x = 0 :=
  zero_on_connected_open Ω hΩ hconn k hk u hu heq c hc
    (eventually_of_mem (ball_mem_nhds c hr) hzero)

end OQ14.HelmholtzUniqueContinuation

#print axioms OQ14.HelmholtzUniqueContinuation.zero_on_ball
#print axioms OQ14.HelmholtzUniqueContinuation.zero_on_connected_open
#print axioms OQ14.HelmholtzUniqueContinuation.zero_on_connected_open_of_ball
