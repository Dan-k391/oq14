import HelmholtzUniqueContinuation
import HelmholtzMollifierZero
import LocalAEZeroPropagation

/-! # Actual local unique continuation for weak Helmholtz fields

Smooth mollifiers solve the equation on fixed inner balls and inherit an actual
zero neighborhood. Ball continuation and their almost-everywhere convergence
therefore give the zero conclusion for the original locally integrable field.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.WeakHelmholtzContinuation

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.WeakPoynting
  OQ14.WeakHelmholtzRegularity OQ14.HelmholtzMollifiers
  OQ14.HelmholtzMollifierZero
open scoped Topology

theorem zero_on_ball_of_ae_zero_near (k : ℂ) (hk : k ≠ 0) (c : Space) (r : ℝ)
    (hr : 0 < r) (u : Space → ℂ) (hu : LocallyIntegrable u)
    (hw : IsWeakHelmholtz k (ball c r) u)
    (hz : ∃ U : Set Space, U ∈ 𝓝 c ∧ u =ᵐ[volume.restrict U] 0) :
    u =ᵐ[volume.restrict (ball c r)] 0 := by
  have hzero := eventually_zero_germ_of_ae_zero_near u c hz
  apply (ae_restrict_iff' measurableSet_ball).mpr
  filter_upwards [smooth_ae_tendsto u hu] with x hx
  intro hxr
  let s := (dist x c+r)/2
  have hd : dist x c < r := hxr
  have hs : s < r := by dsimp [s]; linarith
  have hs0 : 0 < s := by dsimp [s]; linarith [dist_nonneg (x := x) (y := c)]
  have hxs : x ∈ ball c s := by
    change dist x c < s
    dsimp [s]
    linarith
  have he : ∀ᶠ n in atTop, smooth (complexKernel (shrinkingBump n)) u x = 0 := by
    filter_upwards [eventually_helmholtz_on_fixed_ball k c r s hs u hu hw, hzero]
      with n hn hzn
    exact HelmholtzUniqueContinuation.zero_on_ball c s hs0 k hk
      (smooth (complexKernel (shrinkingBump n)) u)
      (smooth_regular _ u hu (complexKernel_regular _) (complexKernel_compact _)).contDiffOn
      hn hzn x hxs
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' (he.mono (fun _ hn => hn.symm)))

theorem zero_on_ball_of_ae_zero_ball (k : ℂ) (hk : k ≠ 0) (c : Space) (r : ℝ)
    (hr : 0 < r) (u : Space → ℂ) (hu : LocallyIntegrable u)
    (hw : IsWeakHelmholtz k (ball c r) u)
    (s : ℝ) (hs : 0 < s) (hz : u =ᵐ[volume.restrict (ball c s)] 0) :
    u =ᵐ[volume.restrict (ball c r)] 0 :=
  zero_on_ball_of_ae_zero_near k hk c r hr u hu hw
    ⟨ball c s, ball_mem_nhds c hs, hz⟩

theorem weak_equation_mono (k : ℂ) (Ω U : Set Space) (u : Space → ℂ)
    (hw : IsWeakHelmholtz k Ω u) (hU : U ⊆ Ω) : IsWeakHelmholtz k U u :=
  fun φ hφ hc hs => hw φ hφ hc (hs.trans hU)

theorem zero_on_connected_open (Ω : Set Space) (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (k : ℂ) (hk : k ≠ 0)
    (u : Space → ℂ) (hu : LocallyIntegrable u) (hw : IsWeakHelmholtz k Ω u)
    (c : Space) (hc : c ∈ Ω) (hz : LocalAEZeroPropagation.germZero u c) :
    u =ᵐ[volume.restrict Ω] 0 := by
  apply LocalAEZeroPropagation.ae_zero_on_of_germ Ω hΩ hconn u _ c hc hz
  intro a _ r hr hb hza
  obtain ⟨s,hs,hzs⟩ := hza
  exact zero_on_ball_of_ae_zero_ball k hk a r hr u hu
    (weak_equation_mono k Ω (ball a r) u hw hb) s hs hzs

end OQ14.WeakHelmholtzContinuation

#print axioms OQ14.WeakHelmholtzContinuation.zero_on_ball_of_ae_zero_near
#print axioms OQ14.WeakHelmholtzContinuation.zero_on_ball_of_ae_zero_ball
#print axioms OQ14.WeakHelmholtzContinuation.weak_equation_mono
#print axioms OQ14.WeakHelmholtzContinuation.zero_on_connected_open
