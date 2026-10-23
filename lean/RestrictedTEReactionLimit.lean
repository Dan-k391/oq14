import RestrictedTETotalFlux
import ParityRemainderMoving

/-! The actual complete harmonic TE parity reaction flux vanishes in the shrinking-ball scaling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEReactionLimit
open MeasureTheory Metric Set Filter Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology

theorem total_minus_free_convergence (A : Index →₀ ℂ) (b R T γ M : ℝ)
    (hR : 0≤R) (hT : 2≤T) (hTR : 2*R≤T) (hγ : 0<γ) (hM : 0≤M)
    (S : ℝ → Source)
    (hS : ∀ᶠ a : ℝ in 𝓝[>] 0, Admissible R (γ*a) (S a))
    (hm : ∀ᶠ a : ℝ in 𝓝[>] 0, sourceMass (S a)≤M*a^2) :
    Tendsto (fun a : ℝ => ∫ q : Plane,
      ‖RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
        freeFlux (S a) ((a : ℂ)⁻¹ • A) q‖) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Ci,Cp,hCi,hCp,hwhole⟩ := RestrictedTETotalFlux.whole_bounds A R hR
  have hpos : 0<T+R := by linarith
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a≤1 ∧ γ*a≤T+R := by
    have ht : Tendsto (fun a : ℝ => γ*a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((show Continuous (fun a : ℝ => γ*a) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ)≤𝓝 0 from nhdsWithin_le_nhds)
    have ha : ∀ᶠ a : ℝ in 𝓝[>] 0, a<1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
    filter_upwards [ha,ht.eventually (gt_mem_nhds hpos)] with a ha ht
    exact ⟨ha.le,ht.le⟩
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _
    (ParityRemainderMoving.upper_limit 1 b R T γ Ci Cp M 1 hγ.ne' hpos.ne')
  filter_upwards [hS,hm,hsmall,self_mem_nhdsWithin] with a hS hm hs ha
  change 0<a at ha
  have heq (q : Plane) : RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
      freeFlux (S a) ((a : ℂ)⁻¹ • A) q=RestrictedTETotalFlux.remainder (b/a) (S a) ((a : ℂ)⁻¹ • A) q := by
    rw [RestrictedTETotalFlux.total_identity]
    ring
  simp_rw [heq]
  have hn : ‖(a : ℂ)⁻¹‖≤1/a := by simp [norm_inv,abs_of_pos ha,one_div]
  exact ((hwhole (b/a) T (γ*a) (mul_pos hγ ha) hT hTR hs.2 (S a) hS (a : ℂ)⁻¹).2.2).trans
    (ParityRemainderMoving.budget_bound 1 b R T γ Ci Cp M 1 a (sourceMass (S a)) ‖(a : ℂ)⁻¹‖
      hR (by linarith) hγ ha hs.1 hs.2 hCi hCp hM (sourceMass_nonnegative _) (norm_nonneg _) hm hn)

end OQ14.RestrictedTEReactionLimit
#print axioms OQ14.RestrictedTEReactionLimit.total_minus_free_convergence
