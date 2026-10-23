import RestrictedTEReactionLimit
import RestrictedTEFreeLimit

/-! The actual complete harmonic TE finite-ball parity flux converges to its static coherent expression. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTETotalLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_inverse_to_static (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : Index →₀ ℂ) :
    let S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A
    Tendsto (fun a : ℝ => ∫ q : Plane,
      ‖RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
        staticMixed (S a) ((a : ℂ)⁻¹ • A) q‖) (𝓝[>] 0) (𝓝 0) := by
  let S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A
  obtain ⟨C,hC,M,hM,η,hη,hest⟩ := RestrictedTESourceMass.mass_and_gap p ρ χ δ R b γ hρ hχ hδ hb hsep hi hh A
  have hg : ∀ᶠ a : ℝ in 𝓝[>] 0, Admissible R (γ*a) (S a) ∧ sourceMass (S a)≤M*a^2 := by
    have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a<η := nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hn,self_mem_nhdsWithin] with a had ha
    have he := hest a ha had
    exact ⟨he.1,he.2.2.1⟩
  let T := max 2 (2*R)
  have hT : 2≤T := le_max_left _ _
  have hTR : 2*R≤T := le_max_right _ _
  have h0 := RestrictedTEReactionLimit.total_minus_free_convergence A b R T γ M hR hT hTR hγ hM S
    (hg.mono (fun _ h => h.1)) (hg.mono (fun _ h => h.2))
  have h1 := RestrictedTEFreeLimit.actual_inverse_to_static p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh A
  have ht := h0.add h1
  simp only [add_zero] at ht
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a≤T+R := by
    have hl := (show Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul γ
    simp only [mul_zero] at hl
    exact (hl.eventually (gt_mem_nhds (by linarith : 0<T+R))).mono (fun _ h => h.le)
  obtain ⟨Ci,Cp,hCi,hCp,hwhole⟩ := RestrictedTETotalFlux.whole_bounds A R hR
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hg,hsmall,self_mem_nhdsWithin] with a hg hdM ha
  change 0<a at ha
  have hd := mul_pos hγ ha
  have hr := (hwhole (b/a) T (γ*a) hd hT hTR hdM (S a) hg.1 (a : ℂ)⁻¹).1
  have hbase := RestrictedTEStaticFlux.dynamic_integrable ((a : ℂ)⁻¹ • A) R (γ*a) hR hd (S a) hg.1
  obtain ⟨_,_,hqq⟩ := MaxwellPlaneL1.whole_plane_bound 1 R (γ*a) hR hd
  have hiq := (hqq (S a) (S a) hg.1 hg.1).1
  have hfree : Integrable (freeFlux (S a) ((a : ℂ)⁻¹ • A)) := (hbase.add hiq).congr
    (Filter.Eventually.of_forall (fun q => (free_identity (S a) ((a : ℂ)⁻¹ • A) q).symm))
  obtain ⟨B,hB,hs⟩ := RestrictedTEStaticFlux.static_mass ((a : ℂ)⁻¹ • A)
  have hstatic := (hs R (γ*a) hd (S a) hg.1).1
  have herror := hfree.sub hstatic
  have heq (q : Plane) : RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
      staticMixed (S a) ((a : ℂ)⁻¹ • A) q=
      RestrictedTETotalFlux.remainder (b/a) (S a) ((a : ℂ)⁻¹ • A) q+
        (freeFlux (S a) ((a : ℂ)⁻¹ • A) q-staticMixed (S a) ((a : ℂ)⁻¹ • A) q) := by
    rw [RestrictedTETotalFlux.total_identity]
    ring
  have hrEq (q : Plane) : RestrictedTETotalFlux.remainder (b/a) (S a) ((a : ℂ)⁻¹ • A) q=
      RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-freeFlux (S a) ((a : ℂ)⁻¹ • A) q := by
    rw [RestrictedTETotalFlux.total_identity]
    ring
  change (∫ q : Plane, ‖RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
    staticMixed (S a) ((a : ℂ)⁻¹ • A) q‖)≤_
  simp_rw [heq]
  have hbound := integral_mono_ae (hr.add herror).norm (hr.norm.add herror.norm)
    (Filter.Eventually.of_forall (fun q => norm_add_le _ _))
  have hint := integral_add hr.norm herror.norm
  simp only [Pi.add_apply,Pi.sub_apply] at hbound hint
  rw [hint] at hbound
  simp only [hrEq] at hbound
  simpa only [hrEq] using hbound

end OQ14.RestrictedTETotalLimit
#print axioms OQ14.RestrictedTETotalLimit.actual_inverse_to_static
