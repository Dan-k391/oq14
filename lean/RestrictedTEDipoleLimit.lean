import RestrictedTETotalLimit
import RestrictedTEDipoleError

/-! Literal complete harmonic TE parity inverse flux has its actual finite-dipole whole-plane limit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEDipoleLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_inverse_to_dipoles (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hR : 0≤R) (hb : b≠0) (hγ : 0<γ)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : Index →₀ ℂ) :
    let S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A
    let P := fun (a : ℝ) l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l))
    Tendsto (fun a : ℝ => ∫ q : Plane,
      ‖RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
        RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q‖)
      (𝓝[>] 0) (𝓝 0) := by
  let S := RestrictedTESourceMass.source p ρ χ R b hρ hχ hi A
  let P := fun (a : ℝ) l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l))
  obtain ⟨C,hC,η,hη,hest⟩ := RestrictedTEAsymptotics.eventual_estimates p ρ χ δ R b hρ hχ hδ hb hsep hi A
  obtain ⟨B,hB,hprofile⟩ := RestrictedTEDipoleError.from_estimates (ι := ι) A
  let K := 6*B*|StaticPlaneInclusions.errorConstant (ι := ι) χ ρ δ 1 R b C C γ|
  have hp : ∀ᶠ a : ℝ in 𝓝[>] 0,
      Integrable (fun q : Plane => staticMixed (S a) ((a : ℂ)⁻¹ • A) q-
        RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q) ∧
      (∫ q : Plane, ‖staticMixed (S a) ((a : ℂ)⁻¹ • A) q-
        RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q‖)≤K*a ∧
      Admissible R (γ*a) (S a) := by
    have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a<η := nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hn,self_mem_nhdsWithin] with a had ha
    change 0<a at ha
    obtain ⟨ha1,he⟩ := hest a ha had
    have hprof := hprofile (p a) ρ a χ δ R 1 b C C γ hρ ha hχ hγ (hh a ha ha1)
      (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1)
      (RestrictedTEAsymptotics.forcing p ρ χ R hρ hχ hi A a)
      (fun l => electric ((a : ℂ)⁻¹ • A) (p a l)) he
    dsimp only at hprof
    rw [← RestrictedTESourceMass.source_actual p ρ χ R b hρ hχ hi A a ha ha1] at hprof
    have hs : Admissible R (γ*a) (S a) := RestrictedTEFiniteBalls.source_admissible p ρ χ R b (γ*a) a hρ hχ hi
      (fun a => (a : ℂ)⁻¹ • A) ha ha1 (fun l => by simpa only [add_mul] using hh a ha ha1 l)
    exact ⟨hprof.1,hprof.2,hs⟩
  have h0 := RestrictedTETotalLimit.actual_inverse_to_static p ρ χ δ R b γ hρ hχ hδ hR hb hγ hsep hi hh A
  have h1 : Tendsto (fun a : ℝ => ∫ q : Plane, ‖staticMixed (S a) ((a : ℂ)⁻¹ • A) q-
      RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q‖)
      (𝓝[>] 0) (𝓝 0) := by
    have ht := (show Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul K
    simp only [mul_zero] at ht
    exact squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _)))
      (hp.mono (fun _ h => h.2.1)) ht
  have ht := h0.add h1
  simp only [add_zero] at ht
  let T := max 2 (2*R)
  have hT : 2≤T := le_max_left _ _
  have hTR : 2*R≤T := le_max_right _ _
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a≤T+R := by
    have hl := (show Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul γ
    simp only [mul_zero] at hl
    exact (hl.eventually (gt_mem_nhds (by linarith : 0<T+R))).mono (fun _ h => h.le)
  obtain ⟨Ci,Cp,hCi,hCp,hwhole⟩ := RestrictedTETotalFlux.whole_bounds A R hR
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hp,hsmall,self_mem_nhdsWithin] with a hp hdM ha
  change 0<a at ha
  have hd := mul_pos hγ ha
  have htotal := (hwhole (b/a) T (γ*a) hd hT hTR hdM (S a) hp.2.2 (a : ℂ)⁻¹).2.1
  obtain ⟨_,_,hs⟩ := RestrictedTEStaticFlux.static_mass ((a : ℂ)⁻¹ • A)
  have hstatic := (hs R (γ*a) hd (S a) hp.2.2).1
  have herror := htotal.sub hstatic
  have heq (q : Plane) : RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
      RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q=
      (RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-staticMixed (S a) ((a : ℂ)⁻¹ • A) q)+
      (staticMixed (S a) ((a : ℂ)⁻¹ • A) q-RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q) := by ring
  change (∫ q : Plane, ‖RestrictedTETotalFlux.totalFlux (b/a) (S a) ((a : ℂ)⁻¹ • A) q-
    RestrictedTEDipoleError.dipoleFlux (p a) (fun _ => ρ*a) (P a) ((a : ℂ)⁻¹ • A) q‖)≤_
  simp_rw [heq]
  have hbound := integral_mono_ae (herror.add hp.1).norm (herror.norm.add hp.1.norm)
    (Filter.Eventually.of_forall (fun q => norm_add_le _ _))
  have hint := integral_add herror.norm hp.1.norm
  simp only [Pi.add_apply,Pi.sub_apply] at hbound hint
  rw [hint] at hbound
  exact hbound

end OQ14.RestrictedTEDipoleLimit
#print axioms OQ14.RestrictedTEDipoleLimit.actual_inverse_to_dipoles
