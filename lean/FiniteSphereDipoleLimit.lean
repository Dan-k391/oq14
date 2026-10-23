import FiniteSphereDipoleFlux
import FiniteSpherePlaneLimit

/-! Complete literal finite-ball material flux has its actual static dipole comparison on the whole plane. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereDipoleLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem actual_inverse_limit (p : ℝ → ι → Space) (ρ χ δ R k b γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hh : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (hq : ∀ a, 0 < a → a ≤ 1 → ∀ s, q a s ∈ closedBall 0 R)
    (hA : ∀ a, 0 < a → a ≤ 1 → (∑ s, ‖A a s‖) ≤ A₀/a) :
    let S := FiniteSphereActualSources.source p ρ χ R k b hρ hχ hi q j A
    let P := fun a l => StaticSpherePolarization.polarization χ
      (fun i => FiniteHerglotzFlux.electric k (fun _ => true) (q a) (j a) (A a) (p a l) i)
    Tendsto (fun a => ∫ z : Plane, ‖ParityTotalFlux.totalFlux k (b/a) (S a) (q a) (j a) (A a) z-
      FiniteSphereDipoleFlux.dipoleFlux k (p a) (fun _ => ρ*a) (P a) (q a) (j a) (A a) z‖) (𝓝[>] 0) (𝓝 0) := by
  let S := FiniteSphereActualSources.source p ρ χ R k b hρ hχ hi q j A
  let U := FiniteSphereActualSources.trial p ρ χ k q j A
  let P := fun a l => StaticSpherePolarization.polarization χ
    (fun i => FiniteHerglotzFlux.electric k (fun _ => true) (q a) (j a) (A a) (p a l) i)
  let M := FiniteSphereQuadratic.massConstant (ι := ι) χ ρ δ k R b
    (SphereReactionKernel.entryBound k*A₀) (2*SphereReactionKernel.entryBound k*|k| * A₀)
  have hM : 0 ≤ M := by
    have := FiniteSphereScale.totalVolume_nonnegative (ι := ι) ρ hρ.le
    have := SphereReactionKernel.entryBound_nonnegative k
    dsimp [M]
    unfold FiniteSphereQuadratic.massConstant FiniteSphereSourceMass.trialConstant
    positivity
  have h0 := FiniteSpherePlaneLimit.actual_inverse_limit p ρ χ δ R k b γ T A₀
    hρ hχ hδ hb hR hk hγ hT hTR hA₀ hsep hi hh q j A hq hA
  obtain ⟨η,hη,he⟩ := FiniteSphereActualSources.mass_and_gap p ρ χ δ R k b γ T A₀
    hρ hχ hδ hb hR hk hγ hT hTR hA₀ hsep hi hh q j A hA
  have hg : ∀ᶠ a : ℝ in 𝓝[>] 0, Admissible R (γ*a) (S a) ∧ Admissible R (γ*a) (U a) ∧
      sourceMass (S a) ≤ M*a^2 ∧ sourceMass (U a) ≤ M*a^2 := by
    have hn : ∀ᶠ a : ℝ in 𝓝[>] 0, a < η := nhdsWithin_le_nhds (gt_mem_nhds hη)
    filter_upwards [hn,self_mem_nhdsWithin] with a had ha
    have h := he a ha had
    exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, a ≤ 1 :=
    (show ∀ᶠ a : ℝ in 𝓝[>] 0, a < 1 from nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)).mono (fun a ha => ha.le)
  have hq' : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ s, q a s ∈ closedBall 0 R := by
    filter_upwards [hsmall,self_mem_nhdsWithin] with a ha1 ha
    exact hq a ha ha1
  have hA' : ∀ᶠ a : ℝ in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a := by
    filter_upwards [hsmall,self_mem_nhdsWithin] with a ha1 ha
    exact hA a ha ha1
  have h1 := StaticTrialLimit.trial_to_static k R T γ M A₀ hR hk hT hTR hγ hM hA₀ U q j A
    (hg.mono (fun a ha => ha.2.1)) hq' (hg.mono (fun a ha => ha.2.2.2)) hA'
  have hdip : ∀ᶠ a : ℝ in 𝓝[>] 0, ∀ z : Plane,
      FiniteStaticCoherent.staticMixed k (U a) (q a) (j a) (A a) z=
      FiniteSphereDipoleFlux.dipoleFlux k (p a) (fun _ => ρ*a) (P a) (q a) (j a) (A a) z := by
    filter_upwards [hsmall,self_mem_nhdsWithin] with a ha1 ha z
    exact FiniteSphereDipoleFlux.static_flux k (p a) (fun _ => ρ*a) (P a) (γ*a)
      (fun _ => mul_pos hρ ha) (mul_pos hγ ha) (fun l => by simpa only [add_mul] using hh a ha ha1 l)
      (q a) (j a) (A a) z
  have hdM : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a ≤ T+R := by
    have ht := (show Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds).const_mul γ
    simp only [mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds (by linarith : 0 < T+R))).mono (fun a ha => ha.le)
  obtain ⟨Ci,Cp,hCi,hCp,hw⟩ := ParityRemainderBound.whole_bounds (ι := κ) k R hR hk
  have ht := h0.add h1
  simp only [add_zero] at ht
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun z => norm_nonneg _))) _ ht
  filter_upwards [hg,hq',hdip,hdM,self_mem_nhdsWithin] with a hg hq hdip hdM ha
  have hd := mul_pos hγ ha
  have htotal := (hw (b/a) T (γ*a) hd hT hTR hdM (S a) hg.1 (q a) (j a) (A a) hq).2.1
  have hmixed := (SourceHerglotzFinite.electric_mass k R T (γ*a) hR hd hk hT hTR (U a) hg.2.1
    (fun _ => true) (q a) (j a) (A a) hq).1
  have hquad := (PlaneQuadraticFlux.whole_mass k R T (γ*a) hR hd hT hTR (U a) (U a) hg.2.1 hg.2.1).1
  have hfree : Integrable (ParityTotalFlux.freeFlux k (U a) (q a) (j a) (A a)) :=
    (hmixed.add hquad).congr (Filter.Eventually.of_forall (fun z => (ParityTotalFlux.free_identity k (U a) (q a) (j a) (A a) z).symm))
  have hrem := (FiniteStaticCoherent.whole_mass k R T (γ*a) hR hd hk hT hTR hdM (U a) hg.2.1
    (q a) (j a) (A a) hq).1
  have hs : Integrable (fun z => ParityTotalFlux.freeFlux k (U a) (q a) (j a) (A a) z-
      FiniteStaticCoherent.staticMixed k (U a) (q a) (j a) (A a) z) :=
    (hrem.add hquad).congr (Filter.Eventually.of_forall (fun z => by dsimp only [Pi.add_apply]; rw [ParityTotalFlux.free_identity]; ring))
  have heq (z : Plane) : ParityTotalFlux.totalFlux k (b/a) (S a) (q a) (j a) (A a) z-
      FiniteSphereDipoleFlux.dipoleFlux k (p a) (fun _ => ρ*a) (P a) (q a) (j a) (A a) z=
      (ParityTotalFlux.totalFlux k (b/a) (S a) (q a) (j a) (A a) z-ParityTotalFlux.freeFlux k (U a) (q a) (j a) (A a) z)+
      (ParityTotalFlux.freeFlux k (U a) (q a) (j a) (A a) z-FiniteStaticCoherent.staticMixed k (U a) (q a) (j a) (A a) z) := by
    rw [hdip z]; ring
  change (∫ z : Plane, ‖ParityTotalFlux.totalFlux k (b/a) (S a) (q a) (j a) (A a) z-
    FiniteSphereDipoleFlux.dipoleFlux k (p a) (fun _ => ρ*a) (P a) (q a) (j a) (A a) z‖) ≤ _
  simp_rw [heq]
  have hbound := integral_mono_ae ((htotal.sub hfree).add hs).norm ((htotal.sub hfree).norm.add hs.norm)
    (Filter.Eventually.of_forall (fun z => norm_add_le _ _))
  simp only [Pi.add_apply,Pi.sub_apply] at hbound
  have hint := integral_add (htotal.sub hfree).norm hs.norm
  simp only [Pi.sub_apply] at hint
  rw [hint] at hbound
  simpa only [Pi.add_apply,Pi.sub_apply,S,U] using hbound

end OQ14.FiniteSphereDipoleLimit
#print axioms OQ14.FiniteSphereDipoleLimit.actual_inverse_limit
