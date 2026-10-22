import ParityRemainderMoving
import PlaneQuadraticMoving
import SourceHerglotzFiniteMoving

/-! Actual complete parity plane flux compared to a static trial source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ParityCompleteLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

private theorem add_mass (f g : Plane → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (∫ q : Plane, ‖f q+g q‖) ≤ (∫ q : Plane, ‖f q‖)+(∫ q : Plane, ‖g q‖) := by
  rw [← integral_add hf.norm hg.norm]
  exact integral_mono_ae (hf.add hg).norm (hf.norm.add hg.norm)
    (Filter.Eventually.of_forall (fun q => norm_add_le _ _))

theorem total_to_trial (k b R T γ C M A₀ : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hγ : 0 < γ) (hC : 0 ≤ C) (hM : 0 ≤ M) (hA₀ : 0 ≤ A₀)
    (ρ σ : ℝ → Source) (p : ℝ → ι → Space) (j : ℝ → ι → Fin 3) (A : ℝ → ι → ℂ)
    (hρ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (ρ a))
    (hσ : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (σ a))
    (hp : ∀ᶠ a in 𝓝[>] 0, ∀ s, p a s ∈ closedBall 0 R)
    (hmρ : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a) ≤ M*a^2)
    (hmσ : ∀ᶠ a in 𝓝[>] 0, sourceMass (σ a) ≤ M*a^2)
    (he : ∀ᶠ a in 𝓝[>] 0, sourceMass (ρ a-σ a) ≤ C*a^3)
    (hA : ∀ᶠ a in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a) :
    Tendsto (fun a => ∫ q : Plane, ‖ParityTotalFlux.totalFlux k (b/a) (ρ a) (p a) (j a) (A a) q-
      ParityTotalFlux.freeFlux k (σ a) (p a) (j a) (A a) q‖) (𝓝[>] 0) (𝓝 0) := by
  have hr := ParityRemainderMoving.total_minus_free_convergence k b R T γ M A₀ hR hk hT hTR hγ hM
    ρ p j A hρ hp hmρ hA
  have hr' : Tendsto (fun a => ∫ q : Plane, ‖ParityTotalFlux.remainder k (b/a) (ρ a) (p a) (j a) (A a) q‖)
      (𝓝[>] 0) (𝓝 0) := by
    convert hr using 1
    funext a
    apply integral_congr_ae
    filter_upwards with q
    rw [ParityTotalFlux.total_identity]
    simp
  have hm := SourceHerglotzFiniteMoving.electric_convergence k R T γ C A₀ hR hγ hk hT hTR hA₀
    ρ σ (fun _ _ => true) p j A hρ hσ hp hA he
  have hq := PlaneQuadraticMoving.self_difference_convergence k R T γ C M hR hγ hT hTR hC hM
    ρ σ hρ hσ hmρ hmσ he
  have ht := (hr'.add hm).add hq
  simp only [add_zero] at ht
  have hpos : 0 < T+R := by linarith
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a ≤ T+R := by
    have ht : Tendsto (fun a : ℝ => γ*a) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((show Continuous (fun a : ℝ => γ*a) by fun_prop).continuousAt (x := 0)).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    exact (ht.eventually (gt_mem_nhds hpos)).mono (fun a ha => ha.le)
  obtain ⟨Ci,Cp,hCi,hCp,hwhole⟩ := ParityRemainderBound.whole_bounds (ι := ι) k R hR hk
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hρ,hσ,hp,hsmall,self_mem_nhdsWithin] with a hρ hσ hp hs ha
  have hir := (hwhole (b/a) T (γ*a) (mul_pos hγ ha) hT hTR hs (ρ a) hρ (p a) (j a) (A a) hp).1
  have him := (SourceHerglotzFinite.electric_sub_mass k R T (γ*a) hR (mul_pos hγ ha) hk hT hTR
    (ρ a) (σ a) hρ hσ (fun _ => true) (p a) (j a) (A a) hp).1
  obtain ⟨_,_,hqq⟩ := MaxwellPlaneL1.whole_plane_bound k R (γ*a) hR (mul_pos hγ ha)
  have hiq := (hqq (ρ a) (ρ a) hρ hρ).1.sub (hqq (σ a) (σ a) hσ hσ).1
  have heq (q : Plane) : ParityTotalFlux.totalFlux k (b/a) (ρ a) (p a) (j a) (A a) q-
      ParityTotalFlux.freeFlux k (σ a) (p a) (j a) (A a) q=
      (ParityTotalFlux.remainder k (b/a) (ρ a) (p a) (j a) (A a) q+
        (SourceHerglotzFinite.electricMixed k (ρ a) (fun _ => true) (p a) (j a) (A a) q-
          SourceHerglotzFinite.electricMixed k (σ a) (fun _ => true) (p a) (j a) (A a) q))+
        (MaxwellPlaneL1.flux k (ρ a) (ρ a) q-MaxwellPlaneL1.flux k (σ a) (σ a) q) := by
    rw [ParityTotalFlux.total_identity,ParityTotalFlux.free_identity,ParityTotalFlux.free_identity]
    ring
  simp_rw [heq]
  exact (add_mass _ _ (hir.add him) hiq).trans (add_le_add_right (add_mass _ _ hir him) _)

end OQ14.ParityCompleteLimit
#print axioms OQ14.ParityCompleteLimit.total_to_trial
