import ConicalRungeBall
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! Genuine finite transverse-plane-wave approximation of an actual separated incident field in ball L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalRungeClosure
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalRungeAnnihilator OQ14.ConicalRungeBall
open scoped InnerProductSpace ComplexConjugate Topology
abbrev Space := Maxwell.Space
abbrev WaveIndex := AngularPower.Sphere × Fin 3

def waves (k a : ℝ) (w : WaveIndex) : BallL2 a := wave k a (w.1 : Space) w.2
def waveSpan (k a : ℝ) : Submodule ℂ (BallL2 a) := Submodule.span ℂ (range (waves k a))

def target (k a T : ℝ) (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) : BallL2 a :=
  (WithLp.equiv 2 (Fin 3 → ScalarBall a)).symm (fun j =>
    (LocalVolumeResponse.electric_memLp_ball k a T G σ
      (NewtonReciprocity.compact_source_integrable T G σ hcσ hG) hcσ hG j).toLp
      (fun x => FieldResponse.electric k G σ x j))

theorem target_component_ae (k a T : ℝ) (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) (j : Fin 3) :
    (target k a T G σ hcσ hG j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => FieldResponse.electric k G σ x j :=
  (LocalVolumeResponse.electric_memLp_ball k a T G σ
    (NewtonReciprocity.compact_source_integrable T G σ hcσ hG) hcσ hG j).coeFn_toLp

theorem inner_target_eq (k a T : ℝ) (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) (g : BallL2 a) :
    ⟪g,target k a T G σ hcσ hG⟫_ℂ=
      ∑ j : Fin 3, ∫ x, FieldResponse.electric k G σ x j*density a g j x := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [density_integral,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [target_component_ae k a T G σ hcσ hG j] with x hx
  simp only [RCLike.inner_apply,hx]

theorem target_mem_closedSpan (k : ℝ) (hk : 0 < k) (a T : ℝ) (ha : 0 ≤ a) (haT : a ≤ T)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hσin : ∀ j x, x ∈ closedBall (0 : Space) a → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j) :
    target k a T G σ hcσ hG ∈ (waveSpan k a).topologicalClosure := by
  haveI : CompleteSpace (BallL2 a) := by
    change CompleteSpace (Fin 3 → ScalarBall a)
    infer_instance
  rw [← (waveSpan k a).orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro g hg
  have hplane (n : Space) (hn : ‖n‖=1) (i : Fin 3) : planePair k (density a g) n i=0 := by
    rw [← inner_wave_eq]
    apply (Submodule.mem_orthogonal' _ _).mp hg
    apply Submodule.subset_span
    refine ⟨(⟨n,?_⟩,i),rfl⟩
    simpa only [mem_sphere,dist_zero_right] using hn
  rw [inner_target_eq]
  exact reciprocal_pair_zero k hk a T ha haT (extension a g) G (density a g) σ
    (density_zero_outer a g) hcσ hσin (extension_ae a g) hG hplane

theorem finite_approximation (k : ℝ) (hk : 0 < k) (a T : ℝ) (ha : 0 ≤ a) (haT : a ≤ T)
    (G : VectorFourier.VectorL2) (σ : Fin 3 → Space → ℂ)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hσin : ∀ j x, x ∈ closedBall (0 : Space) a → σ j x=0)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : WaveIndex →₀ ℂ,
      ‖(c.sum fun w b => b • waves k a w)-target k a T G σ hcσ hG‖ < ε := by
  have ht := target_mem_closedSpan k hk a T ha haT G σ hcσ hσin hG
  change target k a T G σ hcσ hG ∈ closure (waveSpan k a : Set (BallL2 a)) at ht
  obtain ⟨v,hv,hd⟩ := Metric.mem_closure_iff.mp ht ε hε
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨c,?_⟩
  rw [hc]
  simpa only [dist_eq_norm,norm_sub_rev] using hd

theorem separated_finite_approximation (p : ConicalStaticVolume.Data) (a : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (k : ℝ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : WaveIndex →₀ ℂ,
      ‖(c.sum fun w b => b • waves k a w)-
        target k a p.cutoff.rOut (ConicalSeparatedSource.forcing p a) (ConicalSeparatedSource.physicalSource p a)
          (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
          (ConicalSeparatedSource.forcing_ae p a)‖ < ε :=
  finite_approximation k hk a p.cutoff.rOut ha (hai.trans p.cutoff.rIn_lt_rOut).le
    (ConicalSeparatedSource.forcing p a) (ConicalSeparatedSource.physicalSource p a)
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.source_zero_material p a hai) (ConicalSeparatedSource.forcing_ae p a) ε hε

end OQ14.ConicalRungeClosure

#print axioms OQ14.ConicalRungeClosure.target_component_ae
#print axioms OQ14.ConicalRungeClosure.inner_target_eq
#print axioms OQ14.ConicalRungeClosure.target_mem_closedSpan
#print axioms OQ14.ConicalRungeClosure.finite_approximation
#print axioms OQ14.ConicalRungeClosure.separated_finite_approximation
