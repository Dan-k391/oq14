import ConicalSourceFreeHelmholtz
import ConicalSeparatedIllumination
import HelmholtzInteriorEstimate
import DebyeCalculus

/-! Uniform interior control of actual finite-wave incident approximation errors. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalIncidentEstimate
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space

theorem finite_classical_helmholtz (k : ℝ) (hk : k≠0)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) (x : Space) :
    ExteriorHelmholtz.laplacian (fun y => ConicalFinitePlanes.electric k c y i) x+
      (k : ℂ)^2*ConicalFinitePlanes.electric k c x i=0 := by
  have hM := MaterialMaxwell.classical_vacuum_testMaxwell k
    (ConicalFinitePlanes.electric k c) (ConicalFinitePlanes.magnetic k c)
    (fun j => (ConicalFinitePlanes.electric_smooth k c j).of_le (by simp))
    (fun j => (ConicalFinitePlanes.magnetic_smooth k c j).of_le (by simp))
    (ConicalFinitePlanes.maxwell_at k c)
  have hr : RegionalMaxwellHelmholtz.TestMaxwell k 1 univ
      (ConicalFinitePlanes.electric k c) (ConicalFinitePlanes.magnetic k c) := by
    intro j f
    simpa only [Complex.ofReal_one,one_mul,mul_one,neg_mul] using hM j (ConicalInnerMaxwell.globalTest f)
  have hw := RegionalMaxwellHelmholtz.electric_weak_helmholtz k 1 hk (by norm_num)
    univ _ _ hr (RegionalMaxwellHelmholtz.locallyIntegrable_integrableTests univ _
      (fun j => (ConicalFinitePlanes.electric_smooth k c j).continuous.locallyIntegrable)) i
  apply UniformHelmholtzEquation.classical_of_weak univ isOpen_univ k _
    (fun y _ => (ConicalFinitePlanes.electric_smooth k c i).contDiffAt) _ x (mem_univ x)
  simpa only [Real.sqrt_one,mul_one] using hw

private theorem laplacian_add (f g : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ExteriorHelmholtz.laplacian (fun y => f y+g y) x=
      ExteriorHelmholtz.laplacian f x+ExteriorHelmholtz.laplacian g x := by
  have hn := DebyeCalculus.laplacian_sub (fun _ : Space => (0 : ℂ)) g x contDiffAt_const hg
  have hz : ExteriorHelmholtz.laplacian (fun _ : Space => (0 : ℂ)) x=0 := by
    simp [ExteriorHelmholtz.laplacian,dcoord]
  simp only [zero_sub,hz] at hn
  have h := DebyeCalculus.laplacian_sub f (fun y => -g y) x hf hg.neg
  simpa only [sub_neg_eq_add,hn,sub_neg_eq_add] using h

def error (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ)
    (i : Fin 3) : Space → ℂ := fun x => ConicalFinitePlanes.electric k c x i+
      ExteriorContinuity.electric k (ConicalSeparatedSource.physicalSource p a) x i

theorem error_smooth (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) (x : Space)
    (hx : x ∈ ball (0 : Space) a) : ContDiffAt ℝ (⊤ : ℕ∞) (error p a k c i) x :=
  (ConicalFinitePlanes.electric_smooth k c i).contDiffAt.add
    (ConicalInteriorResponse.electric_smooth_interior k _
      (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.source_compact p a (hai.trans p.cutoff.rIn_lt_rOut).le) a
      (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy)) i x hx)

theorem error_helmholtz (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (hk : k≠0)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) (x : Space)
    (hx : x ∈ ball (0 : Space) a) :
    ExteriorHelmholtz.laplacian (error p a k c i) x+(k : ℂ)^2*error p a k c i x=0 := by
  have hs := ConicalInteriorResponse.electric_smooth_interior k _
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.source_compact p a (hai.trans p.cutoff.rIn_lt_rOut).le) a
    (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy)) i x hx
  have hh := ConicalSourceFreeHelmholtz.electric_classical_helmholtz k hk
    (ConicalSeparatedSource.forcing p a) _
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.forcing_ae p a) a p.cutoff.rOut
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy)) i x hx
  unfold error
  rw [laplacian_add _ _ x (ConicalFinitePlanes.electric_smooth k c i).contDiffAt hs]
  linear_combination finite_classical_helmholtz k hk c i x+hh

theorem error_extension_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) a →
      ConicalBallExtension.scalarExtension a
        ((ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k) i) x=
          error p a k c i x := by
  have hr := (ae_restrict_iff' measurableSet_closedBall).mp (ConicalFinitePlanes.restricted_ae k a c i)
  have hi := (ae_restrict_iff' measurableSet_closedBall).mp
    (ConicalBallRestriction.vector_ae a (ConicalSeparatedDynamic.incident p a k) i)
  have hs := (ae_restrict_iff' measurableSet_closedBall).mp
    (ConicalSeparatedDynamic.incident_ae p a k hai i)
  have hd := (ae_restrict_iff' measurableSet_closedBall).mp
    (Lp.coeFn_sub (ConicalFinitePlanes.restricted k a c i) (ConicalSeparatedIllumination.incidentBall p a k i))
  filter_upwards [ConicalBallExtension.scalarExtension_ae a
    ((ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k) i),
    hr,hi,hs,hd,ConicalInteriorResponse.electric_ae_interior k
      (ConicalSeparatedSource.forcing p a) (ConicalSeparatedSource.physicalSource p a)
      (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.forcing_ae p a) a p.cutoff.rOut
      (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy))]
    with x he hr hi hs hd hg hx
  have hc := ball_subset_closedBall hx
  rw [he,indicator_of_mem hc]
  change ((ConicalFinitePlanes.restricted k a c i)-(ConicalSeparatedIllumination.incidentBall p a k i)) x=_
  rw [hd hc]
  simp only [Pi.sub_apply,hr hc,ConicalSeparatedIllumination.incidentBall]
  rw [hi hc,hs hc,congrFun (hg hx) i]
  simp only [sub_neg_eq_add,error]

theorem uniform_error_bound (p : Data) (a b k : ℝ) (hai : a < p.cutoff.rIn)
    (hba : b < a) (hk : k≠0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3)
      (x : Space), x ∈ closedBall (0 : Space) b →
      ‖error p a k c i x‖ ≤ C*‖ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k‖ := by
  obtain ⟨C,hC,hbound⟩ := HelmholtzInteriorEstimate.compact_interior_estimate
    (ball (0 : Space) a) (closedBall (0 : Space) b) isOpen_ball (isCompact_closedBall _ _)
    (closedBall_subset_ball hba) k
  refine ⟨C,hC,?_⟩
  intro c i x hx
  apply (hbound (error p a k c i)
    (ConicalBallExtension.scalarExtension a
      ((ConicalFinitePlanes.restricted k a c-ConicalSeparatedIllumination.incidentBall p a k) i))
    (error_smooth p a k hai c i) (error_helmholtz p a k hai hk c i)
    (error_extension_ae p a k hai c i) x hx).trans
  rw [ConicalBallExtension.scalarExtension_norm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le _ i) hC

end OQ14.ConicalIncidentEstimate
#print axioms OQ14.ConicalIncidentEstimate.finite_classical_helmholtz
#print axioms OQ14.ConicalIncidentEstimate.error_smooth
#print axioms OQ14.ConicalIncidentEstimate.error_helmholtz
#print axioms OQ14.ConicalIncidentEstimate.error_extension_ae
#print axioms OQ14.ConicalIncidentEstimate.uniform_error_bound
