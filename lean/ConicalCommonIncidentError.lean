import ConicalCommonExteriorTranslation
import ConicalIncidentEstimate
import HelmholtzTranslation

/-! A source-free centered Helmholtz error for the actual finite angular illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonIncidentError
open MeasureTheory Set Metric OQ14.Maxwell
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

theorem incident_helmholtz (k : ℝ) (hk : k ≠ 0) (d : Input) (j : Fin 3) (x : Space) :
    ExteriorHelmholtz.laplacian (fun y => (FiniteAngularHerglotz.incident k d).E y j) x +
      (k : ℂ)^2 * (FiniteAngularHerglotz.incident k d).E x j = 0 := by
  let I := FiniteAngularHerglotz.incident k d
  have hM := MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H
    (fun i => (I.smoothE i).of_le (by simp)) (fun i => (I.smoothH i).of_le (by simp)) I.maxwell
  have hr : RegionalMaxwellHelmholtz.TestMaxwell k 1 univ I.E I.H := by
    intro j f
    simpa only [Complex.ofReal_one, one_mul, mul_one, neg_mul] using hM j (ConicalInnerMaxwell.globalTest f)
  have hw := RegionalMaxwellHelmholtz.electric_weak_helmholtz k 1 hk (by norm_num)
    univ _ _ hr (RegionalMaxwellHelmholtz.locallyIntegrable_integrableTests univ _
      (fun i => (I.smoothE i).continuous.locallyIntegrable)) j
  apply UniformHelmholtzEquation.classical_of_weak univ isOpen_univ k _
    (fun y _ => (I.smoothE j).contDiffAt) _ x (mem_univ x)
  simpa only [Real.sqrt_one, mul_one] using hw

def error (p : Data) (a k : ℝ) (center : Space) (d : Input) (j : Fin 3) (x : Space) : ℂ :=
  (FiniteAngularHerglotz.incident k d).E (center+x) j +
    ExteriorContinuity.electric k (ConicalSeparatedSource.physicalSource p a) x j

theorem error_smooth (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (center : Space) (d : Input) (j : Fin 3) (x : Space) (hx : x ∈ ball (0 : Space) a) :
    ContDiffAt ℝ (⊤ : ℕ∞) (error p a k center d j) x :=
  (HelmholtzTranslation.translated_contDiffAt center _ x ((FiniteAngularHerglotz.incident k d).smoothE j).contDiffAt).add
    (ConicalInteriorResponse.electric_smooth_interior k _
      (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.source_compact p a (hai.trans p.cutoff.rIn_lt_rOut).le) a
      (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy)) j x hx)

private theorem laplacian_add (f g : Space → ℂ) (x : Space)
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g x) :
    ExteriorHelmholtz.laplacian (fun y => f y+g y) x = ExteriorHelmholtz.laplacian f x+ExteriorHelmholtz.laplacian g x := by
  have hn := DebyeCalculus.laplacian_sub (fun _ : Space => (0 : ℂ)) g x contDiffAt_const hg
  have hz : ExteriorHelmholtz.laplacian (fun _ : Space => (0 : ℂ)) x = 0 := by simp [ExteriorHelmholtz.laplacian, dcoord]
  simp only [zero_sub,hz] at hn
  have h := DebyeCalculus.laplacian_sub f (fun y => -g y) x hf hg.neg
  simpa only [sub_neg_eq_add,hn,sub_neg_eq_add] using h

theorem error_helmholtz (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (hk : k ≠ 0)
    (center : Space) (d : Input) (j : Fin 3) (x : Space) (hx : x ∈ ball (0 : Space) a) :
    ExteriorHelmholtz.laplacian (error p a k center d j) x+(k : ℂ)^2*error p a k center d j x=0 := by
  have hs := ConicalInteriorResponse.electric_smooth_interior k _
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.source_compact p a (hai.trans p.cutoff.rIn_lt_rOut).le) a
    (fun i y hy => ConicalSeparatedSource.source_zero_material p a hai i y (ball_subset_closedBall hy)) j x hx
  have hh := ConicalSourceFreeHelmholtz.electric_classical_helmholtz k hk (ConicalSeparatedSource.forcing p a) _
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.forcing_ae p a) a p.cutoff.rOut
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (fun i y hy => ConicalSeparatedSource.source_zero_material p a hai i y (ball_subset_closedBall hy)) j x hx
  have ht : ExteriorHelmholtz.laplacian (HelmholtzTranslation.translated center (fun y => (FiniteAngularHerglotz.incident k d).E y j)) x+
      (k : ℂ)^2*(FiniteAngularHerglotz.incident k d).E (center+x) j=0 := by
    rw [HelmholtzTranslation.translated_laplacian]
    exact incident_helmholtz k hk d j (center+x)
  unfold error
  change ExteriorHelmholtz.laplacian (fun y => HelmholtzTranslation.translated center
    (fun z => (FiniteAngularHerglotz.incident k d).E z j) y +
      ExteriorContinuity.electric k (ConicalSeparatedSource.physicalSource p a) y j) x + _ = 0
  rw [laplacian_add _ _ x (HelmholtzTranslation.translated_contDiffAt center _ x ((FiniteAngularHerglotz.incident k d).smoothE j).contDiffAt) hs]
  linear_combination ht+hh

theorem uniform_error_bound (p : Data) (a b k : ℝ) (hai : a < p.cutoff.rIn) (hba : b < a) (hk : k ≠ 0)
    (center : Space) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : Input) (j : Fin 3) (g : ConicalRungeBall.ScalarBall a),
      (∀ᵐ x : Space ∂volume.restrict (closedBall (0 : Space) a), g x = error p a k center d j x) →
      ∀ x ∈ closedBall (0 : Space) b, ‖error p a k center d j x‖ ≤ C*‖g‖ := by
  obtain ⟨C,hC,hbound⟩ := HelmholtzInteriorEstimate.compact_interior_estimate
    (ball (0 : Space) a) (closedBall (0 : Space) b) isOpen_ball (isCompact_closedBall _ _)
    (closedBall_subset_ball hba) k
  refine ⟨C,hC,?_⟩
  intro d j g hg x hx
  have he : ∀ᵐ y : Space, y ∈ ball (0 : Space) a →
      ConicalBallExtension.scalarExtension a g y = error p a k center d j y := by
    have hh := (ae_restrict_iff' measurableSet_closedBall).mp hg
    filter_upwards [ConicalBallExtension.scalarExtension_ae a g, hh] with y he hh hy
    rw [he, indicator_of_mem (ball_subset_closedBall hy), hh (ball_subset_closedBall hy)]
  have ht := hbound (error p a k center d j) (ConicalBallExtension.scalarExtension a g)
    (error_smooth p a k hai center d j) (error_helmholtz p a k hai hk center d j) he x hx
  simpa only [ConicalBallExtension.scalarExtension_norm] using ht

end OQ14.ConicalCommonIncidentError
#print axioms OQ14.ConicalCommonIncidentError.incident_helmholtz
#print axioms OQ14.ConicalCommonIncidentError.error_smooth
#print axioms OQ14.ConicalCommonIncidentError.error_helmholtz
#print axioms OQ14.ConicalCommonIncidentError.uniform_error_bound
