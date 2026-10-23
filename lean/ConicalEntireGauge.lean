import ConicalIncidentEstimate
import AngularHerglotz
import ConicalResponseLinear
import ConicalFiniteGauge

/-! Actual entire Maxwell incident fields in the fixed separated-source potential gauge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalEntireGauge
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalRungeBall
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

/-- An actual smooth entire vacuum Maxwell illumination. -/
structure Incident (k : ℝ) where
  E : Field
  H : Field
  smoothE : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => E x i)
  smoothH : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => H x i)
  maxwell : ∀ x, MaxwellAt k 1 1 E H x

def restricted {k : ℝ} (a : ℝ) (I : Incident k) : ConicalRungeBall.BallL2 a :=
  (WithLp.equiv 2 (Fin 3 → ConicalRungeBall.ScalarBall a)).symm (fun i => (SmallVolumeMaxwell.continuous_memLp_ball _ (I.smoothE i).continuous a).toLp (fun x => I.E x i))

theorem restricted_ae {k : ℝ} (a : ℝ) (I : Incident k) (i : Fin 3) :
    (restricted a I i : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)] fun x => I.E x i :=
  (SmallVolumeMaxwell.continuous_memLp_ball _ (I.smoothE i).continuous a).coeFn_toLp

def error (p : Data) (a k : ℝ) (I : Incident k) (i : Fin 3) (x : Space) : ℂ :=
  I.E x i+ExteriorContinuity.electric k (ConicalSeparatedSource.physicalSource p a) x i

theorem error_smooth (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (I : Incident k) (i : Fin 3)
    (x : Space) (hx : x ∈ ball (0 : Space) a) : ContDiffAt ℝ (⊤ : ℕ∞) (error p a k I i) x :=
  (I.smoothE i).contDiffAt.add
    (ConicalInteriorResponse.electric_smooth_interior k _
      (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
      (ConicalSeparatedSource.source_compact p a (hai.trans p.cutoff.rIn_lt_rOut).le) a
      (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy)) i x hx)

def solution (p : Data) (a k : ℝ) (c : Incident k) : VectorL2 :=
  ConicalMaterialRunge.solutionOperator (ConicalSeparatedSource.material p a) k a
    (restricted a c)

def electric (p : Data) (a k : ℝ) (c : Incident k) : Field :=
  MaterialField.total (ConicalSeparatedSource.material p a) k (solution p a k c) (c.E)

def totalSource (p : Data) (a k : ℝ) (c : Incident k) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a) (solution p a k c)-ConicalSeparatedSource.forcing p a

def source (p : Data) (a k : ℝ) (c : Incident k) (i : Fin 3) (x : Space) : ℂ :=
  DynamicVolume.source (ConicalSeparatedSource.material p a) (solution p a k c) i x-
    ConicalSeparatedSource.physicalSource p a i x

theorem source_ae (p : Data) (a k : ℝ) (c : Incident k) (i : Fin 3) :
    (NewtonL2.physicalCoordinate (totalSource p a k c) i : Space → ℂ) =ᵐ[volume] source p a k c i :=
  ConicalResponseLinear.source_sub_ae _ _ _ _
    (StaticNewton.material_source_ae (ConicalSeparatedSource.material p a) (solution p a k c))
    (ConicalSeparatedSource.forcing_ae p a) i

theorem source_zero_outer (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (c : Incident k) (i : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : source p a k c i x=0 := by
  rw [source,DynamicVolume.source_zero (ConicalSeparatedSource.material p a) (solution p a k c)
    p.cutoff.rOut (ConicalSeparatedMaxwell.material_compact_outer p a hai) i x hx,
    ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le i x hx,sub_self]

theorem exists_incident_extension (p : Data) (a b k : ℝ) (hai : a < p.cutoff.rIn) (hba : b < a)
    (c : Incident k) :
    ∃ J : Field, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i)) ∧
      (∀ i, HasCompactSupport (fun x => J x i)) ∧
      ∀ i x, x ∈ closedBall (0 : Space) b → J x i=error p a k c i x := by
  have hex (i : Fin 3) := ExteriorGreen.smooth_localization isOpen_ball
    (isCompact_closedBall (0 : Space) b) (closedBall_subset_ball hba)
    (error p a k c i) (error_smooth p a k hai c i)
  choose J hJ hc he using hex
  exact ⟨fun x i => J i x,hJ,hc,fun i x hx => (he i x hx).eq_of_nhds⟩

theorem electric_in_fixed_gauge (p : Data) (a b k : ℝ) (hai : a < p.cutoff.rIn) (hba : b < a)
    (c : Incident k) (J : Field)
    (hJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=error p a k c i x)
    (i : Fin 3) :
    (fun x => FieldResponse.electric k (totalSource p a k c) (source p a k c) x i+J x i)
      =ᵐ[volume.restrict (closedBall (0 : Space) b)] fun x => electric p a k c x i := by
  have hs := ConicalResponseLinear.electric_sub_ae k b p.cutoff.rOut
    (StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a) (solution p a k c))
    (ConicalSeparatedSource.forcing p a)
    (DynamicVolume.source (ConicalSeparatedSource.material p a) (solution p a k c))
    (ConicalSeparatedSource.physicalSource p a)
    (StaticNewton.material_source_ae _ _) (ConicalSeparatedSource.forcing_ae p a)
    (DynamicVolume.source_zero _ _ _ (ConicalSeparatedMaxwell.material_compact_outer p a hai))
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le) i
  filter_upwards [hs,ae_restrict_of_ae (ConicalInteriorResponse.electric_ae_interior k
    (ConicalSeparatedSource.forcing p a) (ConicalSeparatedSource.physicalSource p a)
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.forcing_ae p a) a p.cutoff.rOut
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (fun j y hy => ConicalSeparatedSource.source_zero_material p a hai j y (ball_subset_closedBall hy))),
    ae_restrict_mem measurableSet_closedBall] with x hs he hx
  change FieldResponse.electric k
    (StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a) (solution p a k c)-ConicalSeparatedSource.forcing p a)
    (fun j y => DynamicVolume.source (ConicalSeparatedSource.material p a) (solution p a k c) j y-
      ConicalSeparatedSource.physicalSource p a j y) x i+J x i=_
  rw [hs,hJ i x hx,error,congrFun (he (closedBall_subset_ball hba hx)) i]
  change _=c.E x i+
    FieldResponse.electric k (StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a) (solution p a k c))
      (DynamicVolume.source (ConicalSeparatedSource.material p a) (solution p a k c)) x i
  ring

theorem gauss (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (c : Incident k) (J : Field)
    (hJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=error p a k c i x)
    (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
      (FieldResponse.electric k (totalSource p a k c) (source p a k c) x i+J x i)*dcoord f x i)=0 := by
  have hc : HasCompactSupport (f : Space → ℂ) :=
    (isCompact_closedBall (0 : Space) b).of_isClosed_subset isClosed_closure (hf.trans ball_subset_closedBall)
  have hm := MaterialMaxwell.volume_solution_testMaxwell (ConicalSeparatedSource.material p a) k a
    (solution p a k c) (ConicalBallExtension.weighted (ConicalSeparatedSource.material p a) a (restricted a c)) c.E c.H (ConicalSeparatedSource.material_compact p a)
    (ConicalMaterialRunge.weighted_actual _ a _ _ (ConicalSeparatedSource.material_compact p a) (restricted_ae a c))
    (ConicalMaterialRunge.solution_equation _ k a ha hfreq _)
    (fun i => (c.smoothE i).continuous.locallyIntegrable)
    (fun i => (c.smoothH i).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k c.E c.H
      (fun i => (c.smoothE i).of_le (by simp)) (fun i => (c.smoothH i).of_le (by simp)) c.maxwell)
  have hg := ConicalFiniteGauge.material_gauss k hk _ _ _ hm ⟨f,hc⟩
  have he (i : Fin 3) : (∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
      (FieldResponse.electric k (totalSource p a k c) (source p a k c) x i+J x i)*dcoord f x i)=
      ∫ x : Space, (MaterialMaxwell.dielectric (ConicalSeparatedSource.material p a) x : ℂ)*
        electric p a k c x i*dcoord f x i := by
    apply integral_congr_ae
    filter_upwards [(ae_restrict_iff' measurableSet_closedBall).mp
      (electric_in_fixed_gauge p a b k hai hba c J hJ i)] with x he
    by_cases hx : x ∈ ball (0 : Space) b
    · rw [he (ball_subset_closedBall hx)]
      have hxa : ‖x‖ ≤ a := by
        have hn : ‖x‖ < b := by simpa only [mem_ball,dist_zero_right] using hx
        linarith
      have heps : MaterialMaxwell.dielectric (ConicalSeparatedSource.material p a) x=ConicalLocalGauss.epsilon p x := by
        rw [MaterialMaxwell.dielectric,ConicalSeparatedMaxwell.material_spatial_inside p a hai x
          (by simpa only [mem_closedBall,dist_zero_right] using hxa)]
        change 1+(ConicalCapField.permittivity p.contrast p.threshold x-1)=ConicalCapField.permittivity p.contrast p.threshold x
        ring
      rw [heps]
    · have hn : x ∉ tsupport (f : Space → ℂ) := fun h => hx (hf h)
      simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hn,ContinuousLinearMap.zero_apply,mul_zero]
  simpa only [he] using hg


def system (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (c : Incident k) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=error p a k c i x) :
    ConicalProjectionData.System p b :=
  ConicalCompactPotential.system p b (hba.trans hai) k p.cutoff.rOut (totalSource p a k c) (source p a k c)
    (source_zero_outer p a k hai c) (source_ae p a k c) J hJ
    (gauss p a b k ha hai hba hk hfreq c J heJ)

theorem system_total_inner (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (c : Incident k) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=error p a k c i x)
    (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (system p a b k ha hai hba hk hfreq c J hJ heJ) i x=
        electric p a k c x i := by
  filter_upwards [ConicalCompactPotential.total_inner p b (hba.trans hai) k p.cutoff.rOut
    (totalSource p a k c) (source p a k c) (source_zero_outer p a k hai c) (source_ae p a k c) J hJ
    (gauss p a b k ha hai hba hk hfreq c J heJ) i,
    (ae_restrict_iff' measurableSet_closedBall).mp (electric_in_fixed_gauge p a b k hai hba c J heJ i)] with x ht he hx
  exact (ht hx).trans (he (ball_subset_closedBall hx))


end OQ14.ConicalEntireGauge
#print axioms OQ14.ConicalEntireGauge.source_ae
#print axioms OQ14.ConicalEntireGauge.source_zero_outer
#print axioms OQ14.ConicalEntireGauge.exists_incident_extension
#print axioms OQ14.ConicalEntireGauge.electric_in_fixed_gauge
#print axioms OQ14.ConicalEntireGauge.gauss

#print axioms OQ14.ConicalEntireGauge.system
#print axioms OQ14.ConicalEntireGauge.system_total_inner

#print axioms OQ14.ConicalEntireGauge.restricted_ae
#print axioms OQ14.ConicalEntireGauge.error_smooth
