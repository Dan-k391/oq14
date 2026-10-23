import ConicalIncidentEstimate
import ConicalResponseLinear

/-! Literal finite-incident material fields in the fixed separated-source potential gauge. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalFiniteGauge
open MeasureTheory Set Metric OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalRungeBall
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

theorem material_gauss (k : ℝ) (hk : k≠0) (ε : Space → ℝ) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H) (f : DynamicSource.Test) :
    (∑ i : Fin 3, ∫ x, (ε x : ℂ)*E x i*dcoord f.val x i)=0 := by
  let f' : RegionalMaxwellHelmholtz.Test (univ : Set Space) :=
    ⟨f.val,f.val.smooth (⊤ : ℕ∞),f.property,subset_univ _⟩
  have hcurl (i : Fin 3) (g : RegionalMaxwellHelmholtz.Test (univ : Set Space)) :
      RegionalMaxwellHelmholtz.curlPair (RegionalMaxwellHelmholtz.fieldPair H) i g=
        -(Complex.I*(k : ℂ))*RegionalMaxwellHelmholtz.fieldPair (fun x j => (ε x : ℂ)*E x j) i g :=
    (hM i (ConicalInnerMaxwell.globalTest g)).2
  exact RegionalMaxwellHelmholtz.divPair_zero_of_curl
    (RegionalMaxwellHelmholtz.fieldPair H)
    (RegionalMaxwellHelmholtz.fieldPair (fun x j => (ε x : ℂ)*E x j)) (-(Complex.I*(k : ℂ)))
    (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk))) hcurl f'

def solution (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ) : VectorL2 :=
  ConicalMaterialRunge.solutionOperator (ConicalSeparatedSource.material p a) k a
    (ConicalFinitePlanes.restricted k a c)

def electric (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ) : Field :=
  MaterialField.total (ConicalSeparatedSource.material p a) k (solution p a k c) (ConicalFinitePlanes.electric k c)

def totalSource (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a) (solution p a k c)-ConicalSeparatedSource.forcing p a

def source (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) (x : Space) : ℂ :=
  DynamicVolume.source (ConicalSeparatedSource.material p a) (solution p a k c) i x-
    ConicalSeparatedSource.physicalSource p a i x

theorem source_ae (p : Data) (a k : ℝ) (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) :
    (NewtonL2.physicalCoordinate (totalSource p a k c) i : Space → ℂ) =ᵐ[volume] source p a k c i :=
  ConicalResponseLinear.source_sub_ae _ _ _ _
    (StaticNewton.material_source_ae (ConicalSeparatedSource.material p a) (solution p a k c))
    (ConicalSeparatedSource.forcing_ae p a) i

theorem source_zero_outer (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (i : Fin 3) (x : Space)
    (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : source p a k c i x=0 := by
  rw [source,DynamicVolume.source_zero (ConicalSeparatedSource.material p a) (solution p a k c)
    p.cutoff.rOut (ConicalSeparatedMaxwell.material_compact_outer p a hai) i x hx,
    ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le i x hx,sub_self]

theorem exists_incident_extension (p : Data) (a b k : ℝ) (hai : a < p.cutoff.rIn) (hba : b < a)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) :
    ∃ J : Field, (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => J x i)) ∧
      (∀ i, HasCompactSupport (fun x => J x i)) ∧
      ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x := by
  have hex (i : Fin 3) := ExteriorGreen.smooth_localization isOpen_ball
    (isCompact_closedBall (0 : Space) b) (closedBall_subset_ball hba)
    (ConicalIncidentEstimate.error p a k c i) (ConicalIncidentEstimate.error_smooth p a k hai c i)
  choose J hJ hc he using hex
  exact ⟨fun x i => J i x,hJ,hc,fun i x hx => (he i x hx).eq_of_nhds⟩

theorem electric_in_fixed_gauge (p : Data) (a b k : ℝ) (hai : a < p.cutoff.rIn) (hba : b < a)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
    (hJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x)
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
  rw [hs,hJ i x hx,ConicalIncidentEstimate.error,congrFun (he (closedBall_subset_ball hba hx)) i]
  change _=ConicalFinitePlanes.electric k c x i+
    FieldResponse.electric k (StaticCoefficient.sqrtMultiplier (ConicalSeparatedSource.material p a) (solution p a k c))
      (DynamicVolume.source (ConicalSeparatedSource.material p a) (solution p a k c)) x i
  ring

theorem gauss (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field)
    (hJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x)
    (f : 𝓢(Space,ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ i : Fin 3, ∫ x : Space, (ConicalLocalGauss.epsilon p x : ℂ)*
      (FieldResponse.electric k (totalSource p a k c) (source p a k c) x i+J x i)*dcoord f x i)=0 := by
  have hc : HasCompactSupport (f : Space → ℂ) :=
    (isCompact_closedBall (0 : Space) b).of_isClosed_subset isClosed_closure (hf.trans ball_subset_closedBall)
  have hm := ConicalMaterialRunge.finite_solution_maxwell (ConicalSeparatedSource.material p a) k a ha hfreq
    (ConicalSeparatedSource.material_compact p a) c
  have hg := material_gauss k hk _ _ _ hm ⟨f,hc⟩
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
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x) :
    ConicalProjectionData.System p b :=
  ConicalCompactPotential.system p b (hba.trans hai) k p.cutoff.rOut (totalSource p a k c) (source p a k c)
    (source_zero_outer p a k hai c) (source_ae p a k c) J hJ
    (gauss p a b k ha hai hba hk hfreq c J heJ)

theorem system_total_inner (p : Data) (a b k : ℝ) (ha : 0 ≤ a) (hai : a < p.cutoff.rIn) (hba : b < a)
    (hk : k≠0) (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a)
    (c : ConicalRungeClosure.WaveIndex →₀ ℂ) (J : Field) (hJ : ∀ i, Continuous (fun x => J x i))
    (heJ : ∀ i x, x ∈ closedBall (0 : Space) b → J x i=ConicalIncidentEstimate.error p a k c i x)
    (i : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (system p a b k ha hai hba hk hfreq c J hJ heJ) i x=
        electric p a k c x i := by
  filter_upwards [ConicalCompactPotential.total_inner p b (hba.trans hai) k p.cutoff.rOut
    (totalSource p a k c) (source p a k c) (source_zero_outer p a k hai c) (source_ae p a k c) J hJ
    (gauss p a b k ha hai hba hk hfreq c J heJ) i,
    (ae_restrict_iff' measurableSet_closedBall).mp (electric_in_fixed_gauge p a b k hai hba c J heJ i)] with x ht he hx
  exact (ht hx).trans (he (ball_subset_closedBall hx))


end OQ14.ConicalFiniteGauge
#print axioms OQ14.ConicalFiniteGauge.material_gauss
#print axioms OQ14.ConicalFiniteGauge.source_ae
#print axioms OQ14.ConicalFiniteGauge.source_zero_outer
#print axioms OQ14.ConicalFiniteGauge.exists_incident_extension
#print axioms OQ14.ConicalFiniteGauge.electric_in_fixed_gauge
#print axioms OQ14.ConicalFiniteGauge.gauss

#print axioms OQ14.ConicalFiniteGauge.system
#print axioms OQ14.ConicalFiniteGauge.system_total_inner
