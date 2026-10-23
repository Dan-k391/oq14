import SourceCoreReaction
import WeightedAnnulusDatum
import HomogeneousVolumeUniqueness

/-! Actual local L2 bounds for clipped layered source fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceLocalBounds
open MeasureTheory Filter Set Metric OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
open OQ14.ClippedLayerProfiles OQ14.LayerElectricProfiles
open scoped Topology

theorem select_bound (gs : List RadialStack.Layer) (f : RadialStack.Layer → ℂ) (z : ℂ) :
    ∃ M : ℝ,0≤M ∧ ∀ r : ℝ,‖select gs (fun g _ => f g) (fun _ => z) r‖≤M := by
  induction gs with
  | nil => exact ⟨‖z‖,norm_nonneg _,fun _ => le_rfl⟩
  | cons g gs ih =>
    obtain ⟨M,hM,hb⟩ := ih
    refine ⟨‖f g‖+M,add_nonneg (norm_nonneg _) hM,?_⟩
    intro r
    change ‖if g.a<r then f g else select gs (fun g _ => f g) (fun _ => z) r‖≤_
    split_ifs
    · linarith
    · linarith [hb r,norm_nonneg (f g)]

theorem inverseSigma_bound (d : Data) : ∃ M : ℝ,0≤M ∧ ∀ r : ℝ,‖SourceRadialSystem.inverseSigma d r‖≤M := by
  obtain ⟨M,hM,hb⟩ := select_bound d.gs (fun g => (g.σ : ℂ)⁻¹) 0
  refine ⟨max M 1,le_trans hM (le_max_left _ _),?_⟩
  intro r
  dsimp only [SourceRadialSystem.inverseSigma,SourceRadialSystem.extend,ClippedLayerProfiles.inverseSigma]
  split_ifs
  · simpa only [norm_one] using le_max_right M (1 : ℝ)
  · exact (hb r).trans (le_max_left _ _)
  · simpa only [norm_one] using le_max_right M (1 : ℝ)

theorem continuous_memLp_ball (f : Space → ℂ) (hf : Continuous f) (T : ℝ) :
    MemLp f 2 (volume.restrict (closedBall 0 T)) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) T)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (isCompact_closedBall (0 : Space) T).measure_lt_top⟩
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0 : Space) T).exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable.restrict M
    ((ae_restrict_mem measurableSet_closedBall).mono (fun x hx => hM x hx))

theorem bounded_mul_memLp_ball (m f : Space → ℂ) (hm : Measurable m)
    (M : ℝ) (hb : ∀ x,‖m x‖≤M) (T : ℝ) (hf : MemLp f 2 (volume.restrict (closedBall 0 T))) :
    MemLp (fun x => m x*f x) 2 (volume.restrict (closedBall 0 T)) := by
  apply hf.of_le_mul (c := M) (hm.aestronglyMeasurable.restrict.mul hf.aestronglyMeasurable)
  exact Eventually.of_forall (fun x => by change ‖m x*f x‖≤M*‖f x‖;rw [norm_mul];exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _))

theorem electric_memLp_ball (d : Data) (P : Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceElectricProfiles.electric d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  have hQ := quotient_continuous (d.l+3) _ (state_continuous d).fst d.c d.hc
  have hQ' := quotient_continuous (d.l+2) _ (state_continuous d).snd d.c d.hc
  have hP : Continuous (complexEvaluate P) := (complexEvaluate_regular P).continuous
  have hD : Continuous (fun x => dcoord (complexEvaluate P) x i) := by
    simp_rw [complexEvaluate_partial]
    exact (complexEvaluate_regular _).continuous
  have hX : Continuous (fun x : Space => (x i : ℂ)) := by fun_prop
  let A := fun x : Space => (d.l : ℂ)*(d.l+1)*quotient (d.l+3) (SourceElectricProfiles.value d) d.c ‖x‖*
    (x i : ℂ)*complexEvaluate P x
  let B := fun x : Space => SourceElectricProfiles.a d ‖x‖*dcoord (complexEvaluate P) x i-
    (d.l : ℂ)*quotient (d.l+2) (SourceElectricProfiles.momentum d) d.c ‖x‖*(x i : ℂ)*complexEvaluate P x
  have hA : Continuous A := (((continuous_const.mul continuous_const).mul (hQ.comp continuous_norm)).mul hX).mul hP
  have hB : Continuous B :=
    (((SourceElectricProfiles.a_continuous d).comp continuous_norm).mul hD).sub
      (((continuous_const.mul (hQ'.comp continuous_norm)).mul hX).mul hP)
  obtain ⟨M,_,hb⟩ := inverseSigma_bound d
  have hm : Measurable (fun x : Space => SourceRadialSystem.inverseSigma d (radius d.c ‖x‖)) :=
    (SourceRadialSystem.inverseSigma_measurable d).comp ((radius_continuous d.c).comp continuous_norm).measurable
  have hmain := bounded_mul_memLp_ball _ A hm M (fun x => hb _) T (continuous_memLp_ball A hA T)
  have he : (fun x => SourceElectricProfiles.electric d P x i)=
      (fun x => SourceRadialSystem.inverseSigma d (radius d.c ‖x‖)*A x+B x) := by
    funext x
    dsimp [SourceElectricProfiles.electric,RadialNormalPrimitive.electric,SourceElectricProfiles.b,A,B]
    ring
  rw [he]
  exact hmain.add (continuous_memLp_ball B hB T)

theorem magnetic_continuous (d : Data) (P : Poly) (i : Fin 3) :
    Continuous (fun x => SourceElectricProfiles.magnetic d P x i) := by
  have hQ := quotient_continuous (d.l+1) _ (state_continuous d).fst d.c d.hc
  have hT := (continuous_apply i).comp (HarmonicRadiationGeometry.angularToroidal_continuous P)
  exact (continuous_const.mul (hQ.comp continuous_norm)).mul hT

theorem magnetic_memLp_ball (d : Data) (P : Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => SourceElectricProfiles.magnetic d P x i) 2 (volume.restrict (closedBall 0 T)) :=
  continuous_memLp_ball _ (magnetic_continuous d P i) T


theorem sigmaAt_select (gs : List RadialStack.Layer) (r : ℝ) :
    (RadialGluing.sigmaAt gs r : ℂ)=select gs (fun g _ => (g.σ : ℂ)) (fun _ => 0) r := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases h : g.a<r <;> simp [RadialGluing.sigmaAt,select,h,ih]

theorem sigma_formula (d : Data) :
    sigma d=SourceRadialSystem.extend d.R d.X
      (select d.gs (fun g _ => (g.σ : ℂ)) (fun _ => 0)) (fun _ => 1) := by
  unfold sigma
  have hf : (fun r => (RadialGluing.sigmaAt d.gs r : ℂ))=select d.gs (fun g _ => (g.σ : ℂ)) (fun _ => 0) := funext (sigmaAt_select d.gs)
  rw [hf]

theorem sigma_measurable (d : Data) : Measurable (sigma d) := by
  rw [sigma_formula]
  exact extend_measurable _ _ _ _ (select_measurable _ _ _ (fun _ => measurable_const) measurable_const) measurable_const

theorem sigma_bound (d : Data) : ∃ M : ℝ,0≤M ∧ ∀ r : ℝ,‖sigma d r‖≤M := by
  obtain ⟨M,hM,hb⟩ := select_bound d.gs (fun g => (g.σ : ℂ)) 0
  refine ⟨max M 1,le_trans hM (le_max_left _ _),?_⟩
  intro r
  rw [sigma_formula]
  dsimp only [SourceRadialSystem.extend]
  split_ifs
  · simpa only [norm_one] using le_max_right M (1 : ℝ)
  · exact (hb r).trans (le_max_left _ _)
  · simpa only [norm_one] using le_max_right M (1 : ℝ)

theorem piecewise_memLp_ball (r T : ℝ) (f g : Space → ℂ) (hf : Continuous f)
    (hg : MemLp g 2 (volume.restrict (closedBall 0 T))) :
    MemLp (fun x => if ‖x‖≤r then f x else g x) 2 (volume.restrict (closedBall 0 T)) := by
  have hs : MeasurableSet {x : Space | ‖x‖≤r} := measurableSet_le continuous_norm.measurable measurable_const
  have h := ((continuous_memLp_ball f hf T).indicator hs).add (hg.indicator hs.compl)
  convert h using 1
  funext x
  by_cases hx : ‖x‖≤r <;> simp [Set.indicator,hx]

def electricSource (d : Data) (P : Poly) (i : Fin 3) (x : Space) : ℂ :=
  (sigma d ‖x‖-1)*SourceUnclippedMaxwell.electric d P x i

theorem source_zero_inner (d : Data) (P : Poly) (i : Fin 3) (x : Space) (hx : ‖x‖≤d.R) :
    electricSource d P i x=0 := by
  simp only [electricSource,sigma,SourceRadialSystem.extend,if_pos hx,sub_self,zero_mul]

theorem source_zero_outer (d : Data) (P : Poly) (i : Fin 3) (x : Space) (hx : d.X<‖x‖) :
    electricSource d P i x=0 := by
  have hR : d.R<‖x‖ := (RadialStack.chain_ordered d.chain).trans_lt hx
  simp only [electricSource,sigma,SourceRadialSystem.extend,if_neg (not_le.mpr hR),if_neg (not_le.mpr hx),sub_self,zero_mul]

theorem source_eq_clipped (d : Data) (hcR : d.c<d.R) (P : Poly) (i : Fin 3) (x : Space) :
    electricSource d P i x=(sigma d ‖x‖-1)*SourceElectricProfiles.electric d P x i := by
  by_cases hx : ‖x‖≤d.R
  · simp only [electricSource,sigma,SourceRadialSystem.extend,if_pos hx,sub_self,zero_mul]
  · have hc : d.c<‖x‖ := hcR.trans (lt_of_not_ge hx)
    have hd : SourceUnclippedMaxwell.reclip d d.c d.hc=d := by cases d;rfl
    have he := SourceUnclippedMaxwell.electric_agrees d d.c d.hc P x hc
    rw [hd] at he
    rw [electricSource,he]

theorem source_memLp (d : Data) (hcR : d.c<d.R) (P : Poly) (i : Fin 3) :
    MemLp (electricSource d P i) 2 volume := by
  let g : Space → ℂ := (closedBall 0 d.X).indicator (fun x => SourceElectricProfiles.electric d P x i)
  have hg : MemLp g 2 volume := (memLp_indicator_iff_restrict measurableSet_closedBall).mpr
    (electric_memLp_ball d P d.X i)
  obtain ⟨M,_,hb⟩ := sigma_bound d
  have hm : Measurable (fun x : Space => sigma d ‖x‖-1) :=
    ((sigma_measurable d).comp continuous_norm.measurable).sub measurable_const
  have hprod : MemLp (fun x => (sigma d ‖x‖-1)*g x) 2 volume := by
    apply hg.of_le_mul (c := M+1) (hm.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    filter_upwards with x
    change ‖(sigma d ‖x‖-1)*g x‖≤(M+1)*‖g x‖
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by simpa only [norm_one] using add_le_add_right (hb ‖x‖) 1)
  apply hprod.ae_eq
  filter_upwards with x
  by_cases hx : x∈closedBall (0 : Space) d.X
  · simp only [g,Set.indicator_of_mem hx]
    exact (source_eq_clipped d hcR P i x).symm
  · simp only [g,Set.indicator_of_not_mem hx,mul_zero]
    exact (source_zero_outer d P i x (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx)).symm

theorem source_compact (d : Data) (P : Poly) (i : Fin 3) : HasCompactSupport (electricSource d P i) := by
  apply HasCompactSupport.intro' (isCompact_closedBall (0 : Space) d.X) isClosed_closedBall
  intro x hx
  exact source_zero_outer d P i x (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx)

theorem source_integrable (d : Data) (hcR : d.c<d.R) (P : Poly) (i : Fin 3) :
    Integrable (electricSource d P i) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) d.X)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 d.X).measure_ne_top
  have hi : IntegrableOn (electricSource d P i) (closedBall 0 d.X) :=
    ((source_memLp d hcR P i).restrict (closedBall 0 d.X)).integrable (by norm_num : (1 : ENNReal)≤2)
  apply hi.integrable_of_forall_not_mem_eq_zero
  intro x hx
  exact source_zero_outer d P i x (by simpa only [mem_closedBall,dist_zero_right,not_le] using hx)

theorem electric_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceElectricProfiles.electric d P x i) :=
  HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => electric_memLp_ball d P T i)

theorem magnetic_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => SourceElectricProfiles.magnetic d P x i) :=
  HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => magnetic_memLp_ball d P T i)

theorem sigma_electric_memLp_ball (d : Data) (P : Poly) (T : ℝ) (i : Fin 3) :
    MemLp (fun x => sigma d ‖x‖*SourceElectricProfiles.electric d P x i) 2 (volume.restrict (closedBall 0 T)) := by
  obtain ⟨M,_,hb⟩ := sigma_bound d
  exact bounded_mul_memLp_ball _ _ ((sigma_measurable d).comp continuous_norm.measurable) M
    (fun x => hb _) T (electric_memLp_ball d P T i)

theorem sigma_electric_locallyIntegrable (d : Data) (P : Poly) (i : Fin 3) :
    LocallyIntegrable (fun x => sigma d ‖x‖*SourceElectricProfiles.electric d P x i) :=
  HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => sigma_electric_memLp_ball d P T i)
end OQ14.SourceLocalBounds



#print axioms OQ14.SourceLocalBounds.select_bound
#print axioms OQ14.SourceLocalBounds.inverseSigma_bound
#print axioms OQ14.SourceLocalBounds.continuous_memLp_ball
#print axioms OQ14.SourceLocalBounds.bounded_mul_memLp_ball
#print axioms OQ14.SourceLocalBounds.electric_memLp_ball
#print axioms OQ14.SourceLocalBounds.magnetic_continuous
#print axioms OQ14.SourceLocalBounds.magnetic_memLp_ball
#print axioms OQ14.SourceLocalBounds.sigmaAt_select
#print axioms OQ14.SourceLocalBounds.sigma_formula
#print axioms OQ14.SourceLocalBounds.sigma_measurable
#print axioms OQ14.SourceLocalBounds.sigma_bound
#print axioms OQ14.SourceLocalBounds.piecewise_memLp_ball
#print axioms OQ14.SourceLocalBounds.source_zero_inner
#print axioms OQ14.SourceLocalBounds.source_zero_outer
#print axioms OQ14.SourceLocalBounds.source_eq_clipped
#print axioms OQ14.SourceLocalBounds.source_memLp
#print axioms OQ14.SourceLocalBounds.source_compact
#print axioms OQ14.SourceLocalBounds.source_integrable
#print axioms OQ14.SourceLocalBounds.electric_locallyIntegrable
#print axioms OQ14.SourceLocalBounds.magnetic_locallyIntegrable
#print axioms OQ14.SourceLocalBounds.sigma_electric_memLp_ball
#print axioms OQ14.SourceLocalBounds.sigma_electric_locallyIntegrable
