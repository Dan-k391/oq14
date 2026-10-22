import ConicalCutoffCurl
import ConicalStaticField
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Actual radial localization and compact annular forcing for the conical static field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalAnnularSource
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ConicalCapField OQ14.ConicalDisplacement
  OQ14.ConicalVectorPotential OQ14.ConicalCutoffGradient OQ14.ConicalCutoffCurl
open scoped Topology ENNReal

def dielectric (χ : ContDiffBump (0 : Space)) (d t : ℝ) (x : Space) : ℝ :=
  by classical exact if x ∈ closedBall (0 : Space) χ.rOut then permittivity d t x else 1

def forcing (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ) (x : Space) : Space :=
  dielectric χ d t x • cutElectric χ ν a t x-cutCurl χ ν a d t x

theorem bump_fderiv_zero_inner (χ : ContDiffBump (0 : Space)) (x : Space)
    (hx : x ∈ ball (0 : Space) χ.rIn) : fderiv ℝ (χ : Space → ℝ) x=0 := by
  classical
  rw [(χ.eventuallyEq_one_of_mem_ball hx).fderiv_eq]
  simp

theorem bump_fderiv_zero_outer (χ : ContDiffBump (0 : Space)) (x : Space)
    (hx : x ∉ closedBall (0 : Space) χ.rOut) : fderiv ℝ (χ : Space → ℝ) x=0 := by
  classical
  apply fderiv_of_not_mem_tsupport ℝ
  rwa [χ.tsupport_eq]

theorem forcing_zero_inner (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ) (x : Space)
    (hx : x ∈ ball (0 : Space) χ.rIn) : forcing χ ν a d t x=0 := by
  classical
  have hx' : x ∈ closedBall (0 : Space) χ.rOut :=
    closedBall_subset_closedBall χ.rIn_lt_rOut.le (ball_subset_closedBall hx)
  have hone : χ x=1 := χ.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hd := bump_fderiv_zero_inner χ x hx
  ext i
  simp only [forcing,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,dielectric,if_pos hx',
    cutElectric,PiLp.add_apply,cutoffGradient_apply,cutCurl_apply,hone,hd,
    ContinuousLinearMap.zero_apply,mul_zero,zero_mul,add_zero,sub_zero,sub_self,PiLp.zero_apply,one_mul,displacement]

theorem forcing_zero_outer (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) χ.rOut) : forcing χ ν a d t x=0 := by
  classical
  have hz : χ x=0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hx))
  have hd := bump_fderiv_zero_outer χ x hx
  ext i
  simp only [forcing,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,
    cutElectric,PiLp.add_apply,cutoffGradient_apply,cutCurl_apply,hz,hd,
    ContinuousLinearMap.zero_apply,mul_zero,zero_mul,add_zero,sub_self,PiLp.zero_apply]

theorem forcing_tsupport_subset (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ) :
    tsupport (forcing χ ν a d t) ⊆ closedBall (0 : Space) χ.rOut \ ball (0 : Space) χ.rIn := by
  classical
  apply closure_minimal _ (isClosed_closedBall.inter isOpen_ball.isClosed_compl)
  intro x hx
  constructor
  · by_contra hn
    exact hx (forcing_zero_outer χ ν a d t x hn)
  · intro hn
    exact hx (forcing_zero_inner χ ν a d t x hn)

theorem forcing_compact (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ) :
    HasCompactSupport (forcing χ ν a d t) :=
  (isCompact_closedBall (0 : Space) χ.rOut).of_isClosed_subset isClosed_closure
    (fun _ hx => (forcing_tsupport_subset χ ν a d t hx).1)

theorem permittivity_measurable (d t : ℝ) : Measurable (permittivity d t) := by
  classical
  have hm : Measurable (fun x : Space => (unit x : Space) 2) :=
    (ConicalAngularTrial.coordinate_continuous 2).measurable.comp unit_measurable
  exact measurable_const.piecewise
    (measurableSet_le (continuous_abs.measurable.comp hm) measurable_const) measurable_const

theorem dielectric_measurable (χ : ContDiffBump (0 : Space)) (d t : ℝ) :
    Measurable (dielectric χ d t) :=
  (permittivity_measurable d t).piecewise measurableSet_closedBall measurable_const

theorem dielectric_bounds (χ : ContDiffBump (0 : Space)) (d t : ℝ) (hd : 0 ≤ d) (x : Space) :
    1 ≤ dielectric χ d t x ∧ dielectric χ d t x ≤ 1+d := by
  classical
  unfold dielectric
  split_ifs
  · exact ConicalStaticField.permittivity_bounds d t hd x
  · constructor <;> linarith

private theorem bounded_mul_memLp (μ : Measure Space) (f g : Space → ℝ)
    (hf : MemLp f 2 μ) (hg : Measurable g) (M : ℝ) (hb : ∀ᵐ x ∂μ, ‖g x‖ ≤ M) :
    MemLp (fun x => g x*f x) 2 μ := by
  classical
  apply hf.of_le_mul (hg.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards [hb] with x hx
  change ‖g x*f x‖ ≤ M*‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem local_cutoff_memLp (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    : ∀ i : Fin 3,
      MemLp (fun x => cutElectric χ ν a t x i) 2 (volume.restrict (closedBall (0 : Space) χ.rOut)) ∧
      MemLp (fun x => cutCurl χ ν a d t x i) 2 (volume.restrict (closedBall (0 : Space) χ.rOut)) := by
  classical
  let μ : Measure Space := volume.restrict (closedBall (0 : Space) χ.rOut)
  have hχ : ContDiff ℝ 1 (χ : Space → ℝ) := χ.contDiff
  have hmem : ∀ᵐ x ∂μ, x ∈ closedBall (0 : Space) χ.rOut := ae_restrict_mem measurableSet_closedBall
  have hU : MemLp (potential ν a t) 2 μ := potential_memLp_two_ball ν a t χ.rOut hν ha ht ht1
  have hE (j : Fin 3) : MemLp (fun x => electric ν a t x j) 2 μ :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).comp_memLp'
      (electric_memLp_two_ball ν a t χ.rOut hν ha ht ht1)
  have hε (x : Space) : ‖permittivity d t x‖ ≤ 1+d := by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) (ConicalStaticField.permittivity_bounds d t hd x).1)]
    exact (ConicalStaticField.permittivity_bounds d t hd x).2
  have hD (j : Fin 3) : MemLp (fun x => displacement ν a d t x j) 2 μ := by
    simpa only [displacement,PiLp.smul_apply,smul_eq_mul] using
      bounded_mul_memLp μ _ _ (hE j) (permittivity_measurable d t) (1+d)
        (Filter.Eventually.of_forall hε)
  have hX (j k : Fin 3) : MemLp (fun x : Space => x j*displacement ν a d t x k) 2 μ := by
    apply bounded_mul_memLp μ _ _ (hD k)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous.measurable χ.rOut
    filter_upwards [hmem] with x hx
    exact (PiLp.norm_apply_le x j).trans (by simpa only [mem_closedBall,dist_zero_right] using hx)
  have hCross (j : Fin 3) : MemLp (fun x => crossPosition ν a d t x j) 2 μ := by
    simpa only [crossPosition_apply] using (hX (WeakCurl.next j) (WeakCurl.previous j)).sub
      (hX (WeakCurl.previous j) (WeakCurl.next j))
  have hA (j : Fin 3) : MemLp (fun x => vectorPotential ν a d t x j) 2 μ := by
    simpa only [vectorPotential,PiLp.smul_apply,smul_eq_mul] using (hCross j).const_mul (-(ν+1)⁻¹)
  have hMulχ (f : Space → ℝ) (hf : MemLp f 2 μ) : MemLp (fun x => χ x*f x) 2 μ := by
    apply bounded_mul_memLp μ f χ hf hχ.continuous.measurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
      exact χ.le_one)
  have hMulD (j : Fin 3) (f : Space → ℝ) (hf : MemLp f 2 μ) :
      MemLp (fun x => fderiv ℝ (χ : Space → ℝ) x (basis j)*f x) 2 μ := by
    have hcD : Continuous (fun x : Space => fderiv ℝ (χ : Space → ℝ) x (basis j)) :=
      (hχ.continuous_fderiv le_rfl).clm_apply continuous_const
    obtain ⟨C,hC⟩ := (χ.hasCompactSupport.fderiv_apply ℝ (basis j)).exists_bound_of_continuous hcD
    exact bounded_mul_memLp μ f _ hf hcD.measurable C (Filter.Eventually.of_forall hC)
  have hcutE (j : Fin 3) : MemLp (fun x => cutElectric χ ν a t x j) 2 μ := by
    simpa only [cutElectric,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,cutoffGradient_apply,mul_comm]
      using (hMulχ _ (hE j)).add (hMulD j _ hU)
  have hcutC (j : Fin 3) : MemLp (fun x => cutCurl χ ν a d t x j) 2 μ := by
    simpa only [cutCurl_apply] using
      ((hMulχ _ (hD j)).add (hMulD (WeakCurl.next j) _ (hA (WeakCurl.previous j)))).sub
        (hMulD (WeakCurl.previous j) _ (hA (WeakCurl.next j)))
  exact fun j => ⟨hcutE j,hcutC j⟩

theorem cutElectric_zero_outer (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) χ.rOut) : cutElectric χ ν a t x=0 := by
  have hz : χ x=0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hx))
  have hd := bump_fderiv_zero_outer χ x hx
  ext i
  simp only [cutElectric,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,cutoffGradient_apply,
    hz,hd,ContinuousLinearMap.zero_apply,zero_mul,mul_zero,add_zero,PiLp.zero_apply]

theorem cutCurl_zero_outer (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) χ.rOut) : cutCurl χ ν a d t x=0 := by
  have hz : χ x=0 := χ.zero_of_le_dist (le_of_lt (not_le.mp hx))
  have hd := bump_fderiv_zero_outer χ x hx
  ext i
  simp only [cutCurl_apply,hz,hd,ContinuousLinearMap.zero_apply,zero_mul,add_zero,sub_zero,PiLp.zero_apply]

private theorem memLp_of_restrict_zero (S : Set Space) (hS : MeasurableSet S) (f : Space → ℝ)
    (hf : MemLp f 2 (volume.restrict S)) (hz : ∀ x ∉ S, f x=0) : MemLp f 2 volume := by
  classical
  have hInd : MemLp (S.indicator f) 2 volume := (memLp_indicator_iff_restrict hS).mpr hf
  have he : S.indicator f=f := by
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · rw [indicator_of_not_mem hx,hz x hx]
  rwa [he] at hInd

theorem cutElectric_component_memLp (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    MemLp (fun x => cutElectric χ ν a t x i) 2 (volume : Measure Space) := by
  apply memLp_of_restrict_zero _ measurableSet_closedBall _
    (local_cutoff_memLp χ ν a 0 t hν ha (by norm_num) ht ht1 i).1
  intro x hx
  rw [cutElectric_zero_outer χ ν a t x hx]
  rfl

theorem cutCurl_component_memLp (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (i : Fin 3) : MemLp (fun x => cutCurl χ ν a d t x i) 2 (volume : Measure Space) := by
  apply memLp_of_restrict_zero _ measurableSet_closedBall _
    (local_cutoff_memLp χ ν a d t hν ha hd ht ht1 i).2
  intro x hx
  rw [cutCurl_zero_outer χ ν a d t x hx]
  rfl

theorem forcing_component_memLp (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (i : Fin 3) : MemLp (fun x => forcing χ ν a d t x i) 2 (volume : Measure Space) := by
  have hεg (x : Space) : ‖dielectric χ d t x‖ ≤ 1+d := by
    rw [Real.norm_eq_abs,abs_of_nonneg (le_trans (by norm_num) (dielectric_bounds χ d t hd x).1)]
    exact (dielectric_bounds χ d t hd x).2
  simpa only [forcing,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] using
    (bounded_mul_memLp volume _ _ (cutElectric_component_memLp χ ν a t hν ha ht ht1 i)
      (dielectric_measurable χ d t) (1+d) (Filter.Eventually.of_forall hεg)).sub
        (cutCurl_component_memLp χ ν a d t hν ha hd ht ht1 i)

end OQ14.ConicalAnnularSource

#print axioms OQ14.ConicalAnnularSource.bump_fderiv_zero_inner
#print axioms OQ14.ConicalAnnularSource.bump_fderiv_zero_outer
#print axioms OQ14.ConicalAnnularSource.forcing_zero_inner
#print axioms OQ14.ConicalAnnularSource.forcing_zero_outer
#print axioms OQ14.ConicalAnnularSource.forcing_tsupport_subset
#print axioms OQ14.ConicalAnnularSource.forcing_compact
#print axioms OQ14.ConicalAnnularSource.permittivity_measurable
#print axioms OQ14.ConicalAnnularSource.dielectric_measurable
#print axioms OQ14.ConicalAnnularSource.dielectric_bounds
#print axioms OQ14.ConicalAnnularSource.local_cutoff_memLp
#print axioms OQ14.ConicalAnnularSource.cutElectric_zero_outer
#print axioms OQ14.ConicalAnnularSource.cutCurl_zero_outer
#print axioms OQ14.ConicalAnnularSource.cutElectric_component_memLp
#print axioms OQ14.ConicalAnnularSource.cutCurl_component_memLp
#print axioms OQ14.ConicalAnnularSource.forcing_component_memLp
