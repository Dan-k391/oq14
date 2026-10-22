import ConicalPotentialSplit
import ConicalGraphApproximation

/-! Genuine compact L2 weak-gradient graph of the actual Maxwell scalar potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalPotentialGraph
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume
  OQ14.ConicalPotentialSplit OQ14.WeakGreen OQ14.WeakCurl OQ14.PartialSmoothing OQ14.DivCurlCompact
open scoped Topology SchwartzMap

abbrev Space := Maxwell.Space

def bump (p : Data) (x : Space) : ℂ := (p.cutoff x : ℂ)

private theorem bump_regular (p : Data) : ContDiff ℝ (⊤ : ℕ∞) (bump p) :=
  Complex.ofRealCLM.contDiff.comp p.cutoff.contDiff

private theorem bump_compact (p : Data) : HasCompactSupport (bump p) :=
  p.cutoff.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

private theorem bump_tsupport (p : Data) : tsupport (bump p)=closedBall (0 : Space) p.cutoff.rOut := by
  have he : Function.support (bump p)=Function.support (p.cutoff : Space → ℝ) := by
    ext x
    exact not_congr Complex.ofReal_eq_zero
  rw [tsupport,he,← p.cutoff.tsupport_eq]
  rfl

private theorem bump_zero_outer (p : Data) (x : Space) (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) : bump p x=0 := by
  simp only [bump,p.cutoff.zero_of_le_dist (le_of_lt (not_le.mp hx)),Complex.ofReal_zero]

private theorem derivative_zero_outer (p : Data) (x : Space) (hx : x ∉ closedBall (0 : Space) p.cutoff.rOut) (i : Fin 3) :
    dcoord (bump p) x i=0 := by
  have hn : x ∉ tsupport (bump p) := by rwa [bump_tsupport]
  simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hn,ContinuousLinearMap.zero_apply]

def restrictedL2 (R : ℝ) (f : Space → ℂ) (hf : MemLp f 2 (volume.restrict (closedBall (0 : Space) R))) : L2Scalar :=
  ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr hf).toLp ((closedBall (0 : Space) R).indicator f)

private theorem restrictedL2_ae (R : ℝ) (f : Space → ℂ) (hf : MemLp f 2 (volume.restrict (closedBall (0 : Space) R))) :
    (restrictedL2 R f hf : Space → ℂ) =ᵐ[volume] (closedBall (0 : Space) R).indicator f :=
  ((memLp_indicator_iff_restrict measurableSet_closedBall).mpr hf).coeFn_toLp

private theorem scale_restricted_ae (R : ℝ) (f : Space → ℂ) (hf : MemLp f 2 (volume.restrict (closedBall (0 : Space) R)))
    (g : Space → ℂ) (hg : Continuous g) (hc : HasCompactSupport g)
    (hz : ∀ x ∉ closedBall (0 : Space) R, g x=0) :
    (scaleL2 g hg hc (restrictedL2 R f hf) : Space → ℂ) =ᵐ[volume] fun x => g x*f x := by
  filter_upwards [scaleL2_ae g hg hc (restrictedL2 R f hf),restrictedL2_ae R f hf] with x hs hr
  rw [hs,hr]
  by_cases hx : x ∈ closedBall (0 : Space) R
  · rw [indicator_of_mem hx]
  · simp only [indicator_of_not_mem hx,hz x hx,zero_mul,mul_zero]

def value (p : Data) (k : ℝ) : L2Scalar :=
  scaleL2 (bump p) (bump_regular p).continuous (bump_compact p)
    (restrictedL2 p.cutoff.rOut (potential p k) (potential_memLp p k p.cutoff.rOut))

def gradient (p : Data) (k : ℝ) (i : Fin 3) : L2Scalar :=
  scaleL2 (bump p) (bump_regular p).continuous (bump_compact p)
    (restrictedL2 p.cutoff.rOut (fun x => ConicalSpatialMaxwell.electric p k x i-correction p k x i)
      (gradient_memLp p k p.cutoff.rOut i))+
  scaleL2 (fun x => dcoord (bump p) x i) (partial_continuous ((bump_regular p).of_le (by simp)) i)
    ((bump_compact p).fderiv_apply ℝ (basis i))
    (restrictedL2 p.cutoff.rOut (potential p k) (potential_memLp p k p.cutoff.rOut))

theorem value_ae (p : Data) (k : ℝ) : (value p k : Space → ℂ) =ᵐ[volume]
    fun x => bump p x*potential p k x :=
  scale_restricted_ae _ _ _ _ (bump_regular p).continuous (bump_compact p) (bump_zero_outer p)

theorem gradient_ae (p : Data) (k : ℝ) (i : Fin 3) : (gradient p k i : Space → ℂ) =ᵐ[volume]
    fun x => bump p x*(ConicalSpatialMaxwell.electric p k x i-correction p k x i)+dcoord (bump p) x i*potential p k x := by
  have hv := scale_restricted_ae p.cutoff.rOut _ (gradient_memLp p k p.cutoff.rOut i)
    (bump p) (bump_regular p).continuous (bump_compact p) (bump_zero_outer p)
  have hd := scale_restricted_ae p.cutoff.rOut _ (potential_memLp p k p.cutoff.rOut)
    (fun x => dcoord (bump p) x i) (partial_continuous ((bump_regular p).of_le (by simp)) i)
    ((bump_compact p).fderiv_apply ℝ (basis i)) (fun x hx => derivative_zero_outer p x hx i)
  let A : L2Scalar := scaleL2 (bump p) (bump_regular p).continuous (bump_compact p)
    (restrictedL2 p.cutoff.rOut (fun x => ConicalSpatialMaxwell.electric p k x i-correction p k x i)
      (gradient_memLp p k p.cutoff.rOut i))
  let B : L2Scalar := scaleL2 (fun x => dcoord (bump p) x i)
    (partial_continuous ((bump_regular p).of_le (by simp)) i) ((bump_compact p).fderiv_apply ℝ (basis i))
    (restrictedL2 p.cutoff.rOut (potential p k) (potential_memLp p k p.cutoff.rOut))
  filter_upwards [hv,hd,Lp.coeFn_add A B] with x hv hd ha
  change (A+B) x=_
  rw [ha]
  exact congrArg₂ (fun a b : ℂ => a+b) hv hd

private theorem locallyIntegrable_of_balls (f : Space → ℂ)
    (hf : ∀ R : ℝ, MemLp f 2 (volume.restrict (closedBall (0 : Space) R))) : LocallyIntegrable f := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R,hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Space) R).measure_ne_top
  have hi : IntegrableOn f (closedBall (0 : Space) R) := (hf R).integrable (by norm_num)
  exact hi.mono_set hR

private theorem locallyIntegrable_mul_compact (f g : Space → ℂ) (hf : LocallyIntegrable f)
    (hg : Continuous g) (hc : HasCompactSupport g) : Integrable (fun x => f x*g x) := by
  have hi : IntegrableOn (fun x => f x*g x) (tsupport g) :=
    (hf.integrableOn_isCompact hc).mul_continuousOn hg.continuousOn hc
  have hInd : Integrable ((tsupport g).indicator (fun x => f x*g x)) :=
    (integrable_indicator_iff hc.measurableSet).mpr hi
  have he : (tsupport g).indicator (fun x => f x*g x)=(fun x => f x*g x) := by
    funext x
    by_cases hx : x ∈ tsupport g
    · rw [indicator_of_mem hx]
    · simp only [indicator_of_not_mem hx,image_eq_zero_of_nmem_tsupport hx,mul_zero]
  rwa [he] at hInd

theorem gradient_schwartz (p : Data) (k : ℝ) (i : Fin 3) (ψ : 𝓢(Space,ℂ)) :
    (∫ x : Space, gradient p k i x*ψ x)=-(∫ x : Space, value p k x*dcoord ψ x i) := by
  have hV := locallyIntegrable_of_balls (potential p k) (potential_memLp p k)
  have hG := locallyIntegrable_of_balls (fun x => ConicalSpatialMaxwell.electric p k x i-correction p k x i)
    (fun R => gradient_memLp p k R i)
  have hχ := (bump_regular p).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hψ : ContDiff ℝ 1 (ψ : Space → ℂ) := ψ.smooth 1
  have hiA : Integrable (fun x : Space => potential p k x*(bump p x*dcoord ψ x i)) := by
    exact locallyIntegrable_mul_compact _ _ hV
      (hχ.continuous.mul (partial_continuous hψ i)) (bump_compact p).mul_right
  have hiB : Integrable (fun x : Space => potential p k x*(ψ x*dcoord (bump p) x i)) := by
    exact locallyIntegrable_mul_compact _ _ hV
      (ψ.continuous.mul (partial_continuous hχ i)) ((bump_compact p).fderiv_apply ℝ (basis i)).mul_left
  have hiC : Integrable (fun x : Space => (ConicalSpatialMaxwell.electric p k x i-correction p k x i)*(bump p x*ψ x)) := by
    exact locallyIntegrable_mul_compact _ _ hG
      (hχ.continuous.mul ψ.continuous) (bump_compact p).mul_right
  let f : 𝓢(Space,ℂ) := FourierL2.compactSmoothSchwartz (fun x => bump p x*ψ x)
    ((bump_regular p).mul (ψ.smooth (⊤ : ℕ∞))) (bump_compact p).mul_right
  have h := potential_weak_gradient p k i ⟨f,(bump_compact p).mul_right⟩
  change (∫ x : Space, potential p k x*dcoord (fun y => bump p y*ψ y) x i)=
    -(∫ x : Space, (ConicalSpatialMaxwell.electric p k x i-correction p k x i)*(bump p x*ψ x)) at h
  have he : (fun x : Space => potential p k x*dcoord (fun y => bump p y*ψ y) x i)=
      fun x => potential p k x*(bump p x*dcoord ψ x i)+potential p k x*(ψ x*dcoord (bump p) x i) := by
    funext x
    rw [partial_mul (hχ.differentiable le_rfl x) (hψ.differentiable le_rfl x) i]
    ring
  rw [he,integral_add hiA hiB] at h
  have hL : (∫ x : Space, gradient p k i x*ψ x)=
      (∫ x : Space, (ConicalSpatialMaxwell.electric p k x i-correction p k x i)*(bump p x*ψ x))+
      ∫ x : Space, potential p k x*(ψ x*dcoord (bump p) x i) := by
    rw [← integral_add hiC hiB]
    apply integral_congr_ae
    filter_upwards [gradient_ae p k i] with x hx
    rw [hx]
    ring
  have hR : (∫ x : Space, value p k x*dcoord ψ x i)=
      ∫ x : Space, potential p k x*(bump p x*dcoord ψ x i) := by
    apply integral_congr_ae
    filter_upwards [value_ae p k] with x hx
    rw [hx]
    ring
  rw [hL,hR]
  linear_combination h

theorem hasWeakPartial (p : Data) (k : ℝ) (i : Fin 3) :
    HasWeakPartial (value p k) (gradient p k i) i := by
  apply hasWeakPartial_of_schwartz_integral i
  intro ψ
  rw [gradient_schwartz]
  exact neg_add_cancel _

theorem value_compact (p : Data) (k : ℝ) : CompactRepresentative (value p k) :=
  ⟨_,(bump_compact p).mul_right,value_ae p k⟩

theorem bump_inner (p : Data) (x : Space) (hx : x ∈ ball (0 : Space) p.cutoff.rIn) :
    bump p x=1 ∧ ∀ i : Fin 3, dcoord (bump p) x i=0 := by
  have h : bump p =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [p.cutoff.eventuallyEq_one_of_mem_ball hx] with y hy
    simp only [bump,hy,Pi.one_apply,Complex.ofReal_one]
  refine ⟨h.eq_of_nhds,fun i => ?_⟩
  simp only [dcoord,h.fderiv_eq,fderiv_const,Pi.zero_apply,ContinuousLinearMap.zero_apply]

end OQ14.ConicalPotentialGraph

#print axioms OQ14.ConicalPotentialGraph.value_ae
#print axioms OQ14.ConicalPotentialGraph.gradient_ae
#print axioms OQ14.ConicalPotentialGraph.gradient_schwartz
#print axioms OQ14.ConicalPotentialGraph.hasWeakPartial
#print axioms OQ14.ConicalPotentialGraph.value_compact
#print axioms OQ14.ConicalPotentialGraph.bump_inner
