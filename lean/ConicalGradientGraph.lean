import ConicalSeparatedPotential
import ConicalGraphApproximation

/-! Actual localization of a locally L2 weak scalar gradient into a compact global L2 graph. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
namespace OQ14.ConicalGradientGraph
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.WeakGreen OQ14.WeakCurl
  OQ14.PartialSmoothing OQ14.DivCurlCompact
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space

structure PotentialData where
  potential : Space → ℂ
  derivative : Fin 3 → Space → ℂ
  potential_memLp : ∀ R : ℝ, MemLp potential 2 (volume.restrict (closedBall (0 : Space) R))
  derivative_memLp : ∀ (R : ℝ) (i : Fin 3), MemLp (derivative i) 2 (volume.restrict (closedBall (0 : Space) R))
  weak : ∀ (i : Fin 3) (f : DynamicSource.Test),
    (∫ x, potential x*(DynamicSource.testPartial i f).val x)=-(∫ x, derivative i x*f.val x)

structure Graph where
  value : L2Scalar
  gradient : Fin 3 → L2Scalar
  weak : ∀ i, HasWeakPartial value (gradient i) i

def bump (χ : ContDiffBump (0 : Space)) (x : Space) : ℂ := (χ x : ℂ)

private theorem bump_regular (χ : ContDiffBump (0 : Space)) : ContDiff ℝ (⊤ : ℕ∞) (bump χ) :=
  Complex.ofRealCLM.contDiff.comp χ.contDiff

private theorem bump_compact (χ : ContDiffBump (0 : Space)) : HasCompactSupport (bump χ) :=
  χ.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)

private theorem bump_tsupport (χ : ContDiffBump (0 : Space)) : tsupport (bump χ)=closedBall (0 : Space) χ.rOut := by
  have he : Function.support (bump χ)=Function.support (χ : Space → ℝ) := by
    ext x
    exact not_congr Complex.ofReal_eq_zero
  rw [tsupport,he,← χ.tsupport_eq]
  rfl

private theorem bump_zero_outer (χ : ContDiffBump (0 : Space)) (x : Space) (hx : x ∉ closedBall (0 : Space) χ.rOut) : bump χ x=0 := by
  simp only [bump,χ.zero_of_le_dist (le_of_lt (not_le.mp hx)),Complex.ofReal_zero]

private theorem derivative_zero_outer (χ : ContDiffBump (0 : Space)) (x : Space) (hx : x ∉ closedBall (0 : Space) χ.rOut) (i : Fin 3) :
    dcoord (bump χ) x i=0 := by
  have hn : x ∉ tsupport (bump χ) := by rwa [bump_tsupport]
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

def value (χ : ContDiffBump (0 : Space)) (u : PotentialData) : L2Scalar :=
  scaleL2 (bump χ) (bump_regular χ).continuous (bump_compact χ)
    (restrictedL2 χ.rOut (u.potential) (u.potential_memLp χ.rOut))

def gradient (χ : ContDiffBump (0 : Space)) (u : PotentialData) (i : Fin 3) : L2Scalar :=
  scaleL2 (bump χ) (bump_regular χ).continuous (bump_compact χ)
    (restrictedL2 χ.rOut (fun x => u.derivative i x)
      (u.derivative_memLp χ.rOut i))+
  scaleL2 (fun x => dcoord (bump χ) x i) (partial_continuous ((bump_regular χ).of_le (by simp)) i)
    ((bump_compact χ).fderiv_apply ℝ (basis i))
    (restrictedL2 χ.rOut (u.potential) (u.potential_memLp χ.rOut))

theorem value_ae (χ : ContDiffBump (0 : Space)) (u : PotentialData) : (value χ u : Space → ℂ) =ᵐ[volume]
    fun x => bump χ x*u.potential x :=
  scale_restricted_ae _ _ _ _ (bump_regular χ).continuous (bump_compact χ) (bump_zero_outer χ)

theorem gradient_ae (χ : ContDiffBump (0 : Space)) (u : PotentialData) (i : Fin 3) : (gradient χ u i : Space → ℂ) =ᵐ[volume]
    fun x => bump χ x*(u.derivative i x)+dcoord (bump χ) x i*u.potential x := by
  have hv := scale_restricted_ae χ.rOut _ (u.derivative_memLp χ.rOut i)
    (bump χ) (bump_regular χ).continuous (bump_compact χ) (bump_zero_outer χ)
  have hd := scale_restricted_ae χ.rOut _ (u.potential_memLp χ.rOut)
    (fun x => dcoord (bump χ) x i) (partial_continuous ((bump_regular χ).of_le (by simp)) i)
    ((bump_compact χ).fderiv_apply ℝ (basis i)) (fun x hx => derivative_zero_outer χ x hx i)
  let A : L2Scalar := scaleL2 (bump χ) (bump_regular χ).continuous (bump_compact χ)
    (restrictedL2 χ.rOut (fun x => u.derivative i x)
      (u.derivative_memLp χ.rOut i))
  let B : L2Scalar := scaleL2 (fun x => dcoord (bump χ) x i)
    (partial_continuous ((bump_regular χ).of_le (by simp)) i) ((bump_compact χ).fderiv_apply ℝ (basis i))
    (restrictedL2 χ.rOut (u.potential) (u.potential_memLp χ.rOut))
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

theorem gradient_schwartz (χ : ContDiffBump (0 : Space)) (u : PotentialData) (i : Fin 3) (ψ : 𝓢(Space,ℂ)) :
    (∫ x : Space, gradient χ u i x*ψ x)=-(∫ x : Space, value χ u x*dcoord ψ x i) := by
  have hV := locallyIntegrable_of_balls (u.potential) (u.potential_memLp)
  have hG := locallyIntegrable_of_balls (fun x => u.derivative i x)
    (fun R => u.derivative_memLp R i)
  have hχ := (bump_regular χ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hψ : ContDiff ℝ 1 (ψ : Space → ℂ) := ψ.smooth 1
  have hiA : Integrable (fun x : Space => u.potential x*(bump χ x*dcoord ψ x i)) := by
    exact locallyIntegrable_mul_compact _ _ hV
      (hχ.continuous.mul (partial_continuous hψ i)) (bump_compact χ).mul_right
  have hiB : Integrable (fun x : Space => u.potential x*(ψ x*dcoord (bump χ) x i)) := by
    exact locallyIntegrable_mul_compact _ _ hV
      (ψ.continuous.mul (partial_continuous hχ i)) ((bump_compact χ).fderiv_apply ℝ (basis i)).mul_left
  have hiC : Integrable (fun x : Space => (u.derivative i x)*(bump χ x*ψ x)) := by
    exact locallyIntegrable_mul_compact _ _ hG
      (hχ.continuous.mul ψ.continuous) (bump_compact χ).mul_right
  let f : 𝓢(Space,ℂ) := FourierL2.compactSmoothSchwartz (fun x => bump χ x*ψ x)
    ((bump_regular χ).mul (ψ.smooth (⊤ : ℕ∞))) (bump_compact χ).mul_right
  have h := u.weak i ⟨f,(bump_compact χ).mul_right⟩
  change (∫ x : Space, u.potential x*dcoord (fun y => bump χ y*ψ y) x i)=
    -(∫ x : Space, (u.derivative i x)*(bump χ x*ψ x)) at h
  have he : (fun x : Space => u.potential x*dcoord (fun y => bump χ y*ψ y) x i)=
      fun x => u.potential x*(bump χ x*dcoord ψ x i)+u.potential x*(ψ x*dcoord (bump χ) x i) := by
    funext x
    rw [partial_mul (hχ.differentiable le_rfl x) (hψ.differentiable le_rfl x) i]
    ring
  rw [he,integral_add hiA hiB] at h
  have hL : (∫ x : Space, gradient χ u i x*ψ x)=
      (∫ x : Space, (u.derivative i x)*(bump χ x*ψ x))+
      ∫ x : Space, u.potential x*(ψ x*dcoord (bump χ) x i) := by
    rw [← integral_add hiC hiB]
    apply integral_congr_ae
    filter_upwards [gradient_ae χ u i] with x hx
    rw [hx]
    ring
  have hR : (∫ x : Space, value χ u x*dcoord ψ x i)=
      ∫ x : Space, u.potential x*(bump χ x*dcoord ψ x i) := by
    apply integral_congr_ae
    filter_upwards [value_ae χ u] with x hx
    rw [hx]
    ring
  rw [hL,hR]
  linear_combination h

theorem hasWeakPartial (χ : ContDiffBump (0 : Space)) (u : PotentialData) (i : Fin 3) :
    HasWeakPartial (value χ u) (gradient χ u i) i := by
  apply hasWeakPartial_of_schwartz_integral i
  intro ψ
  rw [gradient_schwartz]
  exact neg_add_cancel _

theorem value_compact (χ : ContDiffBump (0 : Space)) (u : PotentialData) : CompactRepresentative (value χ u) :=
  ⟨_,(bump_compact χ).mul_right,value_ae χ u⟩

theorem bump_inner (χ : ContDiffBump (0 : Space)) (x : Space) (hx : x ∈ ball (0 : Space) χ.rIn) :
    bump χ x=1 ∧ ∀ i : Fin 3, dcoord (bump χ) x i=0 := by
  have h : bump χ =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
    filter_upwards [χ.eventuallyEq_one_of_mem_ball hx] with y hy
    simp only [bump,hy,Pi.one_apply,Complex.ofReal_one]
  refine ⟨h.eq_of_nhds,fun i => ?_⟩
  simp only [dcoord,h.fderiv_eq,fderiv_const,Pi.zero_apply,ContinuousLinearMap.zero_apply]

def ofPotential (χ : ContDiffBump (0 : Space)) (u : PotentialData) : Graph :=
  ⟨value χ u,gradient χ u,hasWeakPartial χ u⟩

def separatedPotential (p : ConicalStaticVolume.Data) (a k : ℝ) (hai : a < p.cutoff.rIn) : PotentialData where
  potential := ConicalSeparatedPotential.potential p a k
  derivative i x := ConicalSeparatedMaxwell.electric p a k x i-ConicalSeparatedPotential.correction p a k x i
  potential_memLp R := ConicalSeparatedPotential.potential_memLp p a k R hai
  derivative_memLp R i := ConicalSeparatedPotential.gradient_memLp p a k R hai i
  weak := ConicalSeparatedPotential.potential_weak_gradient p a k hai

def separated (p : ConicalStaticVolume.Data) (a k : ℝ) (hai : a < p.cutoff.rIn) : Graph :=
  ofPotential p.cutoff (separatedPotential p a k hai)

theorem separated_value_ae (p : ConicalStaticVolume.Data) (a k : ℝ) (hai : a < p.cutoff.rIn) :
    ((separated p a k hai).value : Space → ℂ) =ᵐ[volume]
      fun x => bump p.cutoff x*ConicalSeparatedPotential.potential p a k x :=
  value_ae p.cutoff (separatedPotential p a k hai)

theorem separated_gradient_ae (p : ConicalStaticVolume.Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    ((separated p a k hai).gradient i : Space → ℂ) =ᵐ[volume]
      fun x => bump p.cutoff x*(ConicalSeparatedMaxwell.electric p a k x i-ConicalSeparatedPotential.correction p a k x i)+
        dcoord (bump p.cutoff) x i*ConicalSeparatedPotential.potential p a k x :=
  gradient_ae p.cutoff (separatedPotential p a k hai) i

theorem separated_weakPartial (p : ConicalStaticVolume.Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (i : Fin 3) :
    HasWeakPartial (separated p a k hai).value ((separated p a k hai).gradient i) i :=
  (separated p a k hai).weak i

end OQ14.ConicalGradientGraph

#print axioms OQ14.ConicalGradientGraph.value_ae
#print axioms OQ14.ConicalGradientGraph.gradient_ae
#print axioms OQ14.ConicalGradientGraph.gradient_schwartz
#print axioms OQ14.ConicalGradientGraph.hasWeakPartial
#print axioms OQ14.ConicalGradientGraph.value_compact
#print axioms OQ14.ConicalGradientGraph.bump_inner

#print axioms OQ14.ConicalGradientGraph.separated_value_ae
#print axioms OQ14.ConicalGradientGraph.separated_gradient_ae
#print axioms OQ14.ConicalGradientGraph.separated_weakPartial
