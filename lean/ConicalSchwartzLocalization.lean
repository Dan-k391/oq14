import ConicalComplexLocalization
import GradientProjection

/-! Genuine Schwartz weak identities for compact conical localization. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalSchwartzLocalization
open MeasureTheory Metric Set OQ14.Maxwell OQ14.ConicalCapField OQ14.ConicalCutoffGradient
  OQ14.ConicalCutoffCurl OQ14.ConicalAnnularSource OQ14.ConicalComplexLocalization
open scoped Topology SchwartzMap

private def largerBump (χ : ContDiffBump (0 : Space)) : ContDiffBump (0 : Space) :=
  ⟨χ.rOut+1,χ.rOut+2,by linarith [χ.rOut_pos],by linarith⟩

private def localTest (χ : ContDiffBump (0 : Space)) (ψ : Space → ℂ) (x : Space) : ℂ :=
  (largerBump χ x : ℂ)*ψ x

private theorem localTest_regular (χ : ContDiffBump (0 : Space)) (ψ : 𝓢(Space,ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (localTest χ ψ) :=
  (Complex.ofRealCLM.contDiff.comp (largerBump χ).contDiff).mul (ψ.smooth (⊤ : ℕ∞))

private theorem localTest_compact (χ : ContDiffBump (0 : Space)) (ψ : Space → ℂ) :
    HasCompactSupport (localTest χ ψ) :=
  ((largerBump χ).hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).mul_right

private theorem localTest_germ (χ : ContDiffBump (0 : Space)) (ψ : Space → ℂ) (x : Space)
    (hx : x ∈ closedBall (0 : Space) χ.rOut) : localTest χ ψ =ᶠ[nhds x] ψ := by
  have hx' : x ∈ ball (0 : Space) (largerBump χ).rIn := by
    simp only [mem_ball,dist_zero_right,largerBump]
    have hn : ‖x‖ ≤ χ.rOut := by simpa only [mem_closedBall,dist_zero_right] using hx
    linarith
  filter_upwards [(largerBump χ).eventuallyEq_one_of_mem_ball hx'] with y hy
  simp only [localTest,hy,Pi.one_apply,Complex.ofReal_one,one_mul]

private theorem value_pair_local (χ : ContDiffBump (0 : Space)) (F ψ : Space → ℂ)
    (hz : ∀ x ∉ closedBall (0 : Space) χ.rOut, F x=0) :
    (∫ x : Space, F x*localTest χ ψ x)=∫ x : Space, F x*ψ x := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) χ.rOut
  · rw [(localTest_germ χ ψ x hx).eq_of_nhds]
  · rw [hz x hx,zero_mul,zero_mul]

private theorem derivative_pair_local (χ : ContDiffBump (0 : Space)) (F ψ : Space → ℂ)
    (hz : ∀ x ∉ closedBall (0 : Space) χ.rOut, F x=0) (i : Fin 3) :
    (∫ x : Space, F x*dcoord (localTest χ ψ) x i)=∫ x : Space, F x*dcoord ψ x i := by
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ closedBall (0 : Space) χ.rOut
  · unfold dcoord
    rw [(localTest_germ χ ψ x hx).fderiv_eq]
  · rw [hz x hx,zero_mul,zero_mul]

private theorem cutPotential_zero_outer (χ : ContDiffBump (0 : Space)) (ν a t : ℝ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) χ.rOut) : cutPotential χ ν a t x=0 := by
  rw [cutPotential,χ.zero_of_le_dist (le_of_lt (not_le.mp hx)),zero_mul]

theorem cut_weak_partial_schwartz (χ : ContDiffBump (0 : Space)) (ν a t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (i : Fin 3) (ψ : 𝓢(Space,ℂ)) :
    (∫ x : Space, complexify (cutElectric χ ν a t) x i*ψ x)=
      -(∫ x : Space, (cutPotential χ ν a t x : ℂ)*GradientProjection.pderivative i ψ x) := by
  have h := cut_weak_partial_complex χ ν a t hν ha ht ht1 i (localTest χ ψ)
    ((localTest_regular χ ψ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
    (localTest_compact χ ψ)
  have hU : ∀ x ∉ closedBall (0 : Space) χ.rOut, (cutPotential χ ν a t x : ℂ)=0 := by
    intro x hx
    rw [cutPotential_zero_outer χ ν a t x hx,Complex.ofReal_zero]
  have hE : ∀ x ∉ closedBall (0 : Space) χ.rOut, complexify (cutElectric χ ν a t) x i=0 := by
    intro x hx
    simp only [complexify,cutElectric_zero_outer χ ν a t x hx,PiLp.zero_apply,Complex.ofReal_zero]
  rw [derivative_pair_local χ _ ψ hU i,value_pair_local χ _ ψ hE] at h
  simp only [GradientProjection.pderivative_apply]
  simpa only [neg_neg] using congrArg Neg.neg h.symm

theorem cutCurl_weak_divergence_schwartz (χ : ContDiffBump (0 : Space)) (ν a d t : ℝ)
    (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1)
    (hroot : CapAngularShooting.determinant d t a = 0) (heq : ν*(ν+1)=a)
    (ψ : 𝓢(Space,ℂ)) :
    (∑ i : Fin 3, ∫ x : Space, complexify (cutCurl χ ν a d t) x i*GradientProjection.pderivative i ψ x)=0 := by
  have h := cutCurl_weak_divergence_complex χ ν a d t hν ha hd ht ht1 hroot heq (localTest χ ψ)
    ((localTest_regular χ ψ).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
    (localTest_compact χ ψ)
  have hC (i : Fin 3) : ∀ x ∉ closedBall (0 : Space) χ.rOut, complexify (cutCurl χ ν a d t) x i=0 := by
    intro x hx
    simp only [complexify,cutCurl_zero_outer χ ν a d t x hx,PiLp.zero_apply,Complex.ofReal_zero]
  have he : (∑ i : Fin 3, ∫ x : Space, complexify (cutCurl χ ν a d t) x i*dcoord (localTest χ ψ) x i)=
      ∑ i : Fin 3, ∫ x : Space, complexify (cutCurl χ ν a d t) x i*GradientProjection.pderivative i ψ x := by
    apply Finset.sum_congr rfl
    intro i _
    simpa only [GradientProjection.pderivative_apply] using derivative_pair_local χ _ ψ (hC i) i
  rw [he] at h
  exact h

end OQ14.ConicalSchwartzLocalization

#print axioms OQ14.ConicalSchwartzLocalization.cut_weak_partial_schwartz
#print axioms OQ14.ConicalSchwartzLocalization.cutCurl_weak_divergence_schwartz
