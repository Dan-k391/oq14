import LocalHelmholtzRepresentation
import WeakPoynting

/-! # Actual local convolution regularization of weak Helmholtz fields

The weak equation is the literal compact smooth test integral. Convolution with
a genuine compact smooth kernel is smooth, and actual first and second spatial
derivatives are transferred to that kernel. Testing with its shifted reflection
then proves the actual classical equation wherever the reflected support stays
inside the weak-equation domain. Finite kernel radius gives this support
separation on a smaller concentric ball.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.WeakHelmholtzRegularity

open MeasureTheory Set Metric OQ14.Maxwell OQ14.ExteriorHelmholtz OQ14.ExteriorGreen
  OQ14.LocalHelmholtzRepresentation
open scoped Convolution

def IsWeakHelmholtz (k : ℂ) (Ω : Set Space) (u : Space → ℂ) : Prop :=
  ∀ φ : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ y, u y*(laplacian φ y+k^2*φ y)) = 0

def smooth (ρ u : Space → ℂ) : Space → ℂ :=
  convolution u ρ (ContinuousLinearMap.mul ℝ ℂ) volume

theorem smooth_regular (ρ u : Space → ℂ) (hu : LocallyIntegrable u)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (smooth ρ u) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hu hρ

theorem smooth_partial (ρ u : Space → ℂ) (hu : LocallyIntegrable u)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ) (x : Space) (i : Fin 3) :
    dcoord (smooth ρ u) x i = ∫ y, u y*dcoord ρ (x-y) i := by
  have h1 : ContDiff ℝ 1 ρ := hρ.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ) hu h1 x
  change (fderiv ℝ (convolution u ρ (ContinuousLinearMap.mul ℝ ℂ) volume) x) (basis i) = _
  rw [hd.fderiv, convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℂ)
    hu (hc.fderiv ℝ) (h1.continuous_fderiv le_rfl)]
  rfl

theorem smooth_second_partial (ρ u : Space → ℂ) (hu : LocallyIntegrable u)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ) (x : Space) (i : Fin 3) :
    dcoord (fun z => dcoord (smooth ρ u) z i) x i =
      ∫ y, u y*dcoord (fun z => dcoord ρ z i) (x-y) i := by
  have he : (fun z => dcoord (smooth ρ u) z i) = smooth (fun z => dcoord ρ z i) u :=
    funext (fun z => smooth_partial ρ u hu hρ hc z i)
  rw [he, smooth_partial _ u hu (partial_contDiff hρ i) (hc.fderiv_apply ℝ (basis i))]

theorem smooth_helmholtz (k : ℂ) (Ω : Set Space) (u ρ : Space → ℂ)
    (hu : LocallyIntegrable u) (hw : IsWeakHelmholtz k Ω u)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (x : Space) (hs : tsupport (reflect x ρ) ⊆ Ω) :
    laplacian (smooth ρ u) x+k^2*smooth ρ u x = 0 := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (reflect x ρ) :=
    hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport (reflect x ρ) := hc.comp_homeomorph (Homeomorph.subLeft x)
  have htest := hw (reflect x ρ) hφ hφc hs
  simp only [reflect_laplacian x ρ hρ, reflect] at htest
  have hi (i : Fin 3) : Integrable
      (fun y => u y*dcoord (fun z => dcoord ρ z i) (x-y) i) :=
    PointSingularity.test_product_integrable _ _ hu
      (((partial_contDiff (partial_contDiff hρ i) i).continuous).comp
        (continuous_const.sub continuous_id))
      (((hc.fderiv_apply ℝ (basis i)).fderiv_apply ℝ (basis i)).comp_homeomorph
        (Homeomorph.subLeft x))
  have hj : Integrable (fun y => u y*ρ (x-y)) :=
    PointSingularity.test_product_integrable _ _ hu hφ.continuous hφc
  calc
    _ = (∑ i : Fin 3, ∫ y, u y*dcoord (fun z => dcoord ρ z i) (x-y) i) +
        k^2*(∫ y, u y*ρ (x-y)) := by
      simp only [laplacian]
      simp_rw [smooth_second_partial ρ u hu hρ hc]
      rfl
    _ = ∫ y, (∑ i : Fin 3, u y*dcoord (fun z => dcoord ρ z i) (x-y) i)+
        k^2*(u y*ρ (x-y)) := by
      rw [integral_add (integrable_finset_sum _ (fun i _ => hi i)) (hj.const_mul _),
        integral_finset_sum _ (fun i _ => hi i), integral_const_mul]
    _ = ∫ y, u y*(laplacian ρ (x-y)+k^2*ρ (x-y)) := by
      congr 1
      funext y
      simp only [laplacian, mul_add, Finset.mul_sum]
      ring
    _ = 0 := htest

theorem reflect_tsupport (x : Space) (ρ : Space → ℂ) :
    tsupport (reflect x ρ) ⊆ (fun y => x-y) ⁻¹' tsupport ρ := by
  apply closure_minimal _ ((isClosed_tsupport ρ).preimage (continuous_const.sub continuous_id))
  intro y hy
  exact subset_closure hy

theorem reflect_tsupport_in_ball (ρ : Space → ℂ) (ε r : ℝ) (c x : Space)
    (hρ : tsupport ρ ⊆ closedBall 0 ε) (hx : ‖x-c‖+ε < r) :
    tsupport (reflect x ρ) ⊆ ball c r := by
  intro y hy
  have he : ‖x-y‖ ≤ ε := by
    simpa only [mem_closedBall, dist_zero_right] using hρ (reflect_tsupport x ρ hy)
  have hn : ‖y-c‖ ≤ ‖x-c‖+ε := by
    calc
      _ = ‖(x-c)-(x-y)‖ := by congr 1; abel
      _ ≤ ‖x-c‖+‖x-y‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add_left he _
  simpa only [mem_ball, dist_eq_norm] using lt_of_le_of_lt hn hx

theorem smooth_helmholtz_on_ball (k : ℂ) (c : Space) (r ε : ℝ) (u ρ : Space → ℂ)
    (hu : LocallyIntegrable u) (hw : IsWeakHelmholtz k (ball c r) u)
    (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ) (hc : HasCompactSupport ρ)
    (hs : tsupport ρ ⊆ closedBall 0 ε) :
    ∀ x ∈ ball c (r-ε), laplacian (smooth ρ u) x+k^2*smooth ρ u x = 0 := by
  intro x hx
  have hd : ‖x-c‖+ε < r := by
    have ht : ‖x-c‖ < r-ε := by simpa only [mem_ball, dist_eq_norm] using hx
    linarith
  exact smooth_helmholtz k (ball c r) u ρ hu hw hρ hc x
    (reflect_tsupport_in_ball ρ ε r c x hs hd)

end OQ14.WeakHelmholtzRegularity

#print axioms OQ14.WeakHelmholtzRegularity.smooth_regular
#print axioms OQ14.WeakHelmholtzRegularity.smooth_partial
#print axioms OQ14.WeakHelmholtzRegularity.smooth_second_partial
#print axioms OQ14.WeakHelmholtzRegularity.smooth_helmholtz
#print axioms OQ14.WeakHelmholtzRegularity.reflect_tsupport
#print axioms OQ14.WeakHelmholtzRegularity.reflect_tsupport_in_ball
#print axioms OQ14.WeakHelmholtzRegularity.smooth_helmholtz_on_ball
