import NewtonExteriorResponse
import MagneticResponse

/-! # Continuous ordinary exterior representatives of the response fields

Continuity is proved for the literal integral by local uniform domination on
the compact source support. The resulting representatives may therefore be
used for pointwise outgoing limits independently of L2 representative choices.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ExteriorContinuity

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel Filter
open OQ14.WeakCurl (next previous)
open scoped Topology

theorem response_continuousAt (q ρ : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContinuousAt q z) (hρ : Integrable ρ volume) (S : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 S → ρ y = 0) (x : Space) (hx : S < ‖x‖) :
    ContinuousAt (KernelConvolution.response q ρ) x := by
  let a := (‖x‖-S)/2
  have ha : 0 < a := by dsimp [a]; linarith
  have hZ (z : Space) (hz : z ∈ closedBall x a) : S < ‖z‖ := by
    have hdist : ‖x-z‖ ≤ a := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have hn := norm_sub_norm_le x z
    dsimp [a] at hdist
    linarith
  have hNZ (z y : Space) (hz : z ∈ closedBall x a) (hy : y ∈ closedBall 0 S) :
      z-y ≠ 0 := by
    intro he
    have hz' := hZ z hz
    rw [sub_eq_zero.mp he] at hz'
    exact (not_le_of_gt hz') (by simpa only [mem_closedBall, dist_zero_right] using hy)
  have hK : IsCompact (closedBall x a ×ˢ closedBall (0 : Space) S) :=
    (isCompact_closedBall x a).prod (isCompact_closedBall 0 S)
  have hqK : ContinuousOn (fun p : Space × Space => q (p.1-p.2))
      (closedBall x a ×ˢ closedBall (0 : Space) S) := by
    intro p hp
    exact ((hq (p.1-p.2) (hNZ _ _ hp.1 hp.2)).comp (f := fun v : Space × Space => v.1-v.2)
      (continuous_fst.sub continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hqK
  have hys (y : Space) (hy : ρ y ≠ 0) : y ∈ closedBall 0 S := by
    by_cases hn : y ∈ closedBall (0 : Space) S
    · exact hn
    · exact False.elim (hy (hc y hn))
  apply continuousAt_of_dominated (F := fun z y => ρ y * q (z-y))
    (bound := fun y => ‖ρ y‖ * C)
  · filter_upwards [ball_mem_nhds x ha] with z hz
    exact (NewtonExteriorResponse.source_integrand_integrable q ρ hq hρ S hc z
      (hZ z (ball_subset_closedBall hz))).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x ha] with z hz
    filter_upwards with y
    by_cases hy : ρ y = 0
    · simp [hy]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (hC (z,y) ⟨ball_subset_closedBall hz, hys y hy⟩) (norm_nonneg _)
  · exact hρ.norm.mul_const C
  · filter_upwards with y
    by_cases hy : ρ y = 0
    · simp only [hy, zero_mul]
      exact continuousAt_const
    exact continuousAt_const.mul ((hq (x-y)
      (hNZ x y (mem_closedBall_self ha.le) (hys y hy))).comp (f := fun z : Space => z-y)
        (continuous_id.sub continuous_const).continuousAt)

theorem dyadic_continuousAt (k : ℝ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y => DyadicKernel.dyadic k y i j) x := by
  unfold DyadicKernel.dyadic
  exact ((continuousAt_const.mul (phi_contDiffAt k x hx).continuousAt).mul
    continuousAt_const).add (NewtonExterior.hessian_continuousAt k i j x hx)

def electric (k : ℝ) (ρ : Fin 3 → Space → ℂ) : Field :=
  fun x i => ∑ j, KernelConvolution.response (fun z => DyadicKernel.dyadic k z i j) (ρ j) x

theorem electric_continuousAt (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j) volume) (S : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (x : Space) (hx : S < ‖x‖) :
    ContinuousAt (electric k ρ) x := by
  apply continuousAt_pi.mpr
  intro i
  exact tendsto_finset_sum _ (fun j _ =>
    response_continuousAt _ (ρ j) (dyadic_continuousAt k i j) (hρ j) S (hc j) x hx)

theorem magnetic_continuousAt (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j) volume) (S : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (x : Space) (hx : S < ‖x‖) :
    ContinuousAt (MagneticResponse.magnetic k ρ) x := by
  have hg (i : Fin 3) (z : Space) (hz : z ≠ 0) :
      ContinuousAt (fun y => phiGradient k y i) z :=
    (KernelGradient.gradient_differentiableAt k i z hz).continuousAt
  apply continuousAt_pi.mpr
  intro i
  exact continuousAt_const.mul
    ((response_continuousAt _ _ (hg (next i)) (hρ (previous i)) S (hc (previous i)) x hx).sub
      (response_continuousAt _ _ (hg (previous i)) (hρ (next i)) S (hc (next i)) x hx))

theorem electric_ae_exterior (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) :
    ∀ᵐ x ∂(volume : Measure Space), S < ‖x‖ →
      FieldResponse.electric k F ρ x = electric k ρ x := by
  have hh (r : ℚ) : ∀ᵐ x ∂(volume : Measure Space), S < (r : ℝ) → (r : ℝ) < ‖x‖ →
      ∀ i, FieldResponse.electric k F ρ x i = electric k ρ x i := by
    by_cases hr : S < (r : ℝ)
    · filter_upwards [ae_all_iff.mpr
        (fun i => NewtonExteriorResponse.electric_ae_exterior k F ρ hρ hF r S hr hc i)]
        with x hx _ hxr i
      exact hx i hxr
    · exact Eventually.of_forall (fun _ hs => False.elim (hr hs))
  filter_upwards [ae_all_iff.mpr hh] with x hx hSx
  obtain ⟨r, hSr, hrx⟩ := exists_rat_btwn hSx
  exact funext (hx r hSr hrx)

/-- Replace only the exterior values of the original response by its
continuous ordinary-integral representative. -/
def representative (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (S : ℝ) : Field :=
  fun x => if S < ‖x‖ then electric k ρ x else FieldResponse.electric k F ρ x

theorem representative_exterior (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (S : ℝ) (x : Space) (hx : S < ‖x‖) :
    representative k F ρ S x = electric k ρ x := if_pos hx

theorem representative_ae (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) :
    representative k F ρ S =ᵐ[volume] FieldResponse.electric k F ρ := by
  filter_upwards [electric_ae_exterior k F ρ hρ hF S hc] with x hx
  by_cases hs : S < ‖x‖
  · exact (representative_exterior k F ρ S x hs).trans (hx hs).symm
  · simp only [representative, if_neg hs]

theorem representative_continuousAt (k : ℝ) (F : VectorFourier.VectorL2)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (S : ℝ) (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0)
    (x : Space) (hx : S < ‖x‖) :
    ContinuousAt (representative k F ρ S) x := by
  apply (electric_continuousAt k ρ hρ S hc x hx).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact representative_exterior k F ρ S y hy

theorem electric_unique (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j) volume) (S : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 S → ρ j y = 0) (E : Field)
    (hE : ContinuousOn E {x | S < ‖x‖})
    (he : E =ᵐ[volume.restrict {x : Space | S < ‖x‖}] electric k ρ) :
    Set.EqOn E (electric k ρ) {x | S < ‖x‖} :=
  Measure.eqOn_open_of_ae_eq he (isOpen_lt continuous_const continuous_norm) hE
    (fun x hx => (electric_continuousAt k ρ hρ S hc x hx).continuousWithinAt)

end OQ14.ExteriorContinuity

#print axioms OQ14.ExteriorContinuity.response_continuousAt
#print axioms OQ14.ExteriorContinuity.dyadic_continuousAt
#print axioms OQ14.ExteriorContinuity.electric_continuousAt
#print axioms OQ14.ExteriorContinuity.magnetic_continuousAt
#print axioms OQ14.ExteriorContinuity.electric_ae_exterior
#print axioms OQ14.ExteriorContinuity.representative_exterior
#print axioms OQ14.ExteriorContinuity.representative_ae
#print axioms OQ14.ExteriorContinuity.representative_continuousAt
#print axioms OQ14.ExteriorContinuity.electric_unique
