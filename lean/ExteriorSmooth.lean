import ScalarExteriorRegularity
import ExteriorContinuity
import WeakPoynting.InteriorTestDensity

/-! # Actual smooth exterior integral responses

An actual compact smooth cutoff removes the kernel singularity on the
compact difference set relevant to a neighborhood of an exterior point.
The proved smooth-convolution theorem then applies to the L1 source.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ExteriorSmooth

open MeasureTheory Metric OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution Filter
open scoped Topology

theorem localized_kernel (q : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z)
    (R : ℝ) (x : Space) (hx : R < ‖x‖) :
    ∃ g : Space → ℂ, ContDiff ℝ (⊤ : ℕ∞) g ∧ HasCompactSupport g ∧
      ∀ᶠ z in 𝓝 x, ∀ y ∈ closedBall 0 R, g (z-y) = q (z-y) := by
  let a := (‖x‖-R)/2
  have ha : 0 < a := by dsimp [a]; linarith
  let K := (fun p : Space × Space => p.1-p.2) ''
    (closedBall x a ×ˢ closedBall 0 R)
  have hK : IsCompact K :=
    ((isCompact_closedBall x a).prod (isCompact_closedBall 0 R)).image
      (continuous_fst.sub continuous_snd)
  have hn (z y : Space) (hz : z ∈ closedBall x a) (hy : y ∈ closedBall 0 R) :
      z-y ≠ 0 := by
    have hd : ‖x-z‖ ≤ a := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have hyr : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
    have h1 := norm_sub_norm_le x z
    have h2 := norm_sub_norm_le z y
    apply norm_pos_iff.mp
    dsimp [a] at hd
    linarith
  have hKΩ : K ⊆ ({0} : Set Space)ᶜ := by
    rintro _ ⟨⟨z,y⟩, ⟨hz,hy⟩, rfl⟩
    exact hn z y hz hy
  obtain ⟨κ, hκ⟩ := InteriorTestDensity.exists_smooth_interior
    (isClosed_singleton.isOpen_compl) hK hKΩ
  let g : Space → ℂ := fun z => κ.function z * q z
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      have h0 : (0 : Space) ∉ tsupport κ.function := fun h => κ.inside h rfl
      have he : g =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds h0] with y hy
        have hy0 : κ.function y = 0 := Classical.byContradiction
          (fun hn => hy (subset_closure hn))
        simp [g, hy0]
      exact contDiffAt_const.congr_of_eventuallyEq he
    · exact κ.smooth.contDiffAt.mul (hq z hz)
  refine ⟨g, hg, κ.compact.mul_right, ?_⟩
  filter_upwards [ball_mem_nhds x ha] with z hz
  intro y hy
  have hzy : z-y ∈ K := ⟨(z,y), ⟨ball_subset_closedBall hz, hy⟩, rfl⟩
  have h1 := (hκ (z-y) hzy).eq_of_nhds
  simp [g, h1]

theorem response_contDiffAt (q ρ : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z)
    (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (response q ρ) x := by
  obtain ⟨g, hg, hgc, he⟩ := localized_kernel q hq R x hx
  have hgs : ContDiff ℝ (⊤ : ℕ∞) (response g ρ) :=
    hgc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
      hρ.locallyIntegrable hg
  apply hgs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [he] with z hz
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ closedBall (0 : Space) R
  · rw [hz y hy]
  · simp [hc y hy]

theorem response_contDiffOn (q ρ : Space → ℂ)
    (hq : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z)
    (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) :
    ContDiffOn ℝ (⊤ : ℕ∞) (response q ρ) {x | R < ‖x‖} :=
  fun x hx => (response_contDiffAt q ρ hq hρ R hc x hx).contDiffWithinAt

theorem gradient_contDiffAt (k : ℝ) (j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => phiGradient k y j) x := by
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => y j) x :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have he := (contDiffAt_const (c := Complex.I * k)).mul hc |>.cexp
  have hd := ((contDiffAt_const (c := Complex.I * k)).mul (hc.inv hrc)).sub
    ((contDiffAt_const (c := (1 : ℂ))).mul ((hc.pow 2).inv (pow_ne_zero 2 hrc)))
  have hu := Complex.ofRealCLM.contDiff.contDiffAt.comp x (hj.div hn hr)
  simpa only [phiGradient, radialD, Function.comp_def, Complex.ofRealCLM_apply, div_eq_mul_inv] using
    ((he.mul hd).mul hu).mul contDiffAt_const

theorem hessian_contDiffAt (k : ℝ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => phiHessian k y i j) x := by
  have hn : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => ‖y‖) x := contDiffAt_norm ℝ hx
  have hr : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hrc : (‖x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp x hn
  have hi : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => y i) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have hj : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => y j) x :=
    (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.contDiffAt
  have hci := Complex.ofRealCLM.contDiff.contDiffAt.comp x hi
  have hcj := Complex.ofRealCLM.contDiff.contDiffAt.comp x hj
  have he := (contDiffAt_const (c := Complex.I * k)).mul hc |>.cexp
  have hd := he.mul (((contDiffAt_const (c := Complex.I * k)).mul (hc.inv hrc)).sub
    ((contDiffAt_const (c := (1 : ℂ))).mul ((hc.pow 2).inv (pow_ne_zero 2 hrc))))
  have hdd := he.mul
    ((((contDiffAt_const (c := (Complex.I * k)^2)).mul (hc.inv hrc)).sub
      ((contDiffAt_const (c := 2 * (Complex.I * k))).mul ((hc.pow 2).inv (pow_ne_zero 2 hrc)))).add
      ((contDiffAt_const (c := (2 : ℂ))).mul ((hc.pow 3).inv (pow_ne_zero 3 hrc))))
  have ht := ((hdd.mul hci).mul hcj).mul ((hc.pow 2).inv (pow_ne_zero 2 hrc))
  have hu := ((contDiffAt_const (c := (if i = j then 1 else 0 : ℂ))).mul (hc.inv hrc)).sub
    ((hci.mul hcj).mul ((hc.pow 3).inv (pow_ne_zero 3 hrc)))
  simpa only [phiHessian, radialDD, radialD, Function.comp_def, Complex.ofRealCLM_apply, div_eq_mul_inv] using
    (ht.add (hd.mul hu)).mul contDiffAt_const

theorem dyadic_contDiffAt (k : ℝ) (i j : Fin 3) (x : Space) (hx : x ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y => DyadicKernel.dyadic k y i j) x := by
  unfold DyadicKernel.dyadic
  exact ((contDiffAt_const.mul ((phi_contDiffAt k x hx).of_le le_top)).mul
    contDiffAt_const).add (hessian_contDiffAt k i j x hx)

theorem scalar_response_contDiffAt (k : ℝ) (ρ : Space → ℂ)
    (hρ : Integrable ρ) (R : ℝ)
    (hc : ∀ y, y ∉ closedBall 0 R → ρ y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (response (phi k) ρ) x :=
  response_contDiffAt _ _ (fun z hz => (phi_contDiffAt k z hz).of_le le_top) hρ R hc x hx

theorem electric_contDiffAt (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (ExteriorContinuity.electric k ρ) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact ContDiffAt.sum (fun j _ =>
    response_contDiffAt _ _ (dyadic_contDiffAt k i j) (hρ j) R (hc j) x hx)

theorem magnetic_contDiffAt (k : ℝ) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (R : ℝ)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) (x : Space) (hx : R < ‖x‖) :
    ContDiffAt ℝ (⊤ : ℕ∞) (MagneticResponse.magnetic k ρ) x := by
  apply contDiffAt_pi.mpr
  intro i
  exact contDiffAt_const.mul
    ((response_contDiffAt _ _ (gradient_contDiffAt k (WeakCurl.next i))
      (hρ (WeakCurl.previous i)) R (hc (WeakCurl.previous i)) x hx).sub
    (response_contDiffAt _ _ (gradient_contDiffAt k (WeakCurl.previous i))
      (hρ (WeakCurl.next i)) R (hc (WeakCurl.next i)) x hx))

end OQ14.ExteriorSmooth

#print axioms OQ14.ExteriorSmooth.localized_kernel
#print axioms OQ14.ExteriorSmooth.response_contDiffAt
#print axioms OQ14.ExteriorSmooth.response_contDiffOn
#print axioms OQ14.ExteriorSmooth.gradient_contDiffAt
#print axioms OQ14.ExteriorSmooth.hessian_contDiffAt
#print axioms OQ14.ExteriorSmooth.dyadic_contDiffAt
#print axioms OQ14.ExteriorSmooth.scalar_response_contDiffAt
#print axioms OQ14.ExteriorSmooth.electric_contDiffAt
#print axioms OQ14.ExteriorSmooth.magnetic_contDiffAt
