import SphereRemovable
import ModalOrigin
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# Radial interface calculus for actual spherical fields

The origin is removed by transverse Fubini and the spherical interface by
continuity and the off-countable FTC. Radial profile derivatives are bounded
by continuous explicit majorants, so local integrability is proved.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialInterface

open MeasureTheory OQ14.Maxwell OQ14.PointSingularity OQ14.SphereRemovable
  OQ14.GreenKernel OQ14.ModalDipole Filter Set
open scoped Topology

theorem integration_by_parts (i : Fin 3) (R : ℝ) (f g : Space → ℂ)
    (hfc : Continuous f) (hgc : Continuous g) (hcompact : HasCompactSupport g)
    (hf : ∀ x, x ≠ 0 → ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hg : ∀ x, DifferentiableAt ℝ g x)
    (hleft : Integrable (fun x => dcoord f x i * g x))
    (hright : Integrable (fun x => f x * dcoord g x i)) :
    (∫ x, f x * dcoord g x i) = -(∫ x, dcoord f x i * g x) := by
  rw [coordinate_Fubini i _ hright, coordinate_Fubini i _ hleft, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [(split_integrable i _ hleft).prod_left_ae,
    (split_integrable i _ hright).prod_left_ae,
    show ∀ᵐ q : Plane, q ≠ 0 from ae_iff.mpr (by simp)] with q hl hr hq
  have he := integral_derivative_off_countable
    (fun t => f ((split i).symm (t,q)) * g ((split i).symm (t,q)))
    (fun t => dcoord f ((split i).symm (t,q)) i * g ((split i).symm (t,q)) +
      f ((split i).symm (t,q)) * dcoord g ((split i).symm (t,q)) i)
    {t | ‖(split i).symm (t,q)‖ = R}
    (coordinate_line_sphere_finite i q R).countable
    ((hfc.comp (line_continuous i q)).mul (hgc.comp (line_continuous i q)))
    (line_compact_support i q _ hcompact).mul_left
    (fun t ht => ((hf _ (join_ne_zero i q hq t) ht).hasFDerivAt.comp_hasDerivAt t
      (join_hasDerivAt i q t)).mul
      ((hg _).hasFDerivAt.comp_hasDerivAt t (join_hasDerivAt i q t)))
    (hl.add hr)
  rw [integral_add hl hr] at he
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he)

theorem weak_partial (i : Fin 3) (R : ℝ) (f f' : Space → ℂ)
    (hc : Continuous f)
    (hf : ∀ x, x ≠ 0 → ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hder : ∀ x, x ≠ 0 → ‖x‖ ≠ R → dcoord f x i = f' x)
    (hdloc : LocallyIntegrable f')
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (∫ x, f' x * φ x) = -(∫ x, f x * dcoord φ x i) := by
  have hs : ∀ᵐ x : Space, ‖x‖ ≠ R := by
    rw [ae_iff]
    simpa only [not_not, Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (volume : Measure Space) (0 : Space) R
  have he : (fun x => f' x * φ x) =ᵐ[volume] (fun x => dcoord f x i * φ x) := by
    filter_upwards [hs, show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx hx0
    rw [hder x hx0 hx]
  have hl := (test_product_integrable f' φ hdloc hφ.continuous hcompact).congr he
  have hr := test_product_integrable f (fun x => dcoord φ x i) hc.locallyIntegrable
    (partial_continuous hφ i) (hcompact.fderiv_apply ℝ (basis i))
  have hb := integration_by_parts i R f φ hc hφ.continuous hcompact hf
    (fun x => hφ.differentiable le_rfl x) hl hr
  rw [integral_congr_ae he]
  simpa only [neg_neg] using congrArg Neg.neg hb.symm

def radial (f g : ℝ → ℂ) (x : Space) : ℂ :=
  if ‖x‖ ≤ 1 then f ‖x‖ else g ‖x‖

def radialD (fD gD : ℝ → ℂ) (x : Space) (i : Fin 3) : ℂ :=
  (if ‖x‖ ≤ 1 then fD ‖x‖ else gD ‖x‖) * (x i / ‖x‖ : ℝ)

theorem radial_continuous (f g : ℝ → ℂ)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ioi 0))
    (hm : f 1 = g 1) : Continuous (radial f g) := by
  apply continuous_if_le continuous_norm continuous_const
  · exact hf.comp continuous_norm.continuousOn (fun x _ => norm_nonneg x)
  · apply hg.comp continuous_norm.continuousOn
    intro x hx
    change (1 : ℝ) ≤ ‖x‖ at hx
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx
  · intro x hx
    change ‖x‖ = 1 at hx
    rw [hx, hm]

theorem radial_eventually_inner (f g : ℝ → ℂ) (x : Space) (hx : ‖x‖ < 1) :
    radial f g =ᶠ[𝓝 x] (fun y => f ‖y‖) := by
  filter_upwards [continuous_norm.continuousAt.eventually_lt continuousAt_const hx] with y hy
  exact if_pos hy.le

theorem radial_eventually_outer (f g : ℝ → ℂ) (x : Space) (hx : 1 < ‖x‖) :
    radial f g =ᶠ[𝓝 x] (fun y => g ‖y‖) := by
  filter_upwards [continuousAt_const.eventually_lt continuous_norm.continuousAt hx] with y hy
  exact if_neg (not_le.mpr hy)

theorem radial_differentiableAt (f g fD gD : ℝ → ℂ)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) :
    DifferentiableAt ℝ (radial f g) x := by
  have hn := (differentiableAt_id.norm ℝ hx0).hasFDerivAt
  rcases hx1.lt_or_lt with hx | hx
  · exact ((hf _ (norm_pos_iff.mpr hx0)).hasFDerivAt.comp x hn).differentiableAt.congr_of_eventuallyEq
      (radial_eventually_inner f g x hx)
  · exact ((hg _ (norm_pos_iff.mpr hx0)).hasFDerivAt.comp x hn).differentiableAt.congr_of_eventuallyEq
      (radial_eventually_outer f g x hx)

theorem radial_partial (f g fD gD : ℝ → ℂ)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i : Fin 3) :
    dcoord (radial f g) x i = radialD fD gD x i := by
  rcases hx1.lt_or_lt with hx | hx
  · have he : fderiv ℝ (radial f g) x = fderiv ℝ (fun y => f ‖y‖) x :=
      (radial_eventually_inner f g x hx).fderiv_eq
    change fderiv ℝ (radial f g) x (basis i) = _
    rw [he]
    change dcoord (fun y => f ‖y‖) x i = _
    rw [radial_composition_partial f (fD ‖x‖) x hx0 (hf _ (norm_pos_iff.mpr hx0))]
    simp [radialD, hx.le]
  · have he : fderiv ℝ (radial f g) x = fderiv ℝ (fun y => g ‖y‖) x :=
      (radial_eventually_outer f g x hx).fderiv_eq
    change fderiv ℝ (radial f g) x (basis i) = _
    rw [he]
    change dcoord (fun y => g ‖y‖) x i = _
    rw [radial_composition_partial g (gD ‖x‖) x hx0 (hg _ (norm_pos_iff.mpr hx0))]
    simp [radialD, not_le.mpr hx]

theorem radial_profile_continuous (f : ℝ → ℂ) (hf : ContinuousOn f (Ici 0)) :
    Continuous (fun x : Space => f ‖x‖) :=
  hf.comp_continuous continuous_norm (fun x => norm_nonneg x)

theorem clipped_profile_continuous (g : ℝ → ℂ) (hg : ContinuousOn g (Ioi 0)) :
    Continuous (fun x : Space => g (max ‖x‖ (1/2))) :=
  hg.comp_continuous (continuous_norm.max continuous_const)
    (fun x => lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (le_max_right _ _))

theorem coordinate_ratio_norm_le (x : Space) (i : Fin 3) :
    ‖((x i / ‖x‖ : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, norm_div, norm_norm]
  exact div_le_one_of_le₀ (PiLp.norm_apply_le x i) (norm_nonneg x)

theorem radialD_locallyIntegrable (fD gD : ℝ → ℂ)
    (hf : ContinuousOn fD (Ici 0)) (hg : ContinuousOn gD (Ioi 0)) (i : Fin 3) :
    LocallyIntegrable (fun x => radialD fD gD x i) := by
  have hfc := radial_profile_continuous fD hf
  have hgc := clipped_profile_continuous gD hg
  have he : (fun x => radialD fD gD x i) =
      fun x : Space => (if ‖x‖ ≤ 1 then fD ‖x‖ else gD (max ‖x‖ (1/2))) *
        (x i / ‖x‖ : ℝ) := by
    funext x
    unfold radialD
    split_ifs with hx
    · rfl
    · rw [max_eq_left (by linarith : (1/2 : ℝ) ≤ ‖x‖)]
  have hm : Measurable (fun x => radialD fD gD x i) := by
    rw [he]
    apply Measurable.mul
    · exact Measurable.ite (isClosed_le continuous_norm continuous_const).measurableSet
        hfc.measurable hgc.measurable
    · fun_prop
  apply ((hfc.norm.add hgc.norm).locallyIntegrable).mono hm.aestronglyMeasurable
  filter_upwards with x
  rw [congrFun he x, norm_mul]
  have hbound : ‖if ‖x‖ ≤ 1 then fD ‖x‖ else gD (max ‖x‖ (1/2))‖ ≤
      ‖fD ‖x‖‖ + ‖gD (max ‖x‖ (1/2))‖ := by
    split_ifs <;> nlinarith [norm_nonneg (fD ‖x‖), norm_nonneg (gD (max ‖x‖ (1/2)))]
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  exact (mul_le_of_le_one_right (norm_nonneg _) (coordinate_ratio_norm_le x i)).trans hbound

theorem radial_weak_partial (f g fD gD : ℝ → ℂ)
    (hfc : ContinuousOn f (Ici 0)) (hgc : ContinuousOn g (Ioi 0))
    (hm : f 1 = g 1)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (hfD : ContinuousOn fD (Ici 0)) (hgD : ContinuousOn gD (Ioi 0))
    (i : Fin 3) (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (∫ x, radialD fD gD x i * φ x) =
      -(∫ x, radial f g x * dcoord φ x i) :=
  weak_partial i 1 (radial f g) (fun x => radialD fD gD x i)
    (radial_continuous f g hfc hgc hm)
    (radial_differentiableAt f g fD gD hf hg)
    (fun x hx0 hx1 => radial_partial f g fD gD hf hg x hx0 hx1 i)
    (radialD_locallyIntegrable fD gD hfD hgD i) φ hφ hcompact

theorem locallyIntegrable_mul_continuous (f g : Space → ℂ)
    (hf : LocallyIntegrable f) (hg : Continuous g) :
    LocallyIntegrable (fun x => f x * g x) := by
  rw [locallyIntegrable_iff]
  intro K hK
  exact (hf.integrableOn_isCompact hK).mul_continuousOn hg.continuousOn hK

def radialCoordinateD (f g fD gD : ℝ → ℂ) (i j : Fin 3) (x : Space) : ℂ :=
  radialD fD gD x i * (x j : ℂ) + radial f g x * (if i = j then 1 else 0)

theorem radial_coordinate_partial (f g fD gD : ℝ → ℂ)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (x : Space) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≠ 1) (i j : Fin 3) :
    dcoord (fun y => radial f g y * (y j : ℂ)) x i =
      radialCoordinateD f g fD gD i j x := by
  rw [partial_mul (radial_differentiableAt f g fD gD hf hg x hx0 hx1)
    (coordinate_differentiableAt x j), radial_partial f g fD gD hf hg x hx0 hx1 i,
    coordinate_partial]
  unfold radialCoordinateD
  ring

theorem radialCoordinateD_locallyIntegrable (f g fD gD : ℝ → ℂ)
    (hfc : ContinuousOn f (Ici 0)) (hgc : ContinuousOn g (Ioi 0)) (hm : f 1 = g 1)
    (hfD : ContinuousOn fD (Ici 0)) (hgD : ContinuousOn gD (Ioi 0)) (i j : Fin 3) :
    LocallyIntegrable (radialCoordinateD f g fD gD i j) := by
  exact (locallyIntegrable_mul_continuous _ _ (radialD_locallyIntegrable fD gD hfD hgD i)
    (coordinate j).continuous).add
      (((radial_continuous f g hfc hgc hm).mul continuous_const).locallyIntegrable)

theorem weak_gradient_cross_pair (R : ℝ) (f : Space → ℂ) (G : Field)
    (hc : Continuous f)
    (hf : ∀ x, x ≠ 0 → ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hder : ∀ x, x ≠ 0 → ‖x‖ ≠ R → ∀ i, dcoord f x i = G x i)
    (hloc : ∀ i, LocallyIntegrable (fun x => G x i))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ)
    (i j : Fin 3) :
    (∫ x, G x i * dcoord φ x j) = ∫ x, G x j * dcoord φ x i := by
  have hp (j : Fin 3) : ContDiff ℝ 1 (fun x => dcoord φ x j) := by
    have hd : ContDiff ℝ 1 (fderiv ℝ φ) :=
      (contDiff_succ_iff_fderiv (n := 1)).mp hφ |>.2.2
    exact hd.clm_apply contDiff_const
  rw [weak_partial i R f (fun x => G x i) hc hf (fun x hx0 hx1 => hder x hx0 hx1 i)
      (hloc i) _ (hp j) (hcompact.fderiv_apply ℝ (basis j)),
    weak_partial j R f (fun x => G x j) hc hf (fun x hx0 hx1 => hder x hx0 hx1 j)
      (hloc j) _ (hp i) (hcompact.fderiv_apply ℝ (basis i))]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [partial_comm hφ x i j]

theorem weak_gradient_curl_zero (R : ℝ) (f : Space → ℂ) (G : Field)
    (hc : Continuous f)
    (hf : ∀ x, x ≠ 0 → ‖x‖ ≠ R → DifferentiableAt ℝ f x)
    (hder : ∀ x, x ≠ 0 → ‖x‖ ≠ R → ∀ i, dcoord f x i = G x i)
    (hloc : ∀ i, LocallyIntegrable (fun x => G x i))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing G φ = 0 := by
  ext j
  fin_cases j <;> dsimp [weakCurlPairing] <;>
    rw [weak_gradient_cross_pair R f G hc hf hder hloc φ hφ hcompact] <;> simp

theorem radialCoordinate_gradient_curl_zero (f g fD gD : ℝ → ℂ)
    (hfc : ContinuousOn f (Ici 0)) (hgc : ContinuousOn g (Ioi 0))
    (hm : f 1 = g 1)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (hfD : ContinuousOn fD (Ici 0)) (hgD : ContinuousOn gD (Ioi 0))
    (m : Fin 3) (φ : Space → ℂ) (hφ : ContDiff ℝ 2 φ) (hcompact : HasCompactSupport φ) :
    weakCurlPairing (fun x i => radialCoordinateD f g fD gD i m x) φ = 0 :=
  weak_gradient_curl_zero 1 (fun x => radial f g x * (x m : ℂ)) _
    ((radial_continuous f g hfc hgc hm).mul (coordinate m).continuous)
    (fun x hx0 hx1 => (radial_differentiableAt f g fD gD hf hg x hx0 hx1).mul
      (coordinate_differentiableAt x m))
    (fun x hx0 hx1 i => radial_coordinate_partial f g fD gD hf hg x hx0 hx1 i m)
    (fun i => radialCoordinateD_locallyIntegrable f g fD gD hfc hgc hm hfD hgD i m)
    φ hφ hcompact

theorem ae_regular (R : ℝ) : ∀ᵐ x : Space, x ≠ 0 ∧ ‖x‖ ≠ R := by
  have hs : ∀ᵐ x : Space, ‖x‖ ≠ R := by
    rw [ae_iff]
    simpa only [not_not, Metric.sphere, dist_zero_right] using
      Measure.addHaar_sphere (volume : Measure Space) (0 : Space) R
  filter_upwards [hs, show ∀ᵐ x : Space, x ≠ 0 from ae_iff.mpr (by simp)] with x hx hx0
  exact ⟨hx0,hx⟩

theorem actual_partial_locallyIntegrable (R : ℝ) (f D : Space → ℂ) (i : Fin 3)
    (hD : LocallyIntegrable D)
    (he : ∀ x, x ≠ 0 → ‖x‖ ≠ R → dcoord f x i = D x) :
    LocallyIntegrable (fun x => dcoord f x i) := by
  apply hD.mono (measurable_fderiv_apply_const ℝ f (basis i)).aestronglyMeasurable
  filter_upwards [ae_regular R] with x hx
  change ‖dcoord f x i‖ ≤ ‖D x‖
  rw [he x hx.1 hx.2]

theorem radial_dcoord_locallyIntegrable (f g fD gD : ℝ → ℂ)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (hfD : ContinuousOn fD (Ici 0)) (hgD : ContinuousOn gD (Ioi 0)) (i : Fin 3) :
    LocallyIntegrable (fun x => dcoord (radial f g) x i) :=
  actual_partial_locallyIntegrable 1 _ _ i (radialD_locallyIntegrable fD gD hfD hgD i)
    (fun x hx0 hx1 => radial_partial f g fD gD hf hg x hx0 hx1 i)

theorem radial_coordinate_dcoord_locallyIntegrable (f g fD gD : ℝ → ℂ)
    (hfc : ContinuousOn f (Ici 0)) (hgc : ContinuousOn g (Ioi 0)) (hm : f 1 = g 1)
    (hf : ∀ r, 0 < r → HasDerivAt f (fD r) r)
    (hg : ∀ r, 0 < r → HasDerivAt g (gD r) r)
    (hfD : ContinuousOn fD (Ici 0)) (hgD : ContinuousOn gD (Ioi 0)) (i j : Fin 3) :
    LocallyIntegrable (fun x => dcoord (fun y => radial f g y * (y j : ℂ)) x i) :=
  actual_partial_locallyIntegrable 1 _ _ i
    (radialCoordinateD_locallyIntegrable f g fD gD hfc hgc hm hfD hgD i j)
    (fun x hx0 hx1 => radial_coordinate_partial f g fD gD hf hg x hx0 hx1 i j)

theorem curl_integration_by_parts (R : ℝ) (F : Field)
    (hFc : ∀ j, Continuous (fun x => F x j))
    (hFd : ∀ x, x ≠ 0 → ‖x‖ ≠ R → ∀ j, DifferentiableAt ℝ (fun y => F y j) x)
    (hloc : ∀ i j, LocallyIntegrable (fun x => pd F x i j))
    (φ : Space → ℂ) (hφ : ContDiff ℝ 1 φ) (hcompact : HasCompactSupport φ) :
    (fun j => ∫ x, curl F x j * φ x) = weakCurlPairing F φ := by
  have hI (i j : Fin 3) := test_product_integrable _ φ (hloc i j) hφ.continuous hcompact
  have hP (i j : Fin 3) := weak_partial i R (fun x => F x j) (fun x => pd F x i j)
    (hFc j) (fun x hx0 hx1 => hFd x hx0 hx1 j) (fun _ _ _ => rfl) (hloc i j) φ hφ hcompact
  ext j
  fin_cases j <;> dsimp [curl, weakCurlPairing] <;> simp only [sub_mul]
  · rw [integral_sub (hI 1 2) (hI 2 1), hP 1 2, hP 2 1]
    ring
  · rw [integral_sub (hI 2 0) (hI 0 2), hP 2 0, hP 0 2]
    ring
  · rw [integral_sub (hI 0 1) (hI 1 0), hP 0 1, hP 1 0]
    ring

end OQ14.RadialInterface

#print axioms OQ14.RadialInterface.integration_by_parts
#print axioms OQ14.RadialInterface.weak_partial
#print axioms OQ14.RadialInterface.radial_continuous
#print axioms OQ14.RadialInterface.radial_eventually_inner
#print axioms OQ14.RadialInterface.radial_eventually_outer
#print axioms OQ14.RadialInterface.radial_differentiableAt
#print axioms OQ14.RadialInterface.radial_partial
#print axioms OQ14.RadialInterface.radial_profile_continuous
#print axioms OQ14.RadialInterface.clipped_profile_continuous
#print axioms OQ14.RadialInterface.coordinate_ratio_norm_le
#print axioms OQ14.RadialInterface.radialD_locallyIntegrable
#print axioms OQ14.RadialInterface.radial_weak_partial
#print axioms OQ14.RadialInterface.locallyIntegrable_mul_continuous
#print axioms OQ14.RadialInterface.radial_coordinate_partial
#print axioms OQ14.RadialInterface.radialCoordinateD_locallyIntegrable
#print axioms OQ14.RadialInterface.weak_gradient_cross_pair
#print axioms OQ14.RadialInterface.weak_gradient_curl_zero
#print axioms OQ14.RadialInterface.radialCoordinate_gradient_curl_zero
#print axioms OQ14.RadialInterface.ae_regular
#print axioms OQ14.RadialInterface.actual_partial_locallyIntegrable
#print axioms OQ14.RadialInterface.radial_dcoord_locallyIntegrable
#print axioms OQ14.RadialInterface.radial_coordinate_dcoord_locallyIntegrable
#print axioms OQ14.RadialInterface.curl_integration_by_parts
