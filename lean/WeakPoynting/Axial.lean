import WeakPoynting.Aperture
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Lipschitz axial cutoffs for genuine one-dimensional weak derivatives

Directional derivatives below are actual line derivatives. Their weak
integration-by-parts property comes from the proved Rademacher library theorem,
not from an assumed Sobolev density or product identity.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.LipschitzLine

open MeasureTheory OQ14.FluxSlices OQ14.FluxRepresentative Filter
open scoped Topology Convolution NNReal

def mollify (f : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ)) : ℝ → ℝ :=
  convolution f (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume

theorem mollify_regular (f : ℝ → ℝ) (hf : LocallyIntegrable f)
    (φ : ContDiffBump (0 : ℝ)) : ContDiff ℝ (⊤ : ℕ∞) (mollify f φ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf φ.contDiff_normed

theorem mollify_compact (f : ℝ → ℝ) (hc : HasCompactSupport f)
    (φ : ContDiffBump (0 : ℝ)) : HasCompactSupport (mollify f φ) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) hc φ.hasCompactSupport_normed

theorem mollify_partial (f : ℝ → ℝ) (hf : LocallyIntegrable f)
    (φ : ContDiffBump (0 : ℝ)) (x v : ℝ) :
    fderiv ℝ (mollify f φ) x v = ∫ y, f y * fderiv ℝ (φ.normed volume) (x-y) v := by
  have hp : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  have hh := φ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hf hp x
  rw [show fderiv ℝ (mollify f φ) x = _ from hh.fderiv,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf
      (φ.hasCompactSupport_normed.fderiv ℝ) (hp.continuous_fderiv le_rfl)]
  rfl

theorem reflected_lineDeriv (φ : ContDiffBump (0 : ℝ)) (x y v : ℝ) :
    lineDeriv ℝ (fun z => φ.normed volume (x-z)) y (-v) =
      fderiv ℝ (φ.normed volume) (x-y) v := by
  have hp : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  have hh := ((hp.differentiable le_rfl) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change lineDeriv ℝ (φ.normed volume ∘ HSub.hSub x) y (-v) = _
  rw [hh.differentiableAt.lineDeriv_eq_fderiv, hh.fderiv]
  simp

/-- Mollification commutes with the genuine weak directional derivative of a
Lipschitz function, using actual integration by parts against the reflected kernel. -/
theorem mollify_lipschitz_partial {C : ℝ≥0} (f : ℝ → ℝ) (hf : LipschitzWith C f)
    (φ : ContDiffBump (0 : ℝ)) (x v : ℝ) :
    fderiv ℝ (mollify f φ) x v = mollify (fun y => lineDeriv ℝ f y v) φ x := by
  have hp : ContDiff ℝ 1 (fun y => φ.normed volume (x-y)) :=
    φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have hc : HasCompactSupport (fun y => φ.normed volume (x-y)) :=
    φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨D, hg⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hp le_rfl
  have he := hf.integral_lineDeriv_mul_eq (μ := volume) hg hc v
  simp only [reflected_lineDeriv] at he
  rw [mollify_partial f hf.continuous.locallyIntegrable φ x v]
  simpa only [mollify, convolution, ContinuousLinearMap.mul_apply', mul_comm] using he.symm

theorem mollify_swap (f : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    mollify f φ x = convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  rw [convolution_eq_swap]
  simp only [mollify, convolution, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, mul_comm]

theorem mollify_bound (f : ℝ → ℝ) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : ‖mollify f φ x‖ ≤ M := by
  rw [mollify_swap]
  change ‖∫ y, φ.normed volume y * f (x-y)‖ ≤ M
  have hi : Integrable (fun y => φ.normed volume y * M) :=
    ((φ.contDiff_normed (n := (1 : ℕ∞))).continuous.integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed).mul_const M
  calc
    _ ≤ ∫ y, φ.normed volume y * M := norm_integral_le_of_norm_le hi
      (Eventually.of_forall (fun y => by
        rw [norm_mul, Real.norm_of_nonneg (φ.nonneg_normed y)]
        exact mul_le_mul_of_nonneg_left (hM (x-y)) (φ.nonneg_normed y)))
    _ = M := by rw [integral_mul_const, φ.integral_normed, one_mul]

theorem mollify_lipschitz_partial_bound {C : ℝ≥0} (f : ℝ → ℝ)
    (hf : LipschitzWith C f) (φ : ContDiffBump (0 : ℝ)) (x v : ℝ) :
    ‖fderiv ℝ (mollify f φ) x v‖ ≤ C * ‖v‖ := by
  rw [mollify_lipschitz_partial f hf φ x v]
  exact mollify_bound _ (fun y => norm_lineDeriv_le_of_lipschitz ℝ hf) φ x

theorem mollify_lipschitz_partial_ae_tendsto {C : ℝ≥0} (f : ℝ → ℝ)
    (hf : LipschitzWith C f) (v : ℝ) :
    ∀ᵐ x ∂volume, Tendsto (fun n =>
      fderiv ℝ (mollify f (OQ14.FluxRepresentative.shrinkingBump n)) x v)
      atTop (𝓝 (lineDeriv ℝ f x v)) := by
  have hr : ∀ᶠ n in atTop, (OQ14.FluxRepresentative.shrinkingBump n).rOut ≤
      2 * (OQ14.FluxRepresentative.shrinkingBump n).rIn :=
    Eventually.of_forall (fun n => by simp [OQ14.FluxRepresentative.shrinkingBump, div_eq_mul_inv])
  simpa only [mollify_lipschitz_partial f hf, mollify_swap] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      OQ14.FluxRepresentative.shrinkingBump_tendsto hr (hf.locallyIntegrable_lineDeriv (μ := volume) v)

theorem mollify_support (f : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ)) :
    tsupport (mollify f φ) ⊆ Metric.cthickening φ.rOut (tsupport f) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  have hs := support_convolution_subset_swap (ContinuousLinearMap.mul ℝ ℝ) hx
  obtain ⟨y, hy, z, hz, hzy⟩ := hs
  have hy' : ‖y‖ < φ.rOut := by
    simpa [φ.support_normed_eq, Metric.mem_ball, dist_zero_right] using hy
  apply Metric.mem_cthickening_of_dist_le x z φ.rOut (tsupport f) (subset_tsupport _ hz)
  rw [← hzy, dist_eq_norm, add_sub_cancel_right]
  exact hy'.le

/-- Small enough mollifiers retain support strictly inside the original open region. -/
theorem mollify_eventually_inside {Ω : Set ℝ} (hΩ : IsOpen Ω) (f : ℝ → ℝ)
    (hc : HasCompactSupport f) (hsub : tsupport f ⊆ Ω) :
    ∀ᶠ n in atTop, tsupport (mollify f (OQ14.FluxRepresentative.shrinkingBump n)) ⊆ Ω := by
  obtain ⟨δ, hδ, hs⟩ := hc.exists_cthickening_subset_open hΩ hsub
  have he := OQ14.FluxRepresentative.shrinkingBump_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with n hn
  exact (mollify_support f _).trans ((Metric.cthickening_mono hn.le _).trans hs)

theorem directional_pair_integrable {C : ℝ≥0} (f : ℝ → ℝ) (hf : LipschitzWith C f)
    (g : ℝ → ℝ) (hg : Integrable g) (v : ℝ) :
    Integrable (fun x => lineDeriv ℝ f x v * g x) :=
  hg.bdd_mul (aestronglyMeasurable_lineDeriv hf.continuous volume)
    ⟨C * ‖v‖, fun _ => norm_lineDeriv_le_of_lipschitz ℝ hf⟩

/-- The uniformly bounded derivative approximation converges against every actual L1 field. -/
theorem mollify_directional_pair_tendsto {C : ℝ≥0} (f : ℝ → ℝ) (hf : LipschitzWith C f)
    (g : ℝ → ℝ) (hg : Integrable g) (v : ℝ) :
    Tendsto (fun n => ∫ x, fderiv ℝ (mollify f (OQ14.FluxRepresentative.shrinkingBump n)) x v * g x)
      atTop (𝓝 (∫ x, lineDeriv ℝ f x v * g x)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x => (C * ‖v‖) * ‖g x‖)
  · exact Eventually.of_forall (fun n =>
      (((mollify_regular f hf.continuous.locallyIntegrable _).continuous_fderiv (by simp)).clm_apply
        (continuous_const (y := v))).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mollify_lipschitz_partial_bound f hf _ x v) (norm_nonneg _)))
  · exact hg.norm.const_mul _
  · filter_upwards [mollify_lipschitz_partial_ae_tendsto f hf v] with x hx
    exact hx.mul_const (g x)

theorem mollify_directional_pair_integrable {C : ℝ≥0} (f : ℝ → ℝ)
    (hf : LipschitzWith C f) (g : ℝ → ℝ) (hg : Integrable g)
    (φ : ContDiffBump (0 : ℝ)) (v : ℝ) :
    Integrable (fun x => fderiv ℝ (mollify f φ) x v * g x) := by
  have hr := ((mollify_regular f hf.continuous.locallyIntegrable φ).continuous_fderiv
    (by simp)).clm_apply (continuous_const (y := v))
  exact hg.bdd_mul hr.aestronglyMeasurable
    ⟨C * ‖v‖, fun x => mollify_lipschitz_partial_bound f hf φ x v⟩

theorem lineDeriv_one (f : ℝ → ℝ) (x : ℝ) : lineDeriv ℝ f x 1 = deriv f x := by
  simp [lineDeriv, deriv_comp_add_const, deriv_comp_const_add]

theorem mollify_value_pair_tendsto {C : ℝ≥0} (f : ℝ → ℝ) (hf : LipschitzWith C f)
    (hc : HasCompactSupport f) (g : ℝ → ℝ) (hg : Integrable g) :
    Tendsto (fun n => ∫ x, mollify f (shrinkingBump n) x * g x)
      atTop (𝓝 (∫ x, f x * g x)) := by
  obtain ⟨M, hM⟩ := hf.continuous.bounded_above_of_compact_support hc
  apply tendsto_integral_filter_of_dominated_convergence (fun x => M * ‖g x‖)
  · exact Eventually.of_forall (fun n =>
      (mollify_regular f hf.continuous.locallyIntegrable _).continuous.aestronglyMeasurable.mul
        hg.aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mollify_bound f hM _ x) (norm_nonneg _)))
  · exact hg.norm.const_mul _
  · filter_upwards [smooth_ae_tendsto f hf.continuous.locallyIntegrable] with x hx
    exact hx.mul_const (g x)

/-- The original smooth-test weak derivative extends to every actual compact
Lipschitz scalar supported in the open interval region. -/
theorem weak_derivative_lipschitz_test {I : Set ℝ} (hI : IsOpen I)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) {C : ℝ≥0} (θ : ℝ → ℝ)
    (hθ : LipschitzWith C θ) (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ I) :
    (∫ x, deriv θ x * f x + θ x * g x) = 0 := by
  have hlim := (mollify_directional_pair_tendsto θ hθ f hf 1).add
    (mollify_value_pair_tendsto θ hθ hc g hg)
  simp only [fderiv_deriv, smul_eq_mul, one_mul, lineDeriv_one] at hlim
  have he : ∀ᶠ n in atTop,
      (∫ x, deriv (mollify θ (shrinkingBump n)) x * f x) +
        (∫ x, mollify θ (shrinkingBump n) x * g x) = 0 := by
    filter_upwards [mollify_eventually_inside hI θ hc hs] with n hn
    have hr : ContDiff ℝ 1 (mollify θ (shrinkingBump n)) :=
      (mollify_regular θ hθ.continuous.locallyIntegrable _).of_le (by simp)
    have hh := hw ⟨_, hr, mollify_compact θ hc _, hn⟩
    have hd : Integrable (fun x => deriv (mollify θ (shrinkingBump n)) x * f x) := by
      simpa only [fderiv_deriv, smul_eq_mul, one_mul] using
        mollify_directional_pair_integrable θ hθ f hf (shrinkingBump n) 1
    have hv : Integrable (fun x => mollify θ (shrinkingBump n) x * g x) :=
      hg.bdd_mul hr.continuous.aestronglyMeasurable
        (hr.continuous.bounded_above_of_compact_support (mollify_compact θ hc _))
    simpa only [integral_add hd hv] using hh
  have hz := tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (he.mono (fun _ hn => hn.symm)))
  have hd : Integrable (fun x => deriv θ x * f x) := by
    simpa only [lineDeriv_one] using directional_pair_integrable θ hθ f hf 1
  have hv : Integrable (fun x => θ x * g x) :=
    hg.bdd_mul hθ.continuous.aestronglyMeasurable
      (hθ.continuous.bounded_above_of_compact_support hc)
  rw [integral_add hd hv]
  exact hz

structure Cutoff where
  function : ℝ → ℝ
  lipschitzBound : ℝ≥0
  lipschitz : LipschitzWith lipschitzBound function
  compact : HasCompactSupport function

theorem cutoff_integrable (χ : Cutoff) (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => χ.function x * f x) ∧
      Integrable (fun x => χ.function x * g x + deriv χ.function x * f x) := by
  have hb := χ.lipschitz.continuous.bounded_above_of_compact_support χ.compact
  have hd : Integrable (fun x => deriv χ.function x * f x) := by
    simpa only [lineDeriv_one] using directional_pair_integrable χ.function χ.lipschitz f hf 1
  exact ⟨hf.bdd_mul χ.lipschitz.continuous.aestronglyMeasurable hb,
    (hg.bdd_mul χ.lipschitz.continuous.aestronglyMeasurable hb).add hd⟩

/-- A genuine distributional product rule with a Lipschitz multiplier. -/
theorem product_weak_derivative {I : Set ℝ} (hI : IsOpen I) (χ : Cutoff)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) :
    HasWeakDerivativeOn I (fun x => χ.function x * f x)
      (fun x => χ.function x * g x + deriv χ.function x * f x) := by
  intro θ
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport θ.compact θ.regular le_rfl
  obtain ⟨M, hM⟩ := θ.regular.continuous.bounded_above_of_compact_support θ.compact
  obtain ⟨N, hN⟩ := χ.lipschitz.continuous.bounded_above_of_compact_support χ.compact
  have hp := OQ14.LipschitzAperture.bounded_lipschitz_mul θ.function χ.function hA χ.lipschitz
    (fun x => (hM x).trans (Real.le_coe_toNNReal M))
    (fun x => (hN x).trans (Real.le_coe_toNNReal N))
  have hh := weak_derivative_lipschitz_test hI f g hf hg hw
    (fun x => θ.function x * χ.function x) hp θ.compact.mul_right
    (tsupport_mul_subset_left.trans θ.inside)
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [χ.lipschitz.ae_differentiableAt (μ := volume)] with x hx
  rw [deriv_mul (θ.regular.differentiable le_rfl x) hx]
  ring

/-- The weighted endpoint identity remains true for actual Lipschitz cutoffs. -/
theorem weak_endpoint_identity {I : Set ℝ} (hI : IsOpen I)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) {a b : ℝ} (hab : a < b)
    (hsub : Set.Icc a b ⊆ I) (χ : Cutoff)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hae : f =ᵐ[volume.restrict (Set.Icc a b)] F) :
    (∫ x in a..b, deriv χ.function x * f x + χ.function x * g x) =
      χ.function b * F b - χ.function a * F a := by
  obtain ⟨hi, hj⟩ := cutoff_integrable χ f g hf hg
  obtain ⟨J, hJ, hJae, hJinc⟩ := local_continuous_representative hI _ _ hi hj
    (product_weak_derivative hI χ f g hf hg hw) hsub
  have heq : J =ᵐ[volume.restrict (Set.Icc a b)] (fun x => χ.function x * F x) := by
    filter_upwards [hae, hJae] with x hx hjx
    rw [← hjx, hx]
  have he := representative_unique hab hJ (χ.lipschitz.continuous.mul hF) heq
  have hinc := hJinc a ⟨le_rfl, hab.le⟩ b ⟨hab.le, le_rfl⟩
  rw [he ⟨hab.le, le_rfl⟩, he ⟨le_rfl, hab.le⟩] at hinc
  simpa only [add_comm] using hinc.symm

theorem left_trace_identity {I : Set ℝ} (hI : IsOpen I)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) {a b : ℝ} (hab : a < b)
    (hsub : Set.Icc a b ⊆ I) (χ : Cutoff)
    (ha : χ.function a = 1) (hb : χ.function b = 0)
    (F : ℝ → ℝ) (hF : Continuous F)
    (hae : f =ᵐ[volume.restrict (Set.Icc a b)] F) :
    F a = -(∫ x in a..b, deriv χ.function x * f x + χ.function x * g x) := by
  have h := weak_endpoint_identity hI f g hf hg hw hab hsub χ F hF hae
  rw [ha, hb, zero_mul, one_mul, zero_sub] at h
  linarith

end OQ14.LipschitzLine

#print axioms OQ14.LipschitzLine.mollify_lipschitz_partial
#print axioms OQ14.LipschitzLine.mollify_lipschitz_partial_ae_tendsto
#print axioms OQ14.LipschitzLine.mollify_directional_pair_tendsto
#print axioms OQ14.LipschitzLine.mollify_value_pair_tendsto
#print axioms OQ14.LipschitzLine.weak_derivative_lipschitz_test
#print axioms OQ14.LipschitzLine.product_weak_derivative
#print axioms OQ14.LipschitzLine.weak_endpoint_identity
#print axioms OQ14.LipschitzLine.left_trace_identity

