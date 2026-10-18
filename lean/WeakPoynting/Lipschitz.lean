import WeakPoynting.Polarization
import Mathlib.Analysis.Calculus.Rademacher

/-!
# Actual Lipschitz test approximation for weak Maxwell flux

Directional derivatives below are actual line derivatives. Their weak
integration-by-parts property comes from the proved Rademacher library theorem,
not from an assumed Sobolev density or product identity.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.LipschitzFlux

open MeasureTheory OQ14.Maxwell Filter
open scoped Topology Convolution NNReal

def mollify (f : Space → ℝ) (φ : ContDiffBump (0 : Space)) : Space → ℝ :=
  convolution f (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume

theorem mollify_regular (f : Space → ℝ) (hf : LocallyIntegrable f)
    (φ : ContDiffBump (0 : Space)) : ContDiff ℝ (⊤ : ℕ∞) (mollify f φ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    hf φ.contDiff_normed

theorem mollify_compact (f : Space → ℝ) (hc : HasCompactSupport f)
    (φ : ContDiffBump (0 : Space)) : HasCompactSupport (mollify f φ) :=
  HasCompactSupport.convolution (ContinuousLinearMap.mul ℝ ℝ) hc φ.hasCompactSupport_normed

theorem mollify_partial (f : Space → ℝ) (hf : LocallyIntegrable f)
    (φ : ContDiffBump (0 : Space)) (x v : Space) :
    fderiv ℝ (mollify f φ) x v = ∫ y, f y * fderiv ℝ (φ.normed volume) (x-y) v := by
  have hp : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  have hh := φ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hf hp x
  rw [show fderiv ℝ (mollify f φ) x = _ from hh.fderiv,
    convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf
      (φ.hasCompactSupport_normed.fderiv ℝ) (hp.continuous_fderiv le_rfl)]
  rfl

theorem reflected_lineDeriv (φ : ContDiffBump (0 : Space)) (x y v : Space) :
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
theorem mollify_lipschitz_partial {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (φ : ContDiffBump (0 : Space)) (x v : Space) :
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

theorem mollify_swap (f : Space → ℝ) (φ : ContDiffBump (0 : Space)) (x : Space) :
    mollify f φ x = convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  rw [convolution_eq_swap]
  simp only [mollify, convolution, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, mul_comm]

theorem mollify_bound (f : Space → ℝ) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M)
    (φ : ContDiffBump (0 : Space)) (x : Space) : ‖mollify f φ x‖ ≤ M := by
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

theorem mollify_lipschitz_partial_bound {C : ℝ≥0} (f : Space → ℝ)
    (hf : LipschitzWith C f) (φ : ContDiffBump (0 : Space)) (x v : Space) :
    ‖fderiv ℝ (mollify f φ) x v‖ ≤ C * ‖v‖ := by
  rw [mollify_lipschitz_partial f hf φ x v]
  exact mollify_bound _ (fun y => norm_lineDeriv_le_of_lipschitz ℝ hf) φ x

theorem mollify_lipschitz_partial_ae_tendsto {C : ℝ≥0} (f : Space → ℝ)
    (hf : LipschitzWith C f) (v : Space) :
    ∀ᵐ x ∂volume, Tendsto (fun n =>
      fderiv ℝ (mollify f (OQ14.WeakPoynting.shrinkingBump n)) x v)
      atTop (𝓝 (lineDeriv ℝ f x v)) := by
  have hr : ∀ᶠ n in atTop, (OQ14.WeakPoynting.shrinkingBump n).rOut ≤
      2 * (OQ14.WeakPoynting.shrinkingBump n).rIn :=
    Eventually.of_forall (fun n => by simp [OQ14.WeakPoynting.shrinkingBump, div_eq_mul_inv])
  simpa only [mollify_lipschitz_partial f hf, mollify_swap] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      OQ14.WeakPoynting.shrinkingBump_tendsto hr (hf.locallyIntegrable_lineDeriv (μ := volume) v)

theorem mollify_support (f : Space → ℝ) (φ : ContDiffBump (0 : Space)) :
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
theorem mollify_eventually_inside {Ω : Set Space} (hΩ : IsOpen Ω) (f : Space → ℝ)
    (hc : HasCompactSupport f) (hsub : tsupport f ⊆ Ω) :
    ∀ᶠ n in atTop, tsupport (mollify f (OQ14.WeakPoynting.shrinkingBump n)) ⊆ Ω := by
  obtain ⟨δ, hδ, hs⟩ := hc.exists_cthickening_subset_open hΩ hsub
  have he := OQ14.WeakPoynting.shrinkingBump_tendsto.eventually (gt_mem_nhds hδ)
  filter_upwards [he] with n hn
  exact (mollify_support f _).trans ((Metric.cthickening_mono hn.le _).trans hs)

theorem directional_pair_integrable {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (g : Space → ℝ) (hg : Integrable g) (v : Space) :
    Integrable (fun x => lineDeriv ℝ f x v * g x) :=
  hg.bdd_mul (aestronglyMeasurable_lineDeriv hf.continuous volume)
    ⟨C * ‖v‖, fun _ => norm_lineDeriv_le_of_lipschitz ℝ hf⟩

/-- The uniformly bounded derivative approximation converges against every actual L1 field. -/
theorem mollify_directional_pair_tendsto {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (g : Space → ℝ) (hg : Integrable g) (v : Space) :
    Tendsto (fun n => ∫ x, fderiv ℝ (mollify f (OQ14.WeakPoynting.shrinkingBump n)) x v * g x)
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

theorem mollify_directional_pair_integrable {C : ℝ≥0} (f : Space → ℝ)
    (hf : LipschitzWith C f) (g : Space → ℝ) (hg : Integrable g)
    (φ : ContDiffBump (0 : Space)) (v : Space) :
    Integrable (fun x => fderiv ℝ (mollify f φ) x v * g x) := by
  have hr := ((mollify_regular f hf.continuous.locallyIntegrable φ).continuous_fderiv
    (by simp)).clm_apply (continuous_const (y := v))
  exact hg.bdd_mul hr.aestronglyMeasurable
    ⟨C * ‖v‖, fun x => mollify_lipschitz_partial_bound f hf φ x v⟩

def lineFlux (f : Space → ℝ) (P : OQ14.FluxSlices.RealFlux) (x : Space) : ℝ :=
  lineDeriv ℝ f x (basis 0) * P x 0 +
    lineDeriv ℝ f x (basis 1) * P x 1 + lineDeriv ℝ f x (basis 2) * P x 2

theorem lineFlux_integrable {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (P : OQ14.FluxSlices.RealFlux) (hP : ∀ j, Integrable (fun x => P x j)) :
    Integrable (lineFlux f P) :=
  ((directional_pair_integrable f hf _ (hP 0) (basis 0)).add
    (directional_pair_integrable f hf _ (hP 1) (basis 1))).add
    (directional_pair_integrable f hf _ (hP 2) (basis 2))

/-- A genuine divergence-free L1 field can be tested against any compactly
supported Lipschitz scalar with support inside the open region. This is proved
by actual mollification, support control, and dominated convergence. -/
theorem lipschitz_weak_divergence {Ω : Set Space} (hΩ : IsOpen Ω)
    {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (hc : HasCompactSupport f) (hsub : tsupport f ⊆ Ω)
    (P : OQ14.FluxSlices.RealFlux) (hP : ∀ j, Integrable (fun x => P x j))
    (hdiv : OQ14.FluxSlices.HasZeroDistributionalDivergence Ω P) :
    (∫ x, lineFlux f P x) = 0 := by
  let J (n : ℕ) (j : Fin 3) : ℝ :=
    ∫ x, fderiv ℝ (mollify f (OQ14.WeakPoynting.shrinkingBump n)) x (basis j) * P x j
  have hz : ∀ᶠ n in atTop, J n 0 + J n 1 + J n 2 = 0 := by
    filter_upwards [mollify_eventually_inside hΩ f hc hsub] with n hn
    let θ : OQ14.WeakConservation.RealTest Ω := {
      function := mollify f (OQ14.WeakPoynting.shrinkingBump n)
      regular := (mollify_regular f hf.continuous.locallyIntegrable _).of_le (by simp)
      compact := mollify_compact f hc _
      inside := hn }
    have hd := hdiv θ
    have hi (j : Fin 3) := mollify_directional_pair_integrable f hf _ (hP j)
      (OQ14.WeakPoynting.shrinkingBump n) (basis j)
    change (∫ x, fderiv ℝ (mollify f (OQ14.WeakPoynting.shrinkingBump n)) x (basis 0) * P x 0 +
      fderiv ℝ (mollify f (OQ14.WeakPoynting.shrinkingBump n)) x (basis 1) * P x 1 +
      fderiv ℝ (mollify f (OQ14.WeakPoynting.shrinkingBump n)) x (basis 2) * P x 2) = 0 at hd
    have hi01 := (hi 0).add (hi 1)
    dsimp only [Pi.add_def] at hi01
    rw [integral_add hi01 (hi 2), integral_add (hi 0) (hi 1)] at hd
    exact hd
  have ht := ((mollify_directional_pair_tendsto f hf _ (hP 0) (basis 0)).add
    (mollify_directional_pair_tendsto f hf _ (hP 1) (basis 1))).add
    (mollify_directional_pair_tendsto f hf _ (hP 2) (basis 2))
  have hzero : Tendsto (fun n => J n 0 + J n 1 + J n 2) atTop (𝓝 0) :=
    (tendsto_congr' hz).mpr tendsto_const_nhds
  have he := tendsto_nhds_unique ht hzero
  have hi (j : Fin 3) := directional_pair_integrable f hf _ (hP j) (basis j)
  have hi01 := (hi 0).add (hi 1)
  dsimp only [Pi.add_def] at hi01
  unfold lineFlux
  rw [integral_add hi01 (hi 2), integral_add (hi 0) (hi 1)]
  exact he

def gradientFlux (f : Space → ℝ) (P : OQ14.FluxSlices.RealFlux) (x : Space) : ℝ :=
  fderiv ℝ f x (basis 0) * P x 0 +
    fderiv ℝ f x (basis 1) * P x 1 + fderiv ℝ f x (basis 2) * P x 2

theorem lineFlux_eq_gradientFlux_ae {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (P : OQ14.FluxSlices.RealFlux) : lineFlux f P =ᵐ[volume] gradientFlux f P := by
  filter_upwards [hf.ae_differentiableAt (μ := volume)] with x hx
  simp only [lineFlux, gradientFlux, hx.lineDeriv_eq_fderiv]

/-- The actual a.e. Fréchet gradient gives an integrable pairing and the same
zero weak divergence for every compact interior Lipschitz test. -/
theorem lipschitz_weak_gradient_divergence {Ω : Set Space} (hΩ : IsOpen Ω)
    {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (hc : HasCompactSupport f) (hsub : tsupport f ⊆ Ω)
    (P : OQ14.FluxSlices.RealFlux) (hP : ∀ j, Integrable (fun x => P x j))
    (hdiv : OQ14.FluxSlices.HasZeroDistributionalDivergence Ω P) :
    Integrable (gradientFlux f P) ∧ (∫ x, gradientFlux f P x) = 0 := by
  have he := lineFlux_eq_gradientFlux_ae f hf P
  exact ⟨(lineFlux_integrable f hf P hP).congr he,
    (integral_congr_ae he).symm.trans (lipschitz_weak_divergence hΩ f hf hc hsub P hP hdiv)⟩

theorem lipschitz_maxwell_real_conservation {Ω : Set Space} (hΩ : IsOpen Ω)
    {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (hc : HasCompactSupport f) (hsub : tsupport f ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : OQ14.DomainCurl.HCurl Ω)
    (hM : OQ14.WeakConservation.WeakMaxwell ω μ ε E H) :
    Integrable (gradientFlux f (OQ14.FluxSlices.zeroExtendedPower Ω E H)) ∧
      (∫ x, gradientFlux f (OQ14.FluxSlices.zeroExtendedPower Ω E H) x) = 0 :=
  lipschitz_weak_gradient_divergence hΩ f hf hc hsub _
    (OQ14.FluxSlices.zeroExtendedPower_integrable hΩ.measurableSet E H)
    (OQ14.FluxSlices.maxwell_zeroExtendedPower_divergence hΩ ω μ ε E H hM)

def complexGradientFlux (f : Space → ℝ) (P : Space → Vector) (x : Space) : ℂ :=
  ((fderiv ℝ f x (basis 0) : ℝ) : ℂ) * P x 0 +
    ((fderiv ℝ f x (basis 1) : ℝ) : ℂ) * P x 1 +
    ((fderiv ℝ f x (basis 2) : ℝ) : ℂ) * P x 2

theorem complexGradientFlux_decomposition (f : Space → ℝ) (P : Space → Vector) (x : Space) :
    complexGradientFlux f P x = (gradientFlux f (fun y j => (P y j).re) x : ℂ) +
      Complex.I * (gradientFlux f (fun y j => (P y j).im) x : ℂ) := by
  apply Complex.ext <;> simp [complexGradientFlux, gradientFlux, Complex.mul_re, Complex.mul_im]

/-- The physical Hermitian two-input weak power law now permits arbitrary
compact Lipschitz scalar tests, without a C1 or smooth-density assumption. -/
theorem lipschitz_maxwell_cross_conservation {Ω : Set Space} (hΩ : IsOpen Ω)
    {C : ℝ≥0} (f : Space → ℝ) (hf : LipschitzWith C f)
    (hc : HasCompactSupport f) (hsub : tsupport f ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (u v : OQ14.CrossFlux.State Ω)
    (hu : OQ14.WeakConservation.WeakMaxwell ω μ ε u.1 u.2)
    (hv : OQ14.WeakConservation.WeakMaxwell ω μ ε v.1 v.2) :
    Integrable (complexGradientFlux f (OQ14.CrossFlux.crossFlux u v)) ∧
      (∫ x, complexGradientFlux f (OQ14.CrossFlux.crossFlux u v) x) = 0 := by
  let P := OQ14.CrossFlux.crossFlux u v
  have hp := OQ14.CrossFlux.crossFlux_integrable hΩ.measurableSet u v
  obtain ⟨hdr, hdi⟩ := OQ14.CrossFlux.crossFlux_components_conservation hΩ ω μ ε u v hu hv
  obtain ⟨hir, hzr⟩ := lipschitz_weak_gradient_divergence hΩ f hf hc hsub
    (fun x j => (P x j).re) (fun j => (hp j).re) hdr
  obtain ⟨hii, hzi⟩ := lipschitz_weak_gradient_divergence hΩ f hf hc hsub
    (fun x j => (P x j).im) (fun j => (hp j).im) hdi
  have heq : complexGradientFlux f P = fun x =>
      (gradientFlux f (fun y j => (P y j).re) x : ℂ) +
        Complex.I * (gradientFlux f (fun y j => (P y j).im) x : ℂ) :=
    funext (complexGradientFlux_decomposition f P)
  change Integrable (complexGradientFlux f P) ∧ (∫ x, complexGradientFlux f P x) = 0
  rw [heq]
  refine ⟨hir.ofReal.add (hii.ofReal.const_mul Complex.I), ?_⟩
  calc
    _ = (∫ x, (gradientFlux f (fun y j => (P y j).re) x : ℂ)) +
        ∫ x, Complex.I * (gradientFlux f (fun y j => (P y j).im) x : ℂ) :=
      integral_add hir.ofReal (hii.ofReal.const_mul Complex.I)
    _ = 0 := by
      rw [integral_const_mul, integral_complex_ofReal, integral_complex_ofReal, hzr, hzi]
      simp

end OQ14.LipschitzFlux

#print axioms OQ14.LipschitzFlux.mollify_regular
#print axioms OQ14.LipschitzFlux.mollify_compact
#print axioms OQ14.LipschitzFlux.mollify_lipschitz_partial
#print axioms OQ14.LipschitzFlux.mollify_bound
#print axioms OQ14.LipschitzFlux.mollify_lipschitz_partial_bound
#print axioms OQ14.LipschitzFlux.mollify_lipschitz_partial_ae_tendsto
#print axioms OQ14.LipschitzFlux.mollify_support
#print axioms OQ14.LipschitzFlux.mollify_eventually_inside
#print axioms OQ14.LipschitzFlux.directional_pair_integrable
#print axioms OQ14.LipschitzFlux.mollify_directional_pair_tendsto
#print axioms OQ14.LipschitzFlux.lineFlux_integrable
#print axioms OQ14.LipschitzFlux.lipschitz_weak_divergence
#print axioms OQ14.LipschitzFlux.lineFlux_eq_gradientFlux_ae
#print axioms OQ14.LipschitzFlux.lipschitz_weak_gradient_divergence
#print axioms OQ14.LipschitzFlux.lipschitz_maxwell_real_conservation
#print axioms OQ14.LipschitzFlux.lipschitz_maxwell_cross_conservation
