import WeakPoynting.Slices
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Continuous representatives of genuine one-dimensional weak derivatives

The primitive is an actual Lebesgue integral. A distribution with zero weak
derivative is proved to be almost everywhere constant by real convolution,
not assumed to have a continuous representative.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.FluxRepresentative

open MeasureTheory OQ14.FluxSlices Filter
open scoped Topology Convolution Manifold

def smooth (f : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ)) : ℝ → ℝ :=
  convolution f (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume

def reflectedTest (φ : ContDiffBump (0 : ℝ)) (x : ℝ) : LineTest Set.univ where
  function := fun y => φ.normed volume (x - y)
  regular := φ.contDiff_normed.comp (contDiff_const.sub contDiff_id)
  compact := φ.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
  inside := Set.subset_univ _

theorem reflectedTest_deriv (φ : ContDiffBump (0 : ℝ)) (x y : ℝ) :
    deriv (reflectedTest φ x).function y = -deriv (φ.normed volume) (x - y) := by
  have hφ : Differentiable ℝ (φ.normed volume) :=
    (φ.contDiff_normed (n := (1 : ℕ∞))).differentiable le_rfl
  have hh := (hφ (x - y)).hasDerivAt.comp y
    ((hasDerivAt_const y x).sub (hasDerivAt_id y))
  simpa [reflectedTest, Function.comp_def] using hh.deriv

theorem smooth_deriv (f : ℝ → ℝ) (hf : LocallyIntegrable f)
    (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    deriv (smooth f φ) x = ∫ y, f y * deriv (φ.normed volume) (x - y) := by
  have hφ : ContDiff ℝ 1 (φ.normed volume) := φ.contDiff_normed
  have hh := φ.hasCompactSupport_normed.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hf hφ x
  change (fderiv ℝ (convolution f (φ.normed volume) (ContinuousLinearMap.mul ℝ ℝ) volume) x) 1 = _
  rw [hh.fderiv, convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf
    (φ.hasCompactSupport_normed.fderiv ℝ) (hφ.continuous_fderiv le_rfl)]
  simp only [convolution, ContinuousLinearMap.mul_apply', fderiv_deriv]

theorem smooth_eq_bump (f : ℝ → ℝ) (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    smooth f φ x = convolution (φ.normed volume) f (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  rw [convolution_eq_swap]
  simp only [smooth, convolution, ContinuousLinearMap.lsmul_apply,
    ContinuousLinearMap.mul_apply', smul_eq_mul, mul_comm]

def shrinkingBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by apply div_lt_div_of_pos_right (by norm_num); positivity

theorem shrinkingBump_tendsto :
    Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, ← mul_div_assoc, mul_one, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)

theorem smooth_ae_tendsto (f : ℝ → ℝ) (hf : LocallyIntegrable f) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smooth f (shrinkingBump n) x) atTop (𝓝 (f x)) := by
  have hr : ∀ᶠ n in atTop, (shrinkingBump n).rOut ≤ 2 * (shrinkingBump n).rIn :=
    Eventually.of_forall (fun n => by simp [shrinkingBump, div_eq_mul_inv])
  simpa only [smooth_eq_bump] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable shrinkingBump_tendsto hr hf

/-- A genuine locally integrable distribution with zero weak derivative is a.e. constant. -/
theorem ae_constant_of_weak_derivative_zero (f : ℝ → ℝ) (hf : LocallyIntegrable f)
    (hz : ∀ θ : LineTest Set.univ, (∫ x, f x * deriv θ.function x) = 0) :
    ∃ c : ℝ, f =ᵐ[volume] (fun _ => c) := by
  have hs (φ : ContDiffBump (0 : ℝ)) (x y : ℝ) : smooth f φ x = smooth f φ y := by
    apply is_const_of_deriv_eq_zero
    · exact (φ.hasCompactSupport_normed.contDiff_convolution_right
        (ContinuousLinearMap.mul ℝ ℝ) hf (φ.contDiff_normed (n := (1 : ℕ∞)))).differentiable le_rfl
    · intro z
      have hh := hz (reflectedTest φ z)
      simp only [reflectedTest_deriv, mul_neg, integral_neg, neg_eq_zero] at hh
      rw [smooth_deriv f hf φ z]
      exact hh
  have ha := smooth_ae_tendsto f hf
  obtain ⟨x₀, hx₀⟩ := ha.exists
  refine ⟨f x₀, ?_⟩
  filter_upwards [ha] with x hx
  have heq : (fun n => smooth f (shrinkingBump n) x) =
      (fun n => smooth f (shrinkingBump n) x₀) := funext (fun n => hs _ x x₀)
  rw [heq] at hx
  exact tendsto_nhds_unique hx hx₀

def primitive (g : ℝ → ℝ) (x : ℝ) : ℝ := ∫ y in Set.Iic x, g y

theorem primitive_continuous (g : ℝ → ℝ) (hg : Integrable g) : Continuous (primitive g) := by
  have heq : primitive g = fun x => primitive g 0 + ∫ y in (0 : ℝ)..x, g y := by
    funext x
    have h := intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := x)
      hg.integrableOn hg.integrableOn
    change primitive g x - primitive g 0 = _ at h
    linarith
  rw [heq]
  exact continuous_const.add (hg.continuous_primitive 0)

theorem primitive_increment (g : ℝ → ℝ) (hg : Integrable g) (a b : ℝ) :
    primitive g b - primitive g a = ∫ x in a..b, g x :=
  intervalIntegral.integral_Iic_sub_Iic hg.integrableOn hg.integrableOn

/-- The actual L1 primitive satisfies integration by parts against compact C1 tests. -/
theorem primitive_test_identity (g : ℝ → ℝ) (hg : Integrable g)
    (θ : LineTest Set.univ) :
    (∫ x, primitive g x * deriv θ.function x) = -(∫ x, g x * θ.function x) := by
  let K : ℝ × ℝ → ℝ := fun p => if p.1 ≤ p.2 then g p.1 * deriv θ.function p.2 else 0
  have hθd : Integrable (deriv θ.function) :=
    (θ.regular.continuous_deriv le_rfl).integrable_of_hasCompactSupport θ.compact.deriv
  have hK : Integrable K := by
    exact (hg.mul_prod hθd).indicator (measurableSet_le measurable_fst measurable_snd)
  have hleft (x : ℝ) : (∫ y, K (y, x)) = primitive g x * deriv θ.function x := by
    have heq : (fun y => K (y, x)) =
        (Set.Iic x).indicator (fun y => g y * deriv θ.function x) := by
      funext y
      by_cases hy : y ≤ x <;> simp [K, hy]
    rw [heq, integral_indicator measurableSet_Iic, integral_mul_const]
    rfl
  have hright (y : ℝ) : (∫ x, K (y, x)) = -(g y * θ.function y) := by
    have heq : (fun x => K (y, x)) =
        (Set.Ici y).indicator (fun x => g y * deriv θ.function x) := by
      funext x
      by_cases hx : y ≤ x <;> simp [K, hx]
    rw [heq, integral_indicator measurableSet_Ici, integral_const_mul,
      integral_Ici_eq_integral_Ioi, θ.compact.integral_Ioi_deriv_eq θ.regular]
    ring
  have hh := integral_integral_swap (f := fun y x => K (y, x)) hK
  simp only [hleft, hright, integral_neg] at hh
  exact hh.symm

/-- A whole-line L1 weak derivative has an actual continuous representative,
with every increment equal to the integral of the prescribed weak derivative. -/
theorem continuous_representative (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn Set.univ f g) :
    ∃ F : ℝ → ℝ, Continuous F ∧ f =ᵐ[volume] F ∧
      ∀ a b, F b - F a = ∫ x in a..b, g x := by
  have hp := primitive_continuous g hg
  have hz : ∀ θ : LineTest Set.univ,
      (∫ x, (f x - primitive g x) * deriv θ.function x) = 0 := by
    intro θ
    have hθd := θ.regular.continuous_deriv le_rfl
    have hfd : Integrable (fun x => f x * deriv θ.function x) := by
      simpa only [mul_comm] using hf.bdd_mul hθd.aestronglyMeasurable
        (hθd.bounded_above_of_compact_support θ.compact.deriv)
    have hgd : Integrable (fun x => primitive g x * deriv θ.function x) :=
      (hp.mul hθd).integrable_of_hasCompactSupport θ.compact.deriv.mul_left
    have hgθ : Integrable (fun x => θ.function x * g x) :=
      hg.bdd_mul θ.regular.continuous.aestronglyMeasurable
        (θ.regular.continuous.bounded_above_of_compact_support θ.compact)
    have hh := hw θ
    rw [integral_add (by simpa only [mul_comm] using hfd) hgθ] at hh
    simp only [sub_mul]
    rw [integral_sub hfd hgd, primitive_test_identity g hg θ]
    simpa only [mul_comm, sub_neg_eq_add] using hh
  obtain ⟨c, hc⟩ := ae_constant_of_weak_derivative_zero (fun x => f x - primitive g x)
    (hf.locallyIntegrable.sub hp.locallyIntegrable) hz
  refine ⟨fun x => c + primitive g x, continuous_const.add hp, ?_, ?_⟩
  · filter_upwards [hc] with x hx
    linarith
  · intro a b
    rw [add_sub_add_left_eq_sub, primitive_increment g hg a b]

/-- A genuine smooth cutoff, equal to one near a given compact set. -/
theorem exists_line_cutoff {I K : Set ℝ} (hI : IsOpen I) (hK : IsCompact K)
    (hKI : K ⊆ I) : ∃ κ : LineTest I,
      ∀ x ∈ K, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
  obtain ⟨V, hV, hKV, hVI, hcV⟩ :=
    exists_open_between_and_isCompact_closure hK hI hKI
  obtain ⟨f, hf1, hf0, _⟩ := exists_smooth_one_nhds_of_subset_interior
    (𝓘(ℝ, ℝ)) (t := V) hK.isClosed (by simpa [hV.interior_eq] using hKV)
  have hs : Function.support f ⊆ V := by
    intro x hx
    by_contra hn
    exact hx (hf0 x hn)
  have hts : tsupport f ⊆ closure V := closure_mono hs
  refine ⟨⟨f, f.contMDiff.contDiff.of_le (by simp),
    hcV.of_isClosed_subset isClosed_closure hts, hts.trans hVI⟩, ?_⟩
  intro x hx
  exact hf1.filter_mono (nhds_le_nhdsSet hx)

def lineProductTest {I : Set ℝ} (κ : LineTest I) (θ : LineTest Set.univ) : LineTest I where
  function := fun x => κ.function x * θ.function x
  regular := κ.regular.mul θ.regular
  compact := κ.compact.mul_right
  inside := tsupport_mul_subset_left.trans κ.inside

theorem lineProductTest_deriv {I : Set ℝ} (κ : LineTest I) (θ : LineTest Set.univ) (x : ℝ) :
    deriv (lineProductTest κ θ).function x =
      deriv κ.function x * θ.function x + κ.function x * deriv θ.function x :=
  deriv_mul ((κ.regular.differentiable le_rfl) x) ((θ.regular.differentiable le_rfl) x)

/-- Localization of the actual distributional derivative by the proved product rule. -/
theorem cutoff_weak_derivative {I : Set ℝ} (κ : LineTest I) (f g : ℝ → ℝ)
    (hw : HasWeakDerivativeOn I f g) :
    HasWeakDerivativeOn Set.univ (fun x => κ.function x * f x)
      (fun x => κ.function x * g x + deriv κ.function x * f x) := by
  intro θ
  have h := hw (lineProductTest κ θ)
  convert h using 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun x => by
    dsimp only
    rw [lineProductTest_deriv]
    simp only [lineProductTest]
    ring)

theorem cutoff_integrable {I : Set ℝ} (κ : LineTest I) (f g : ℝ → ℝ)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun x => κ.function x * f x) ∧
    Integrable (fun x => κ.function x * g x + deriv κ.function x * f x) := by
  have hk := κ.regular.continuous
  have hd := κ.regular.continuous_deriv le_rfl
  exact ⟨hf.bdd_mul hk.aestronglyMeasurable (hk.bounded_above_of_compact_support κ.compact),
    (hg.bdd_mul hk.aestronglyMeasurable (hk.bounded_above_of_compact_support κ.compact)).add
      (hf.bdd_mul hd.aestronglyMeasurable (hd.bounded_above_of_compact_support κ.compact.deriv))⟩

/-- On every compact interval inside the open weak-derivative region, the L1
slice has a continuous representative with the exact integral increment law. -/
theorem local_continuous_representative {I : Set ℝ} (hI : IsOpen I)
    (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hw : HasWeakDerivativeOn I f g) {a b : ℝ} (hab : Set.Icc a b ⊆ I) :
    ∃ F : ℝ → ℝ, Continuous F ∧ f =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      ∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b, F d - F c = ∫ x in c..d, g x := by
  obtain ⟨κ, hκ⟩ := exists_line_cutoff hI isCompact_Icc hab
  obtain ⟨hi, hj⟩ := cutoff_integrable κ f g hf hg
  obtain ⟨F, hF, hae, hinc⟩ := continuous_representative _ _ hi hj
    (cutoff_weak_derivative κ f g hw)
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_Icc] with x hx hm
    simpa only [(hκ x hm).eq_of_nhds, one_mul] using hx
  · intro c hc d hd
    rw [hinc]
    apply intervalIntegral.integral_congr
    intro x hx
    have hm := Set.uIcc_subset_Icc hc hd hx
    have he := hκ x hm
    have hderiv : deriv κ.function x = 0 := by
      simpa using he.deriv_eq
    dsimp only
    rw [he.eq_of_nhds, hderiv]
    ring

/-- The endpoint values of this representative are determined by its a.e. class
on any nondegenerate interval. -/
theorem representative_unique {a b : ℝ} (hab : a < b) {F G : ℝ → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (hae : F =ᵐ[volume.restrict (Set.Icc a b)] G) : Set.EqOn F G (Set.Icc a b) := by
  have hopen := Measure.eqOn_open_of_ae_eq
    (ae_restrict_of_ae_restrict_of_subset Set.Ioo_subset_Icc_self hae)
    isOpen_Ioo hF.continuousOn hG.continuousOn
  simpa only [closure_Ioo hab.ne] using hopen.closure hF hG

/-- Actual regional weak Maxwell fields therefore determine continuous weighted
plane flux values throughout each closed interval in the axial collar. -/
theorem maxwell_continuous_flux {Ω : Set OQ14.Maxwell.Space} {I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I) (ψ : PlaneTest)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : OQ14.Maxwell.Space → ℝ) (E H : OQ14.DomainCurl.HCurl Ω)
    (hM : OQ14.WeakConservation.WeakMaxwell ω μ ε E H)
    {a b : ℝ} (hab : Set.Icc a b ⊆ I) :
    ∃ F : ℝ → ℝ, Continuous F ∧
      fluxSlice ψ (zeroExtendedPower Ω E H) =ᵐ[volume.restrict (Set.Icc a b)] F ∧
      ∀ c ∈ Set.Icc a b, ∀ d ∈ Set.Icc a b,
        F d - F c = ∫ z in c..d, derivativeSlice ψ (zeroExtendedPower Ω E H) z := by
  obtain ⟨hf, hg, hw⟩ := maxwell_flux_slices hΩ ψ hbox ω μ ε E H hM
  exact local_continuous_representative hI _ _ hf hg hw hab

end OQ14.FluxRepresentative

#print axioms OQ14.FluxRepresentative.smooth_deriv
#print axioms OQ14.FluxRepresentative.smooth_ae_tendsto
#print axioms OQ14.FluxRepresentative.ae_constant_of_weak_derivative_zero
#print axioms OQ14.FluxRepresentative.primitive_continuous
#print axioms OQ14.FluxRepresentative.primitive_increment
#print axioms OQ14.FluxRepresentative.primitive_test_identity
#print axioms OQ14.FluxRepresentative.continuous_representative
#print axioms OQ14.FluxRepresentative.exists_line_cutoff
#print axioms OQ14.FluxRepresentative.cutoff_weak_derivative
#print axioms OQ14.FluxRepresentative.cutoff_integrable
#print axioms OQ14.FluxRepresentative.local_continuous_representative
#print axioms OQ14.FluxRepresentative.representative_unique
#print axioms OQ14.FluxRepresentative.maxwell_continuous_flux
