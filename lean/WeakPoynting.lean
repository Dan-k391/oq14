import HCurl
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Smoothing actual weak H(curl) fields

This module begins the analytic bridge needed for weak-field Poynting identities.
Convolution is the actual Lebesgue integral. Curl commutation is proved from
the distributional equation, using translated compact C1 kernel tests.
The arbitrary-H(curl) Poynting product identity is not assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.WeakPoynting

open MeasureTheory OQ14.Maxwell OQ14.WeakCurl
open scoped ComplexConjugate Topology Convolution
open Filter

def smoothScalar (ρ : Space → ℂ) (u : L2Scalar) : Space → ℂ :=
  convolution u ρ (ContinuousLinearMap.mul ℝ ℂ) volume

theorem smoothScalar_integral (ρ : Space → ℂ) (u : L2Scalar) (x : Space) :
    smoothScalar ρ u x = ∫ y, u y * ρ (x - y) := rfl

theorem smoothScalar_regular {n : ℕ∞} {ρ : Space → ℂ}
    (hρ : ContDiff ℝ n ρ) (hc : HasCompactSupport ρ) (u : L2Scalar) :
    ContDiff ℝ n (smoothScalar ρ u) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    ((Lp.memLp u).locallyIntegrable (by norm_num)) hρ

def shiftedTest (ρ : Test) (x : Space) : Test where
  function := fun y => ρ.function (x - y)
  regular := ρ.regular.comp (contDiff_const.sub contDiff_id)
  compact := ρ.compact.comp_homeomorph (Homeomorph.subLeft x)

theorem shiftedTest_partial (ρ : Test) (x y : Space) (i : Fin 3) :
    dcoord (shiftedTest ρ x).function y i = -dcoord ρ.function (x - y) i := by
  have hh := ((ρ.regular.differentiable (by norm_num)) (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  have hv := congrArg (fun L : Space →L[ℝ] ℂ => L (basis i)) hh.fderiv
  simpa [shiftedTest, dcoord, Function.comp_def] using hv

theorem smoothScalar_partial (ρ : Test) (u : L2Scalar) (x : Space) (i : Fin 3) :
    dcoord (smoothScalar ρ.function u) x i =
      ∫ y, u y * dcoord ρ.function (x - y) i := by
  have hu := (Lp.memLp u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hh := ρ.compact.hasFDerivAt_convolution_right
    (ContinuousLinearMap.mul ℝ ℂ) hu ρ.regular x
  change (fderiv ℝ (convolution u ρ.function (ContinuousLinearMap.mul ℝ ℂ) volume) x)
    (basis i) = _
  rw [hh.fderiv, convolution_precompR_apply
    (ContinuousLinearMap.mul ℝ ℂ) hu (ρ.compact.fderiv ℝ)
    (ρ.regular.continuous_fderiv le_rfl)]
  rfl

def smoothField (ρ : Space → ℂ) (E : L2Vector) : Field :=
  fun x j => smoothScalar ρ (E j) x

theorem curl_component (F : Field) (x : Space) (j : Fin 3) :
    curl F x j = pd F x (next j) (previous j) - pd F x (previous j) (next j) := by
  fin_cases j <;> rfl

/-- Actual convolution commutes with the distributional curl of an L2 field. -/
theorem curl_smoothField (ρ : Test) {E C : L2Vector} (h : HasWeakCurl E C)
    (x : Space) : curl (smoothField ρ.function E) x = smoothField ρ.function C x := by
  funext j
  have hh := (hasWeakCurl_iff_integral E C).mp h (shiftedTest ρ x) j
  simp only [shiftedTest_partial, mul_neg, integral_neg] at hh
  rw [curl_component]
  change dcoord (smoothScalar ρ.function (E (previous j))) x (next j) -
    dcoord (smoothScalar ρ.function (E (next j))) x (previous j) =
      smoothScalar ρ.function (C j) x
  rw [smoothScalar_partial, smoothScalar_partial, smoothScalar_integral]
  simpa [shiftedTest, sub_eq_add_neg, add_comm] using hh.symm

def complexKernel (φ : ContDiffBump (0 : Space)) : Space → ℂ :=
  fun x => (φ.normed volume x : ℂ)

theorem complexKernel_regular (φ : ContDiffBump (0 : Space)) :
    ContDiff ℝ (⊤ : ℕ∞) (complexKernel φ) :=
  Complex.ofRealCLM.contDiff.comp φ.contDiff_normed

theorem complexKernel_compact (φ : ContDiffBump (0 : Space)) :
    HasCompactSupport (complexKernel φ) :=
  φ.hasCompactSupport_normed.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

theorem smoothScalar_complexKernel (φ : ContDiffBump (0 : Space))
    (u : L2Scalar) (x : Space) :
    smoothScalar (complexKernel φ) u x =
      convolution (φ.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x := by
  rw [convolution_eq_swap]
  simp only [smoothScalar_integral, ContinuousLinearMap.lsmul_apply,
    complexKernel, Complex.real_smul, mul_comm]

/-- Actual pointwise convolutions converge almost everywhere to an arbitrary L2 field. -/
theorem smoothScalar_ae_tendsto (φ : ℕ → ContDiffBump (0 : Space))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) {K : ℝ}
    (hratio : ∀ᶠ n in atTop, (φ n).rOut ≤ K * (φ n).rIn) (u : L2Scalar) :
    ∀ᵐ x ∂volume, Tendsto (fun n => smoothScalar (complexKernel (φ n)) u x)
      atTop (𝓝 (u x)) := by
  simpa only [smoothScalar_complexKernel] using
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hφ hratio
      ((Lp.memLp u).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))

/-- The genuine measure-preserving translation of an L2 equivalence class. -/
def translateL2 (u : L2Scalar) (a : Space) : L2Scalar :=
  Lp.compMeasurePreserving (fun x : Space => x + a) (measurePreserving_add_right volume a) u

theorem translateL2_norm (u : L2Scalar) (a : Space) : ‖translateL2 u a‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u (measurePreserving_add_right volume a)

theorem translateL2_ae (u : L2Scalar) (a : Space) :
    (fun x => translateL2 u a x) =ᵐ[volume] (fun x => u (x + a)) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

theorem translateL2_zero (u : L2Scalar) : translateL2 u 0 = u := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume (0 : Space))]
    with x hx
  simpa [translateL2] using hx

/-- Translation is strongly continuous in the actual L2 norm. -/
theorem translateL2_continuous (u : L2Scalar) : Continuous (translateL2 u) := by
  let g : Space → C(Space, Space) := fun a => ⟨fun x => x + a, continuous_id.add continuous_const⟩
  have hg : Continuous g :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_add_right volume a) (by norm_num)

/-- Bochner averaging of the L2 translation orbit. -/
def averageL2 (φ : ContDiffBump (0 : Space)) (u : L2Scalar) : L2Scalar :=
  convolution (φ.normed volume) (translateL2 u) (ContinuousLinearMap.lsmul ℝ ℝ) volume 0

theorem averageL2_norm_le (φ : ContDiffBump (0 : Space)) (u : L2Scalar) :
    ‖averageL2 φ u‖ ≤ ‖u‖ := by
  unfold averageL2
  rw [convolution_def]
  calc
    ‖∫ y, (ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume y) (translateL2 u (0 - y))‖
      ≤ ∫ y, ‖(ContinuousLinearMap.lsmul ℝ ℝ) (φ.normed volume y)
          (translateL2 u (0 - y))‖ := norm_integral_le_integral_norm _
    _ = ∫ y, φ.normed volume y * ‖u‖ := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp [ContinuousLinearMap.lsmul_apply, norm_smul, translateL2_norm,
        Real.norm_of_nonneg (φ.nonneg_normed y)]
    _ = ‖u‖ := by rw [integral_mul_const, φ.integral_normed, one_mul]

/-- These actual Bochner averages converge in L2 norm, not merely pointwise. -/
theorem averageL2_tendsto (φ : ℕ → ContDiffBump (0 : Space))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) (u : L2Scalar) :
    Tendsto (fun n => averageL2 (φ n) u) atTop (𝓝 u) := by
  have hh := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Space)) hφ (translateL2_continuous u) (0 : Space)
  simpa only [averageL2, translateL2_zero] using hh

def normL2 (u : L2Scalar) : Lp ℝ 2 (volume : Measure Space) :=
  (Lp.memLp u).norm.toLp (fun x => ‖u x‖)

theorem normL2_norm (u : L2Scalar) : ‖normL2 u‖ = ‖u‖ := by
  unfold normL2
  rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm]

theorem integral_norm_mul_le (u v : L2Scalar) :
    (∫ x, ‖u x‖ * ‖v x‖) ≤ ‖u‖ * ‖v‖ := by
  have he : (∫ x, ‖u x‖ * ‖v x‖) =
      @Inner.inner ℝ (Lp ℝ 2 (volume : Measure Space)) _ (normL2 u) (normL2 v) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(Lp.memLp u).norm.coeFn_toLp, (Lp.memLp v).norm.coeFn_toLp]
      with x hx hy
    simp [normL2, hx, hy, real_inner_comm, mul_comm]
  rw [he]
  simpa only [normL2_norm] using real_inner_le_norm (normL2 u) (normL2 v)

/-- Absolute integrability of the kernel/test pairing, enabling genuine Fubini. -/
theorem kernel_test_integrable (q g : Space → ℂ) (hq : Continuous q)
    (hqc : HasCompactSupport q) (hg : Continuous g) (hgc : HasCompactSupport g)
    (u : L2Scalar) :
    Integrable (fun p : Space × Space => q p.2 * u (p.1 - p.2) * g p.1)
      ((volume : Measure Space).prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : Space × Space => q p.2 * u (p.1 - p.2) * g p.1)
      ((volume : Measure Space).prod volume) :=
    (hq.aestronglyMeasurable.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ)
      (Lp.aestronglyMeasurable u)).mul (hg.comp continuous_fst).aestronglyMeasurable
  let v : L2Scalar := (hg.memLp_of_hasCompactSupport hgc).toLp g
  have hv : (fun x => v x) =ᵐ[volume] g :=
    (hg.memLp_of_hasCompactSupport hgc).coeFn_toLp
  have hslice (y : Space) : Integrable (fun x => q y * u (x - y) * g x) := by
    apply ((testPair_integrable g hg hgc (translateL2 u (-y))).const_mul (q y)).congr
    filter_upwards [translateL2_ae u (-y)] with x hx
    simp only [hx, sub_eq_add_neg]
    ring
  have hbound (y : Space) :
      (∫ x, ‖q y * u (x - y) * g x‖) ≤ ‖q y‖ * (‖u‖ * ‖v‖) := by
    calc
      (∫ x, ‖q y * u (x - y) * g x‖) =
          ‖q y‖ * ∫ x, ‖translateL2 u (-y) x‖ * ‖v x‖ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [translateL2_ae u (-y), hv] with x hx hxv
        simp only [hx, hxv, norm_mul, sub_eq_add_neg]
        ring
      _ ≤ ‖q y‖ * (‖u‖ * ‖v‖) := by
        simpa only [translateL2_norm] using
          mul_le_mul_of_nonneg_left (integral_norm_mul_le (translateL2 u (-y)) v)
            (norm_nonneg (q y))
  apply (integrable_prod_iff' hm).mpr
  refine ⟨ae_of_all _ hslice, ?_⟩
  apply ((hq.integrable_of_hasCompactSupport hqc).norm.mul_const (‖u‖ * ‖v‖)).mono'
    hm.prod_swap.norm.integral_prod_right'
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  exact hbound y

/-- Identification by genuine test integrals; Fubini is justified absolutely. -/
theorem averageL2_testPair (φ : ContDiffBump (0 : Space)) (g : Space → ℂ)
    (hg : Continuous g) (hgc : HasCompactSupport g) (u : L2Scalar) :
    testPair g hg hgc (averageL2 φ u) =
      ∫ x, smoothScalar (complexKernel φ) u x * g x := by
  have hp : Continuous (φ.normed (volume : Measure Space)) :=
    (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous
  have hi : Integrable (fun y => φ.normed volume y • translateL2 u (0 - y)) :=
    φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hp.locallyIntegrable (translateL2_continuous u) 0
  have ht (y : Space) : testPair g hg hgc (translateL2 u (0 - y)) =
      ∫ x, u (x - y) * g x := by
    rw [testPair_integral]
    apply integral_congr_ae
    filter_upwards [translateL2_ae u (0 - y)] with x hx
    rw [hx]
    simp [sub_eq_add_neg]
  have hF := kernel_test_integrable (complexKernel φ) g
    (complexKernel_regular φ).continuous (complexKernel_compact φ) hg hgc u
  let L : L2Scalar →L[ℝ] ℂ := (testPair g hg hgc).restrictScalars ℝ
  calc
    testPair g hg hgc (averageL2 φ u) =
        ∫ y, (φ.normed volume y : ℂ) * ∫ x, u (x - y) * g x := by
      change L (∫ y, φ.normed volume y • translateL2 u (0 - y)) = _
      rw [← L.integral_comp_comm hi]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [map_smul]
      change φ.normed volume y • testPair g hg hgc (translateL2 u (0 - y)) = _
      rw [ht, Complex.real_smul]
    _ = ∫ y, ∫ x, complexKernel φ y * u (x - y) * g x := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [complexKernel]
      ring
    _ = ∫ x, ∫ y, complexKernel φ y * u (x - y) * g x :=
      (integral_integral_swap hF).symm
    _ = ∫ x, smoothScalar (complexKernel φ) u x * g x := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [integral_mul_const, smoothScalar_complexKernel, convolution_def]
      rfl

/-- The Bochner L2 average is represented by the actual smooth convolution. -/
theorem averageL2_ae (φ : ContDiffBump (0 : Space)) (u : L2Scalar) :
    (fun x => averageL2 φ u x) =ᵐ[volume] smoothScalar (complexKernel φ) u := by
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (averageL2 φ u)).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2))
    (smoothScalar_regular (complexKernel_regular φ) (complexKernel_compact φ) u).continuous.locallyIntegrable
  intro g hg hgc
  have hh := averageL2_testPair φ (fun x => (g x : ℂ))
    (Complex.continuous_ofReal.comp hg.continuous)
    (hgc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)) u
  rw [testPair_integral] at hh
  simpa only [Complex.real_smul, mul_comm] using hh

theorem smoothScalar_memLp (φ : ContDiffBump (0 : Space)) (u : L2Scalar) :
    MemLp (smoothScalar (complexKernel φ) u) 2 volume :=
  (memLp_congr_ae (averageL2_ae φ u)).mp (Lp.memLp (averageL2 φ u))

def mollifyL2 (φ : ContDiffBump (0 : Space)) (u : L2Scalar) : L2Scalar :=
  (smoothScalar_memLp φ u).toLp (smoothScalar (complexKernel φ) u)

theorem mollifyL2_eq_average (φ : ContDiffBump (0 : Space)) (u : L2Scalar) :
    mollifyL2 φ u = averageL2 φ u := by
  apply Lp.ext
  exact (smoothScalar_memLp φ u).coeFn_toLp.trans (averageL2_ae φ u).symm

/-- Strong L2 convergence of the very same smooth pointwise convolutions. -/
theorem mollifyL2_tendsto (φ : ℕ → ContDiffBump (0 : Space))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) (u : L2Scalar) :
    Tendsto (fun n => mollifyL2 (φ n) u) atTop (𝓝 u) := by
  simpa only [mollifyL2_eq_average] using averageL2_tendsto φ hφ u

def kernelTest (φ : ContDiffBump (0 : Space)) : Test where
  function := complexKernel φ
  regular := (complexKernel_regular φ).of_le (by simp)
  compact := complexKernel_compact φ

def mollifyVector (φ : ContDiffBump (0 : Space)) (E : L2Vector) : L2Vector :=
  fun j => mollifyL2 φ (E j)

theorem mollify_hasWeakCurl (φ : ContDiffBump (0 : Space)) {E C : L2Vector}
    (h : HasWeakCurl E C) : HasWeakCurl (mollifyVector φ E) (mollifyVector φ C) := by
  have hcurl : curl (smoothField (complexKernel φ) E) = smoothField (complexKernel φ) C := by
    funext x
    exact curl_smoothField (kernelTest φ) h x
  have hE : ∀ j, MemLp (fun x => smoothField (complexKernel φ) E x j) 2 volume :=
    fun j => smoothScalar_memLp φ (E j)
  have hC : ∀ j, MemLp (fun x => curl (smoothField (complexKernel φ) E) x j) 2 volume := by
    rw [hcurl]
    exact fun j => smoothScalar_memLp φ (C j)
  have hh := classical_hasWeakCurl (smoothField (complexKernel φ) E)
    (fun j => (smoothScalar_regular (complexKernel_regular φ)
      (complexKernel_compact φ) (E j)).of_le (by simp)) hE hC
  have heq : fieldToL2 (curl (smoothField (complexKernel φ) E)) hC = mollifyVector φ C := by
    funext j
    apply Lp.ext
    filter_upwards [(hC j).coeFn_toLp, (smoothScalar_memLp φ (C j)).coeFn_toLp] with x hx hy
    exact hx.trans ((congrArg (fun F : Field => F x j) hcurl).trans hy.symm)
  rw [heq] at hh
  exact hh

def mollifyHCurl (φ : ContDiffBump (0 : Space)) (u : HCurl) : HCurl :=
  ⟨(mollifyVector φ u.val.1, mollifyVector φ u.val.2), mollify_hasWeakCurl φ u.property⟩

theorem mollifyHCurl_tendsto (φ : ℕ → ContDiffBump (0 : Space))
    (hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0)) (u : HCurl) :
    Tendsto (fun n => mollifyHCurl (φ n) u) atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  exact (tendsto_pi_nhds.mpr (fun j => mollifyL2_tendsto φ hφ (u.val.1 j))).prodMk_nhds
    (tendsto_pi_nhds.mpr (fun j => mollifyL2_tendsto φ hφ (u.val.2 j)))

/-- A graph element has a globally smooth representative and its actual curl. -/
def SmoothGraph (u : HCurl) : Prop :=
  ∃ F : Field, (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j)) ∧
    (∀ j, (fun x => u.val.1 j x) =ᵐ[volume] (fun x => F x j)) ∧
    (∀ j, (fun x => u.val.2 j x) =ᵐ[volume] (fun x => curl F x j))

theorem mollifyHCurl_smooth (φ : ContDiffBump (0 : Space)) (u : HCurl) :
    SmoothGraph (mollifyHCurl φ u) := by
  refine ⟨smoothField (complexKernel φ) u.val.1,
    fun j => smoothScalar_regular (complexKernel_regular φ) (complexKernel_compact φ) _,
    fun j => (smoothScalar_memLp φ (u.val.1 j)).coeFn_toLp, ?_⟩
  intro j
  have hcurl : curl (smoothField (complexKernel φ) u.val.1) =
      smoothField (complexKernel φ) u.val.2 :=
    funext (fun x => curl_smoothField (kernelTest φ) u.property x)
  rw [hcurl]
  exact (smoothScalar_memLp φ (u.val.2 j)).coeFn_toLp

def shrinkingBump (n : ℕ) : ContDiffBump (0 : Space) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right (by norm_num)
    positivity

theorem shrinkingBump_tendsto :
    Tendsto (fun n => (shrinkingBump n).rOut) atTop (𝓝 0) := by
  simpa only [shrinkingBump, ← mul_div_assoc, mul_one, mul_zero] using
    tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)

/-- A genuine smooth graph-norm approximation of every whole-space H(curl) field. -/
theorem smooth_graph_approximation (u : HCurl) :
    ∃ v : ℕ → HCurl, (∀ n, SmoothGraph (v n)) ∧ Tendsto v atTop (𝓝 u) :=
  ⟨fun n => mollifyHCurl (shrinkingBump n) u,
    fun n => mollifyHCurl_smooth (shrinkingBump n) u,
    mollifyHCurl_tendsto shrinkingBump shrinkingBump_tendsto u⟩

end OQ14.WeakPoynting

#print axioms OQ14.WeakPoynting.smoothScalar_regular
#print axioms OQ14.WeakPoynting.shiftedTest_partial
#print axioms OQ14.WeakPoynting.smoothScalar_partial
#print axioms OQ14.WeakPoynting.curl_smoothField
#print axioms OQ14.WeakPoynting.complexKernel_regular
#print axioms OQ14.WeakPoynting.smoothScalar_ae_tendsto
#print axioms OQ14.WeakPoynting.translateL2_continuous
#print axioms OQ14.WeakPoynting.averageL2_norm_le
#print axioms OQ14.WeakPoynting.averageL2_tendsto
#print axioms OQ14.WeakPoynting.kernel_test_integrable
#print axioms OQ14.WeakPoynting.averageL2_ae
#print axioms OQ14.WeakPoynting.smoothScalar_memLp
#print axioms OQ14.WeakPoynting.mollifyL2_tendsto
#print axioms OQ14.WeakPoynting.mollify_hasWeakCurl
#print axioms OQ14.WeakPoynting.mollifyHCurl_tendsto
#print axioms OQ14.WeakPoynting.smooth_graph_approximation
