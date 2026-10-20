import ModalScaling

/-! # Actual shell-response poles after positive frequency scaling

The shell response is composed with multiplication by the physical radius.
Its punctured analytic normal form proves the exact pole order and the
operator-norm residue factor. This remains the spherical matching response.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.ModalScaledPole

open Complex MeasureTheory Filter OQ14.Maxwell OQ14.ModalAlgebra OQ14.ModalMatching OQ14.ModalShell
  OQ14.ModalFieldResidue OQ14.ModalFieldPole OQ14.ModalScaling
open scoped Topology ENNReal

def scaledResponse (n : ℂ) (s : ℝ) (k : ℂ) : Amplitudes →L[ℂ] ShellL2 :=
  response n ((s : ℂ)*k)

def scaledRegularized (n : ℂ) (s : ℝ) (k₀ k : ℂ) : Amplitudes →L[ℂ] ShellL2 :=
  ((s : ℂ)⁻¹) • regularized n k₀ ((s : ℂ)*k)

theorem scaled_center (s : ℝ) (hs : 0 < s) (k₀ : ℂ) :
    (s : ℂ)*(k₀/(s : ℂ)) = k₀ := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  field_simp [hs0]

theorem scaledRegularized_analytic (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency)
    (hn : n ≠ 0) (hd : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    AnalyticAt ℂ (scaledRegularized n s k₀.1) (k₀.1/(s : ℂ)) := by
  have ha : AnalyticAt ℂ (regularized n k₀.1)
      ((s : ℂ)*(k₀.1/(s : ℂ))) := by
    rw [scaled_center s hs]
    exact regularized_analytic n k₀.1 hn k₀.property hd
  unfold scaledRegularized
  exact (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (s : ℂ)⁻¹) _).smul
    (ha.comp (analyticAt_const.mul analyticAt_id))

theorem scaledRegularized_center (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency) :
    scaledRegularized n s k₀.1 (k₀.1/(s : ℂ)) =
      ((s : ℂ)⁻¹) • residueOperator n k₀ := by
  rw [scaledRegularized, scaled_center s hs, regularized_center]

theorem scaledResponse_normal_form (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ k : ℂ)
    (hd : tmDet 1 n k₀ = 0) (hk : k ≠ k₀/(s : ℂ)) :
    scaledResponse n s k = (k-k₀/(s : ℂ))⁻¹ • scaledRegularized n s k₀ k := by
  have hs0 : (s : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs.ne'
  have hsk : (s : ℂ)*k ≠ k₀ := by
    intro h
    apply hk
    apply (eq_div_iff hs0).mpr
    simpa only [mul_comm] using h
  rw [scaledResponse, response_normal_form n k₀ _ hd hsk, scaledRegularized, smul_smul]
  congr 1
  have he : (s : ℂ)*k-k₀ = (s : ℂ)*(k-k₀/(s : ℂ)) := by
    field_simp
    ring
  rw [he, mul_inv_rev]

theorem scaledResponse_meromorphic (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (hn : n ≠ 0) :
    MeromorphicAt (scaledResponse n s) (k₀.1/(s : ℂ)) := by
  have hda : AnalyticAt ℂ (tmDet 1 n) ((s : ℂ)*(k₀.1/(s : ℂ))) := by
    rw [scaled_center s hs]
    exact determinant_analytic n k₀.1 hn k₀.property
  have hna : AnalyticAt ℂ (numerator n) ((s : ℂ)*(k₀.1/(s : ℂ))) := by
    rw [scaled_center s hs]
    exact numerator_analytic n k₀.1 hn k₀.property
  exact ((hda.comp (analyticAt_const.mul analyticAt_id)).meromorphicAt.inv).smul
    (hna.comp (analyticAt_const.mul analyticAt_id)).meromorphicAt

theorem scaledRegularized_nonzero (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency)
    (hn : n ≠ 0) (hd : tmDet 1 n k₀.1 = 0)
    (hder : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    scaledRegularized n s k₀.1 (k₀.1/(s : ℂ)) ≠ 0 := by
  rw [scaledRegularized_center n s hs]
  exact smul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr hs.ne'))
    (residueOperator_nonzero n k₀ hn hd hder)

theorem scaledResponse_order_minus_one (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (hn : n ≠ 0) (hd : tmDet 1 n k₀.1 = 0)
    (hder : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    (scaledResponse_meromorphic n s hs k₀ hn).order = (-1 : ℤ) := by
  apply (MeromorphicAt.order_eq_int_iff _).mpr
  refine ⟨scaledRegularized n s k₀.1,
    scaledRegularized_analytic n s hs k₀ hn hder,
    scaledRegularized_nonzero n s hs k₀ hn hd hder, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with k hk
  simpa only [zpow_neg_one] using scaledResponse_normal_form n s hs k₀.1 k hd hk

theorem scaledResponse_residue_limit (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (hn : n ≠ 0) (hd : tmDet 1 n k₀.1 = 0)
    (hder : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    Tendsto (fun k : ℂ => (k-k₀.1/(s : ℂ)) • scaledResponse n s k)
      (𝓝[≠] (k₀.1/(s : ℂ))) (𝓝 (((s : ℂ)⁻¹) • residueOperator n k₀)) := by
  have ht := (scaledRegularized_analytic n s hs k₀ hn hder).continuousAt.tendsto.mono_left
    (show 𝓝[≠] (k₀.1/(s : ℂ)) ≤ 𝓝 (k₀.1/(s : ℂ)) from nhdsWithin_le_nhds)
  rw [scaledRegularized_center n s hs] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with k hk
  rw [scaledResponse_normal_form n s hs k₀.1 k hd hk, smul_smul,
    mul_inv_cancel₀ (sub_ne_zero.mpr hk), one_smul]

def physicalShell (s : ℝ) : Set Space := {x | s ≤ ‖x‖ ∧ ‖x‖ ≤ 2*s}

def physicalPoint (s : ℝ) (x : Shell) : Space := s • (x : Space)

def physicalMeasure (s : ℝ) : Measure Shell := ENNReal.ofReal (s^3) • shellMeasure

abbrev PhysicalL2 (s : ℝ) := Lp PairVector 2 (physicalMeasure s)

theorem physicalPoint_shell (s : ℝ) (hs : 0 < s) (x : Shell) :
    physicalPoint s x ∈ physicalShell s := by
  have hn : ‖physicalPoint s x‖ = s*‖(x : Space)‖ := by
    simp [physicalPoint, norm_smul, abs_of_pos hs]
  change s ≤ ‖physicalPoint s x‖ ∧ ‖physicalPoint s x‖ ≤ 2*s
  rw [hn]
  constructor <;> nlinarith [x.property.1, x.property.2]

theorem physicalPoint_injective (s : ℝ) (hs : 0 < s) : Function.Injective (physicalPoint s) := by
  intro x y h
  apply Subtype.ext
  exact smul_right_injective Space hs.ne' h

theorem physicalPoint_range (s : ℝ) (hs : 0 < s) :
    Set.range (physicalPoint s) = physicalShell s := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact physicalPoint_shell s hs x
  · intro hy
    have hn : ‖s⁻¹ • y‖ = ‖y‖/s := by
      simp [norm_smul, abs_of_pos hs, div_eq_mul_inv, mul_comm]
    have hx : s⁻¹ • y ∈ shell := by
      change 1 ≤ ‖s⁻¹ • y‖ ∧ ‖s⁻¹ • y‖ ≤ 2
      rw [hn]
      exact ⟨(le_div_iff₀ hs).mpr (by simpa using hy.1),
        (div_le_iff₀ hs).mpr hy.2⟩
    refine ⟨⟨s⁻¹ • y,hx⟩, ?_⟩
    simp [physicalPoint, smul_smul, hs.ne']

theorem physicalMeasure_map (s : ℝ) (hs : 0 < s) :
    (physicalMeasure s).map (physicalPoint s) = volume.restrict (physicalShell s) := by
  have hm : Measurable (fun x : Space => s • x) := measurable_const.smul measurable_id
  have he : physicalPoint s = (fun x : Space => s • x) ∘ ((↑) : Shell → Space) := rfl
  have hpre : (fun x : Space => s • x) ⁻¹' physicalShell s = shell := by
    ext x
    simp only [Set.mem_preimage, physicalShell, Set.mem_setOf_eq, shell, norm_smul,
      Real.norm_eq_abs, abs_of_pos hs]
    constructor
    · rintro ⟨h1,h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1,h2⟩
      constructor <;> nlinarith
  have hmeas : MeasurableSet (physicalShell s) :=
    (isClosed_le continuous_const continuous_norm).measurableSet.inter
      (isClosed_le continuous_norm continuous_const).measurableSet
  rw [physicalMeasure, Measure.map_smul, he, ← Measure.map_map hm measurable_subtype_coe,
    shellMeasure_map, ← hpre, ← Measure.restrict_map hm hmeas, Measure.map_addHaar_smul volume hs.ne']
  rw [Measure.restrict_smul, smul_smul]
  have hc : ENNReal.ofReal (s^3) *
      ENNReal.ofReal |(s^Module.finrank ℝ Space)⁻¹| = 1 := by
    simp only [finrank_euclideanSpace, Fintype.card_fin, abs_of_pos (inv_pos.mpr (pow_pos hs 3))]
    rw [← ENNReal.ofReal_mul (by positivity)]
    simp [hs.ne']
  rw [hc, one_smul]

def physicalLiftRaw (s : ℝ) (F : ShellL2) : PhysicalL2 s :=
  ((Lp.memLp F).smul_measure ENNReal.ofReal_ne_top).toLp F

theorem physicalLiftRaw_ae (s : ℝ) (F : ShellL2) :
    (physicalLiftRaw s F : Shell → PairVector) =ᵐ[physicalMeasure s] F :=
  MemLp.coeFn_toLp _

def physicalNormFactor (s : ℝ) : ℝ :=
  ENNReal.toReal ((ENNReal.ofReal (s^3)) ^ ((1/(2 : ℝ≥0∞)).toReal))

theorem physicalLiftRaw_norm (s : ℝ) (F : ShellL2) :
    ‖physicalLiftRaw s F‖ = physicalNormFactor s * ‖F‖ := by
  rw [physicalLiftRaw, Lp.norm_toLp, physicalMeasure, eLpNorm_smul_measure_of_ne_top (by norm_num),
    smul_eq_mul, ENNReal.toReal_mul, Lp.norm_def]
  rfl

def physicalLiftLinear (s : ℝ) : ShellL2 →ₗ[ℂ] PhysicalL2 s where
  toFun := physicalLiftRaw s
  map_add' F G := by
    apply Lp.ext
    filter_upwards [physicalLiftRaw_ae s (F+G), physicalLiftRaw_ae s F,
      physicalLiftRaw_ae s G, Lp.coeFn_add (physicalLiftRaw s F) (physicalLiftRaw s G),
      Measure.ae_smul_measure (Lp.coeFn_add F G) (ENNReal.ofReal (s^3))] with x hfg hf hg ha hb
    simp only [Pi.add_apply] at ha hb
    rw [hfg, ha, hf, hg, hb]
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [physicalLiftRaw_ae s (c • F), physicalLiftRaw_ae s F,
      Lp.coeFn_smul c (physicalLiftRaw s F),
      Measure.ae_smul_measure (Lp.coeFn_smul c F) (ENNReal.ofReal (s^3))] with x hcf hf ha hb
    simp only [Pi.smul_apply, RingHom.id_apply] at ha hb ⊢
    rw [hcf, ha, hf, hb]

def physicalLift (s : ℝ) : ShellL2 →L[ℂ] PhysicalL2 s :=
  (physicalLiftLinear s).mkContinuous (physicalNormFactor s)
    (fun F => le_of_eq (physicalLiftRaw_norm s F))

theorem physicalLift_ae (s : ℝ) (F : ShellL2) :
    (physicalLift s F : Shell → PairVector) =ᵐ[physicalMeasure s] F :=
  physicalLiftRaw_ae s F

theorem physicalLift_norm (s : ℝ) (F : ShellL2) :
    ‖physicalLift s F‖ = physicalNormFactor s * ‖F‖ :=
  physicalLiftRaw_norm s F

theorem physicalLift_injective (s : ℝ) (hs : 0 < s) : Function.Injective (physicalLift s) := by
  intro F G h
  apply Lp.ext
  have ha : (F : Shell → PairVector) =ᵐ[physicalMeasure s] G := by
    apply (physicalLift_ae s F).symm.trans
    rw [h]
    exact physicalLift_ae s G
  exact (Measure.ae_smul_measure_iff (ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hs 3))).mp ha

def physicalPost (s : ℝ) :
    (Amplitudes →L[ℂ] ShellL2) →L[ℂ] (Amplitudes →L[ℂ] PhysicalL2 s) :=
  ContinuousLinearMap.compL ℂ Amplitudes ShellL2 (PhysicalL2 s) (physicalLift s)

def physicalResponse (n : ℂ) (s : ℝ) (k : ℂ) : Amplitudes →L[ℂ] PhysicalL2 s :=
  physicalPost s (scaledResponse n s k)

def physicalRegularized (n : ℂ) (s : ℝ) (k₀ k : ℂ) : Amplitudes →L[ℂ] PhysicalL2 s :=
  physicalPost s (scaledRegularized n s k₀ k)

def physicalResidue (n : ℂ) (s : ℝ) (k₀ : Frequency) : Amplitudes →L[ℂ] PhysicalL2 s :=
  physicalPost s (((s : ℂ)⁻¹) • residueOperator n k₀)

theorem physicalPost_injective (s : ℝ) (hs : 0 < s) : Function.Injective (physicalPost s) := by
  intro T U h
  apply ContinuousLinearMap.ext
  intro f
  apply physicalLift_injective s hs
  exact congrArg (fun V : Amplitudes →L[ℂ] PhysicalL2 s => V f) h

theorem clm_meromorphic {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (T : E →L[ℂ] F)
    (g : ℂ → E) (z₀ : ℂ) (hg : MeromorphicAt g z₀) :
    MeromorphicAt (fun z => T (g z)) z₀ := by
  obtain ⟨m,hm⟩ := hg
  refine ⟨m, ?_⟩
  have h := (T.analyticAt _).comp hm
  simpa only [Function.comp_def, map_smul] using h

theorem physicalRegularized_analytic (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency)
    (hn : n ≠ 0) (hd : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    AnalyticAt ℂ (physicalRegularized n s k₀.1) (k₀.1/(s : ℂ)) :=
  ((physicalPost s).analyticAt _).comp (scaledRegularized_analytic n s hs k₀ hn hd)

theorem physicalRegularized_center (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency) :
    physicalRegularized n s k₀.1 (k₀.1/(s : ℂ)) = physicalResidue n s k₀ := by
  rw [physicalRegularized, scaledRegularized_center n s hs]
  rfl

theorem physicalResidue_nonzero (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency)
    (hn : n ≠ 0) (hd : tmDet 1 n k₀.1 = 0)
    (hder : deriv (tmDet 1 n) k₀.1 ≠ 0) : physicalResidue n s k₀ ≠ 0 := by
  intro hz
  have hzero : ((s : ℂ)⁻¹) • residueOperator n k₀ = 0 :=
    physicalPost_injective s hs (by simpa only [map_zero] using hz)
  exact (smul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr hs.ne'))
    (residueOperator_nonzero n k₀ hn hd hder)) hzero

theorem physicalResidue_apply_nonzero (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (f : Amplitudes) (hf : residueOperator n k₀ f ≠ 0) :
    physicalResidue n s k₀ f ≠ 0 := by
  intro hz
  have hzero : ((s : ℂ)⁻¹) • residueOperator n k₀ f = 0 :=
    physicalLift_injective s hs (by simpa only [map_zero] using hz)
  exact (smul_ne_zero (inv_ne_zero (ofReal_ne_zero.mpr hs.ne')) hf) hzero

theorem physicalResponse_meromorphic (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (hn : n ≠ 0) :
    MeromorphicAt (physicalResponse n s) (k₀.1/(s : ℂ)) :=
  clm_meromorphic (physicalPost s) _ _ (scaledResponse_meromorphic n s hs k₀ hn)

theorem physicalResponse_normal_form (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ k : ℂ)
    (hd : tmDet 1 n k₀ = 0) (hk : k ≠ k₀/(s : ℂ)) :
    physicalResponse n s k = (k-k₀/(s : ℂ))⁻¹ • physicalRegularized n s k₀ k := by
  rw [physicalResponse, scaledResponse_normal_form n s hs k₀ k hd hk, map_smul]
  rfl

theorem physicalResponse_order_minus_one (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (hn : n ≠ 0) (hd : tmDet 1 n k₀.1 = 0)
    (hder : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    (physicalResponse_meromorphic n s hs k₀ hn).order = (-1 : ℤ) := by
  apply (MeromorphicAt.order_eq_int_iff _).mpr
  refine ⟨physicalRegularized n s k₀.1,
    physicalRegularized_analytic n s hs k₀ hn hder, ?_, ?_⟩
  · rw [physicalRegularized_center n s hs]
    exact physicalResidue_nonzero n s hs k₀ hn hd hder
  · filter_upwards [self_mem_nhdsWithin] with k hk
    simpa only [zpow_neg_one] using physicalResponse_normal_form n s hs k₀.1 k hd hk

theorem physicalResponse_residue_limit (n : ℂ) (s : ℝ) (hs : 0 < s)
    (k₀ : Frequency) (hn : n ≠ 0) (hd : tmDet 1 n k₀.1 = 0)
    (hder : deriv (tmDet 1 n) k₀.1 ≠ 0) :
    Tendsto (fun k : ℂ => (k-k₀.1/(s : ℂ)) • physicalResponse n s k)
      (𝓝[≠] (k₀.1/(s : ℂ))) (𝓝 (physicalResidue n s k₀)) := by
  have ht := (physicalPost s).continuous.continuousAt.tendsto.comp
    (scaledResponse_residue_limit n s hs k₀ hn hd hder)
  simpa only [Function.comp_def, map_smul, physicalResponse, physicalResidue] using ht

theorem physicalResidue_actual (n : ℂ) (s : ℝ) (hs : 0 < s) (k₀ : Frequency)
    (f : Amplitudes) :
    (physicalResidue n s k₀ f : Shell → PairVector) =ᵐ[physicalMeasure s]
      fun x => (((s : ℂ)⁻¹) • dilate s (OQ14.ModalPoleMode.electricMode n k₀.1 f)
          (physicalPoint s x),
        ((s : ℂ)⁻¹) • dilate s (OQ14.ModalPoleMode.magneticMode n k₀.1 f)
          (physicalPoint s x)) := by
  change (physicalLift s (((s : ℂ)⁻¹) • residueOperator n k₀ f) : Shell → PairVector) =ᵐ[_] _
  filter_upwards [physicalLift_ae s (((s : ℂ)⁻¹) • residueOperator n k₀ f),
    Measure.ae_smul_measure (Lp.coeFn_smul ((s : ℂ)⁻¹) (residueOperator n k₀ f))
      (ENNReal.ofReal (s^3)),
    Measure.ae_smul_measure (OQ14.ModalPoleMode.residue_shell_actual n k₀ f)
      (ENNReal.ofReal (s^3))] with x hl hsm ha
  rw [hl, hsm, Pi.smul_apply, ha]
  simp only [Pi.smul_apply, Prod.smul_mk, dilate, physicalPoint,
    smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

theorem physicalResponse_actual (n : ℂ) (s : ℝ) (hs : 0 < s) (k : Frequency)
    (f : Amplitudes) :
    (physicalResponse n s (k.1/(s : ℂ)) f : Shell → PairVector) =ᵐ[physicalMeasure s]
      fun x => (dilate s (OQ14.ModalInterface.outerE k.1 (solve 1 n k.1 f).2)
          (physicalPoint s x),
        dilate s (OQ14.ModalInterface.outerH k.1 (solve 1 n k.1 f).2)
          (physicalPoint s x)) := by
  have heq : physicalResponse n s (k.1/(s : ℂ)) f =
      physicalLift s (responseOperator n k f) := by
    change physicalLift s (response n ((s : ℂ)*(k.1/(s : ℂ))) f) = _
    rw [scaled_center s hs, response_eq_actual]
  rw [heq]
  filter_upwards [physicalLift_ae s (responseOperator n k f),
    Measure.ae_smul_measure (responseOperator_actual n k f) (ENNReal.ofReal (s^3))]
    with x hl ha
  rw [hl, ha]
  simp only [dilate, physicalPoint, smul_smul, inv_mul_cancel₀ hs.ne', one_smul]

/-- Actual simple poles of the volume-weighted physical shell response can
have any prescribed positive real part and arbitrarily large quality. -/
theorem exists_prescribed_physical_shell_poles (n : ℝ) (hn : 1 < n)
    (k0 : ℝ) (hk0 : 0 < k0) (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k : Frequency, ∃ s : ℝ, 0 < s ∧
      (k.1/(s : ℂ)).re = k0 ∧ (k.1/(s : ℂ)).im < 0 ∧
      Q < (k.1/(s : ℂ)).re / (-2*(k.1/(s : ℂ)).im) ∧
      tmDet 1 (n : ℂ) k.1 = 0 ∧ deriv (tmDet 1 (n : ℂ)) k.1 ≠ 0 ∧
      (∃ hm : MeromorphicAt (physicalResponse (n : ℂ) s) (k.1/(s : ℂ)),
        hm.order = (-1 : ℤ)) ∧ physicalResidue (n : ℂ) s k ≠ 0 ∧
      Tendsto (fun z : ℂ => (z-k.1/(s : ℂ)) • physicalResponse (n : ℂ) s z)
        (𝓝[≠] (k.1/(s : ℂ))) (𝓝 (physicalResidue (n : ℂ) s k)) := by
  obtain ⟨k,hk,hd,hder,hre,him,hqual⟩ :=
    OQ14.ModalAsymptotics.tm_high_quality_zeros 1 n hn 0 Q hQ
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  let s : ℝ := k.re/k0
  obtain ⟨hs,hsre,hsim,hsQ⟩ := prescribed_frequency_scale k hre him k0 hk0
  refine ⟨⟨k,hk⟩,s,hs,hsre,hsim,?_,hd,hder,
    ⟨physicalResponse_meromorphic (n : ℂ) s hs ⟨k,hk⟩ hn0,
      physicalResponse_order_minus_one (n : ℂ) s hs ⟨k,hk⟩ hn0 hd hder⟩,
    physicalResidue_nonzero (n : ℂ) s hs ⟨k,hk⟩ hn0 hd hder,
    physicalResponse_residue_limit (n : ℂ) s hs ⟨k,hk⟩ hn0 hd hder⟩
  rw [hsQ]
  exact hqual

end OQ14.ModalScaledPole

#print axioms OQ14.ModalScaledPole.scaled_center
#print axioms OQ14.ModalScaledPole.scaledRegularized_analytic
#print axioms OQ14.ModalScaledPole.scaledRegularized_center
#print axioms OQ14.ModalScaledPole.scaledResponse_normal_form
#print axioms OQ14.ModalScaledPole.scaledResponse_meromorphic
#print axioms OQ14.ModalScaledPole.scaledRegularized_nonzero
#print axioms OQ14.ModalScaledPole.scaledResponse_order_minus_one
#print axioms OQ14.ModalScaledPole.scaledResponse_residue_limit
#print axioms OQ14.ModalScaledPole.physicalPoint_shell
#print axioms OQ14.ModalScaledPole.physicalPoint_injective
#print axioms OQ14.ModalScaledPole.physicalPoint_range
#print axioms OQ14.ModalScaledPole.physicalMeasure_map
#print axioms OQ14.ModalScaledPole.physicalLiftRaw_ae
#print axioms OQ14.ModalScaledPole.physicalLiftRaw_norm
#print axioms OQ14.ModalScaledPole.physicalLift_ae
#print axioms OQ14.ModalScaledPole.physicalLift_norm
#print axioms OQ14.ModalScaledPole.physicalLift_injective
#print axioms OQ14.ModalScaledPole.physicalPost_injective
#print axioms OQ14.ModalScaledPole.clm_meromorphic
#print axioms OQ14.ModalScaledPole.physicalRegularized_analytic
#print axioms OQ14.ModalScaledPole.physicalRegularized_center
#print axioms OQ14.ModalScaledPole.physicalResidue_nonzero
#print axioms OQ14.ModalScaledPole.physicalResidue_apply_nonzero
#print axioms OQ14.ModalScaledPole.physicalResponse_meromorphic
#print axioms OQ14.ModalScaledPole.physicalResponse_normal_form
#print axioms OQ14.ModalScaledPole.physicalResponse_order_minus_one
#print axioms OQ14.ModalScaledPole.physicalResponse_residue_limit
#print axioms OQ14.ModalScaledPole.physicalResidue_actual
#print axioms OQ14.ModalScaledPole.physicalResponse_actual
#print axioms OQ14.ModalScaledPole.exists_prescribed_physical_shell_poles
