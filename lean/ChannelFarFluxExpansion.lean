import ChannelScaledFields
import RadialFlux

/-! Far expansion of the sphere flux of the complete field `E = E_in + E_out + E_sc`.

For `r > R` the flux of the complete field on the sphere of radius `r` equals
`g r + Re (exp (-2 i r) * c r)` exactly, with
`g r = - (1/2) Re (I_ii r + I_oo r)` and `c r = - (1/2) (I_io r + conj (I_oi r))` where
`I_xy r = int pair (U_x r n) (T_y r n)` are the sphere pairings of the scaled electric parts `U_x` and the scaled
tangential magnetic traces `T_y` of the incoming part (`x = i`) and of the outgoing part (`x = o`, the outgoing
Hankel part of the incident field plus the scattered field).  By dominated convergence `g → G` and `c → C`, and
`G = (1/2) (int |a_out + F|^2 - int |a_in|^2)` where `a_in` and `a_out` are the incoming and outgoing amplitudes of
the incident field and `F` is the far amplitude of the scattered field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ChannelFarFluxExpansion
open Filter MeasureTheory Topology OQ14.Maxwell OQ14.DebyeRadialTrace OQ14.ChannelScaledFields
abbrev Sphere := OQ14.AngularPower.Sphere
abbrev Idx := SymmetricHarmonicJets.Index

theorem factor_one (r : ℝ) : MaxwellFarField.factor 1 r = RegularTEIncoming.phase false r * (r : ℂ) := by
  unfold MaxwellFarField.factor RegularTEIncoming.phase
  simp only [Complex.ofReal_one, mul_one, Bool.false_eq_true, if_false]
  ring

theorem key_identity (r z w a b c d : ℂ) (hzw : z * w = 1) :
    r ^ 2 * ((a + b) * (c + d)) =
      ((r * z) * a) * ((r * w) * c) + ((r * w) * b) * ((r * z) * d) +
        (w * w) * (((r * z) * a) * ((r * z) * d)) + (z * z) * (((r * w) * b) * ((r * w) * c)) := by
  linear_combination (-(r ^ 2) * (a * c + b * d + (a * d + b * c) * (1 + z * w))) * hzw

/-- The pointwise decomposition of the weighted tangential pairing into the non-oscillating and the oscillating
parts. -/
theorem decomp_identity (r : ℝ) (Ei Eo Ti To : Vector) :
    (r : ℂ) ^ 2 * pair (Ei + Eo) (Ti + To) =
      pair ((RegularTEIncoming.phase true r * (r : ℂ)) • Ei) ((RegularTEIncoming.phase true r * (r : ℂ)) • Ti) +
      pair (MaxwellFarField.factor 1 r • Eo) (MaxwellFarField.factor 1 r • To) +
      Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) *
        pair ((RegularTEIncoming.phase true r * (r : ℂ)) • Ei) (MaxwellFarField.factor 1 r • To) +
      Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) *
        pair (MaxwellFarField.factor 1 r • Eo) ((RegularTEIncoming.phase true r * (r : ℂ)) • Ti) := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = Complex.exp (Complex.I * (r : ℂ)) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w = Complex.exp (-Complex.I * (r : ℂ)) := ⟨_, rfl⟩
  have hzw : z * w = 1 := by
    rw [hz, hw, ← Complex.exp_add]
    have : Complex.I * (r : ℂ) + -Complex.I * (r : ℂ) = 0 := by ring
    rw [this, Complex.exp_zero]
  have hP : RegularTEIncoming.phase true r * (r : ℂ) = (r : ℂ) * z := by
    simp only [RegularTEIncoming.phase, if_true, hz]
    ring
  have hF : MaxwellFarField.factor 1 r = (r : ℂ) * w := by
    rw [factor_one]
    simp only [RegularTEIncoming.phase, Bool.false_eq_true, if_false, hw]
    ring_nf
  have he1 : Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) = w * w := by
    rw [hw, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have he2 : Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) = z * z := by
    rw [hz, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hcz : (starRingEnd ℂ) z = w := by
    rw [hz, hw, ← Complex.exp_conj]
    congr 1
    simp [map_mul, Complex.conj_I, Complex.conj_ofReal]
  have hcw : (starRingEnd ℂ) w = z := by
    rw [hz, hw, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
  rw [hP, hF, he1, he2]
  unfold pair dot conjugate
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, hcz, hcw, Complex.conj_ofReal]
  linear_combination key_identity r z w (Ei 0) (Eo 0) ((starRingEnd ℂ) (Ti 0)) ((starRingEnd ℂ) (To 0)) hzw +
    key_identity r z w (Ei 1) (Eo 1) ((starRingEnd ℂ) (Ti 1)) ((starRingEnd ℂ) (To 1)) hzw +
    key_identity r z w (Ei 2) (Eo 2) ((starRingEnd ℂ) (Ti 2)) ((starRingEnd ℂ) (To 2)) hzw

/-! ### The four scaled families -/

/-- Scaled electric part of the incoming Hankel part of the incident field. -/
def Ui (A : Idx →₀ ℂ) (r : ℝ) (n : Sphere) : Vector :=
  (RegularTEIncoming.phase true r * (r : ℂ)) • partE A true (r • (n : Space))

/-- Scaled tangential magnetic trace of the incoming Hankel part. -/
def Ti (A : Idx →₀ ℂ) (r : ℝ) (n : Sphere) : Vector :=
  (RegularTEIncoming.phase true r * (r : ℂ)) • crossProduct (position (n : Space)) (partH A true (r • (n : Space)))

/-- Scaled electric outgoing part (outgoing Hankel part of the incident field plus the scattered field). -/
def Uo (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ) (n : Sphere) : Vector :=
  MaxwellFarField.factor 1 r • (partE A false (r • (n : Space)) + ExteriorContinuity.electric 1 ρ (r • (n : Space)))

/-- Scaled tangential magnetic trace of the outgoing part. -/
def To (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ) (n : Sphere) : Vector :=
  MaxwellFarField.factor 1 r •
    crossProduct (position (n : Space)) (partH A false (r • (n : Space)) + MagneticResponse.magnetic 1 ρ (r • (n : Space)))

/-- The far amplitude of the scattered field. -/
def Fsc (ρ : Fin 3 → Space → ℂ) (n : Sphere) : Vector := MaxwellFarField.electricAmplitude 1 ρ (n : Space)

theorem good_Ui (A : Idx →₀ ℂ) : Good (Ui A) (aE A true) := good_partE A true

theorem good_Ti (A : Idx →₀ ℂ) : Good (Ti A) (aE A true) :=
  (good_partH A true).congr_lim (aT_true A)

theorem good_Uo (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0) :
    Good (Uo A ρ) (fun n => aE A false n + Fsc ρ n) := by
  refine ((good_partE A false).add (good_Usc R hR ρ hρ hc)).congr (Eventually.of_forall (fun r n => ?_))
  unfold Uo Usc
  rw [smul_add, factor_one]

theorem good_To (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0) :
    Good (To A ρ) (fun n => -aE A false n + -Fsc ρ n) := by
  have h := ((good_partH A false).add (good_Tsc R hR ρ hρ hc)).congr_lim (U1 := fun n => -aE A false n + -Fsc ρ n)
    (by
      funext n
      simp only [aT_false, Fsc])
  refine h.congr (Eventually.of_forall (fun r n => ?_))
  unfold To Tsc
  rw [map_add, smul_add, map_smul, factor_one]

/-! ### Exact decomposition of the flux and its limits -/

theorem pair_self (a : Vector) : pair a a = (energy a : ℂ) := dot_conjugate a

theorem pair_neg (a : Vector) : pair a (-a) = -(energy a : ℂ) := by
  have h := dot_conjugate a
  unfold pair
  have hc : conjugate (-a) = -conjugate a := by
    ext j
    simp [conjugate]
  rw [hc]
  unfold dot at h ⊢
  simp only [Pi.neg_apply]
  linear_combination -h

/-- The four sphere pairings. -/
def Iii (A : Idx →₀ ℂ) (r : ℝ) : ℂ := ∫ n, pair (Ui A r n) (Ti A r n) ∂OQ14.AngularPower.angularMeasure
def Ioo (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ) : ℂ :=
  ∫ n, pair (Uo A ρ r n) (To A ρ r n) ∂OQ14.AngularPower.angularMeasure
def Iio (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ) : ℂ :=
  ∫ n, pair (Ui A r n) (To A ρ r n) ∂OQ14.AngularPower.angularMeasure
def Ioi (A : Idx →₀ ℂ) (ρ : Fin 3 → Space → ℂ) (r : ℝ) : ℂ :=
  ∫ n, pair (Uo A ρ r n) (Ti A r n) ∂OQ14.AngularPower.angularMeasure

/-- Exact decomposition of the sphere flux of the complete field into sphere pairings. -/
theorem flux_decomposition (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0) (E H : Field)
    (hEx : ∀ x, R < ‖x‖ → E x = RestrictedTEIncoming.incomingElectric A x +
      RestrictedTEIncoming.outgoingElectric A x + ExteriorContinuity.electric 1 ρ x)
    (hHx : ∀ x, R < ‖x‖ → H x = RestrictedTEIncoming.incomingMagnetic A x +
      RestrictedTEIncoming.outgoingMagnetic A x + MagneticResponse.magnetic 1 ρ x) :
    ∀ᶠ r : ℝ in atTop, OQ14.RadialFlux.flux E H r =
      -(1/2 : ℝ) * (Iii A r + Ioo A ρ r +
        Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * Iio A ρ r +
        Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * Ioi A ρ r).re := by
  filter_upwards [eventually_gt_atTop (max R 0), pairing_integrable (good_Ui A) (good_Ti A),
    pairing_integrable (good_Uo A R hR ρ hρ hc) (good_To A R hR ρ hρ hc),
    pairing_integrable (good_Ui A) (good_To A R hR ρ hρ hc),
    pairing_integrable (good_Uo A R hR ρ hρ hc) (good_Ti A)] with r hr h1 h2 h3 h4
  have hrR : R < r := lt_of_le_of_lt (le_max_left _ _) hr
  have hr0 : 0 < r := lt_of_le_of_lt (le_max_right _ _) hr
  -- the pointwise integrand
  have hpt : ∀ n : Sphere, r ^ 2 * FarFieldPower.radialPower (n : Space) (E (r • (n : Space))) (H (r • (n : Space))) =
      -(1/2 : ℝ) * (pair (Ui A r n) (Ti A r n) + pair (Uo A ρ r n) (To A ρ r n) +
        Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Ui A r n) (To A ρ r n) +
        Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Uo A ρ r n) (Ti A r n)).re := by
    intro n
    have hn : ‖(n : Space)‖ = 1 := OQ14.AngularPower.sphere_norm n
    have hnr : R < ‖r • (n : Space)‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr0, hn, mul_one]
      exact hrR
    rw [hEx _ hnr, hHx _ hnr, SphereTangentialPower.radial_power _ hn]
    have hid := decomp_identity r (partE A true (r • (n : Space)))
      (partE A false (r • (n : Space)) + ExteriorContinuity.electric 1 ρ (r • (n : Space)))
      (crossProduct (position (n : Space)) (partH A true (r • (n : Space))))
      (crossProduct (position (n : Space)) (partH A false (r • (n : Space)) + MagneticResponse.magnetic 1 ρ (r • (n : Space))))
    have hE' : RestrictedTEIncoming.incomingElectric A (r • (n : Space)) +
        RestrictedTEIncoming.outgoingElectric A (r • (n : Space)) + ExteriorContinuity.electric 1 ρ (r • (n : Space)) =
        partE A true (r • (n : Space)) +
          (partE A false (r • (n : Space)) + ExteriorContinuity.electric 1 ρ (r • (n : Space))) := by
      rw [partE_true, partE_false, add_assoc]
    have hH' : crossProduct (position (n : Space)) (RestrictedTEIncoming.incomingMagnetic A (r • (n : Space)) +
        RestrictedTEIncoming.outgoingMagnetic A (r • (n : Space)) + MagneticResponse.magnetic 1 ρ (r • (n : Space))) =
        crossProduct (position (n : Space)) (partH A true (r • (n : Space))) +
          crossProduct (position (n : Space)) (partH A false (r • (n : Space)) + MagneticResponse.magnetic 1 ρ (r • (n : Space))) := by
      rw [partH_true, partH_false, add_assoc, map_add]
    rw [hE', hH']
    have hre := congrArg Complex.re hid
    have hlhs : ((r : ℂ) ^ 2 * pair (partE A true (r • (n : Space)) + (partE A false (r • (n : Space)) +
        ExteriorContinuity.electric 1 ρ (r • (n : Space))))
        (crossProduct (position (n : Space)) (partH A true (r • (n : Space))) +
          crossProduct (position (n : Space)) (partH A false (r • (n : Space)) +
            MagneticResponse.magnetic 1 ρ (r • (n : Space))))).re =
        r ^ 2 * (dot (partE A true (r • (n : Space)) + (partE A false (r • (n : Space)) +
        ExteriorContinuity.electric 1 ρ (r • (n : Space))))
        (conjugate (crossProduct (position (n : Space)) (partH A true (r • (n : Space))) +
          crossProduct (position (n : Space)) (partH A false (r • (n : Space)) +
            MagneticResponse.magnetic 1 ρ (r • (n : Space)))))).re := by
      have : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
      rfl
    rw [hlhs] at hre
    unfold Ui Ti Uo To
    simp only [] at hre ⊢
    linarith [hre]
  unfold Iii Ioo Iio Ioi
  unfold OQ14.RadialFlux.flux
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  congr 1
  have hint : Integrable (fun n => pair (Ui A r n) (Ti A r n) + pair (Uo A ρ r n) (To A ρ r n) +
      Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Ui A r n) (To A ρ r n) +
      Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Uo A ρ r n) (Ti A r n))
      OQ14.AngularPower.angularMeasure :=
    ((h1.add h2).add (h3.const_mul _)).add (h4.const_mul _)
  have hre := integral_re hint
  have hsum : (∫ n, (pair (Ui A r n) (Ti A r n) + pair (Uo A ρ r n) (To A ρ r n) +
      Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Ui A r n) (To A ρ r n) +
      Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Uo A ρ r n) (Ti A r n))
      ∂OQ14.AngularPower.angularMeasure) =
      (∫ n, pair (Ui A r n) (Ti A r n) ∂OQ14.AngularPower.angularMeasure) +
        (∫ n, pair (Uo A ρ r n) (To A ρ r n) ∂OQ14.AngularPower.angularMeasure) +
        Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) *
          (∫ n, pair (Ui A r n) (To A ρ r n) ∂OQ14.AngularPower.angularMeasure) +
        Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) *
          (∫ n, pair (Uo A ρ r n) (Ti A r n) ∂OQ14.AngularPower.angularMeasure) := by
    have hI3 : Integrable (fun n => pair (Ui A r n) (Ti A r n) + pair (Uo A ρ r n) (To A ρ r n))
        OQ14.AngularPower.angularMeasure := h1.add h2
    have hI2 : Integrable (fun n => pair (Ui A r n) (Ti A r n) + pair (Uo A ρ r n) (To A ρ r n) +
        Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * pair (Ui A r n) (To A ρ r n))
        OQ14.AngularPower.angularMeasure := hI3.add (h3.const_mul _)
    have e1 := integral_add hI2 (h4.const_mul (Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I)))
    have e2 := integral_add hI3 (h3.const_mul (Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I)))
    have e3 := integral_add h1 h2
    rw [e1, e2, e3, integral_const_mul, integral_const_mul]
  rw [← hsum]
  exact hre

/-- The far expansion of the sphere flux of the complete field with its limits. -/
theorem far_flux_expansion (A : Idx →₀ ℂ) (R : ℝ) (hR : 0 ≤ R) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j)) (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0) (E H : Field)
    (hEx : ∀ x, R < ‖x‖ → E x = RestrictedTEIncoming.incomingElectric A x +
      RestrictedTEIncoming.outgoingElectric A x + ExteriorContinuity.electric 1 ρ x)
    (hHx : ∀ x, R < ‖x‖ → H x = RestrictedTEIncoming.incomingMagnetic A x +
      RestrictedTEIncoming.outgoingMagnetic A x + MagneticResponse.magnetic 1 ρ x) :
    ∃ (R1 : ℝ) (g : ℝ → ℝ) (c : ℝ → ℂ) (G : ℝ) (C : ℂ), R ≤ R1 ∧
      (∀ r, R1 < r → OQ14.RadialFlux.flux E H r =
        g r + (Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * c r).re) ∧
      Tendsto g atTop (𝓝 G) ∧ Tendsto c atTop (𝓝 C) ∧
      G = (1/2 : ℝ) * ((∫ n, energy (aE A false n + Fsc ρ n) ∂OQ14.AngularPower.angularMeasure) -
        ∫ n, energy (aE A true n) ∂OQ14.AngularPower.angularMeasure) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (flux_decomposition A R hR ρ hρ hc E H hEx hHx)
  have hii := pairing_limit (good_Ui A) (good_Ti A)
  have hoo := pairing_limit (good_Uo A R hR ρ hρ hc) (good_To A R hR ρ hρ hc)
  have hio := pairing_limit (good_Ui A) (good_To A R hR ρ hρ hc)
  have hoi := pairing_limit (good_Uo A R hR ρ hρ hc) (good_Ti A)
  have hg : Tendsto (fun r => -(1/2 : ℝ) * (Iii A r + Ioo A ρ r).re) atTop
      (𝓝 (-(1/2 : ℝ) * ((∫ n, pair (aE A true n) (aE A true n) ∂OQ14.AngularPower.angularMeasure) +
        (∫ n, pair (aE A false n + Fsc ρ n) (-aE A false n + -Fsc ρ n) ∂OQ14.AngularPower.angularMeasure)).re)) :=
    ((Complex.continuous_re.tendsto _).comp (hii.add hoo)).const_mul _
  have hcl : Tendsto (fun r => (((-(1/2 : ℝ) : ℝ) : ℂ)) * (Iio A ρ r + (starRingEnd ℂ) (Ioi A ρ r))) atTop
      (𝓝 ((((-(1/2 : ℝ) : ℝ) : ℂ)) *
        ((∫ n, pair (aE A true n) (-aE A false n + -Fsc ρ n) ∂OQ14.AngularPower.angularMeasure) +
          (starRingEnd ℂ) (∫ n, pair (aE A false n + Fsc ρ n) (aE A true n) ∂OQ14.AngularPower.angularMeasure)))) :=
    (hio.add ((Complex.continuous_conj.tendsto _).comp hoi)).const_mul _
  have hIii : (∫ n, pair (aE A true n) (aE A true n) ∂OQ14.AngularPower.angularMeasure) =
      ((∫ n, energy (aE A true n) ∂OQ14.AngularPower.angularMeasure : ℝ) : ℂ) := by
    simp_rw [pair_self]
    exact integral_complex_ofReal
  have hIoo : (∫ n, pair (aE A false n + Fsc ρ n) (-aE A false n + -Fsc ρ n) ∂OQ14.AngularPower.angularMeasure) =
      -((∫ n, energy (aE A false n + Fsc ρ n) ∂OQ14.AngularPower.angularMeasure : ℝ) : ℂ) := by
    have : ∀ n : Sphere, pair (aE A false n + Fsc ρ n) (-aE A false n + -Fsc ρ n) =
        -((energy (aE A false n + Fsc ρ n) : ℝ) : ℂ) := by
      intro n
      rw [← neg_add, pair_neg]
    simp_rw [this]
    rw [integral_neg, integral_complex_ofReal]
  refine ⟨max N R, fun r => -(1/2 : ℝ) * (Iii A r + Ioo A ρ r).re,
    fun r => (((-(1/2 : ℝ) : ℝ) : ℂ)) * (Iio A ρ r + (starRingEnd ℂ) (Ioi A ρ r)),
    (1/2 : ℝ) * ((∫ n, energy (aE A false n + Fsc ρ n) ∂OQ14.AngularPower.angularMeasure) -
      ∫ n, energy (aE A true n) ∂OQ14.AngularPower.angularMeasure), _, le_max_right _ _, ?_, ?_, hcl, rfl⟩
  · intro r hr
    have hr' : N ≤ r := (le_max_left _ _).trans hr.le
    rw [hN r hr']
    have hconj : (starRingEnd ℂ) (Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I)) =
        Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) := by
      rw [← Complex.exp_conj]
      congr 1
      have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
      simp [map_mul, Complex.conj_I, Complex.conj_ofReal, h2]
    have hre : (Complex.exp (2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * Ioi A ρ r).re =
        (Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * (starRingEnd ℂ) (Ioi A ρ r)).re := by
      rw [← Complex.conj_re, map_mul, hconj]
    have e1 : Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) *
        ((((-(1/2 : ℝ) : ℝ) : ℂ)) * (Iio A ρ r + (starRingEnd ℂ) (Ioi A ρ r))) =
        (((-(1/2 : ℝ) : ℝ) : ℂ)) * (Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * Iio A ρ r +
          Complex.exp (-2 * ((1 : ℝ) : ℂ) * (r : ℂ) * Complex.I) * (starRingEnd ℂ) (Ioi A ρ r)) := by
      ring
    rw [e1, Complex.re_ofReal_mul, Complex.add_re]
    simp only [Complex.add_re]
    rw [hre]
    ring
  · have hG : -(1/2 : ℝ) * ((∫ n, pair (aE A true n) (aE A true n) ∂OQ14.AngularPower.angularMeasure) +
        (∫ n, pair (aE A false n + Fsc ρ n) (-aE A false n + -Fsc ρ n) ∂OQ14.AngularPower.angularMeasure)).re =
        (1/2 : ℝ) * ((∫ n, energy (aE A false n + Fsc ρ n) ∂OQ14.AngularPower.angularMeasure) -
          ∫ n, energy (aE A true n) ∂OQ14.AngularPower.angularMeasure) := by
      rw [hIii, hIoo, Complex.add_re, Complex.ofReal_re, Complex.neg_re, Complex.ofReal_re]
      ring
    rw [← hG]
    exact hg

end OQ14.ChannelFarFluxExpansion
#print axioms OQ14.ChannelFarFluxExpansion.factor_one
#print axioms OQ14.ChannelFarFluxExpansion.key_identity
#print axioms OQ14.ChannelFarFluxExpansion.decomp_identity
#print axioms OQ14.ChannelFarFluxExpansion.good_Ui
#print axioms OQ14.ChannelFarFluxExpansion.good_Ti
#print axioms OQ14.ChannelFarFluxExpansion.good_Uo
#print axioms OQ14.ChannelFarFluxExpansion.good_To
#print axioms OQ14.ChannelFarFluxExpansion.pair_self
#print axioms OQ14.ChannelFarFluxExpansion.pair_neg
#print axioms OQ14.ChannelFarFluxExpansion.flux_decomposition
#print axioms OQ14.ChannelFarFluxExpansion.far_flux_expansion
