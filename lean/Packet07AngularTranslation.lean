import Packet07AffineGeometry
import FullChannelMagnetic

/-! Translation of actual continuous angular Herglotz input by a unit-modulus phase. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07AngularTranslation
open Filter MeasureTheory Maxwell SphereHarmonicBasis
open scoped Topology
abbrev Sphere := SphereHarmonicBasis.Sphere
abbrev Vector := ComplexVectorSphere.Vector

def phase (k : ℝ) (a : Maxwell.Space) (n : Sphere) : ℂ := SphereReactionKernel.wave k a n

def translatedAmplitude (k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector)) : C(Sphere,Vector) where
  toFun n := phase k a n • A n
  continuous_toFun := by
    have hp : Continuous (phase k a) := by unfold phase SphereReactionKernel.wave; fun_prop
    exact hp.smul A.continuous

theorem phase_norm (k : ℝ) (a : Maxwell.Space) (n : Sphere) : ‖phase k a n‖ = 1 :=
  SphereReactionKernel.wave_norm k a n

/-- Translation changes only the angular phase, so the exact angular L² norm is unchanged. -/
theorem translated_norm (k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector)) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (translatedAmplitude k a A)‖ =
      ‖ContinuousMap.toLp 2 angularMeasure ℂ A‖ := by
  apply le_antisymm
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(translatedAmplitude k a A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      A.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n h1 h2
    rw [h1,h2]
    simp [translatedAmplitude, norm_smul, phase_norm]
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(translatedAmplitude k a A).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
      A.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n h1 h2
    rw [h1,h2]
    simp [translatedAmplitude, norm_smul, phase_norm]

/-- The phase-modulated density generates exactly the translated electric Herglotz field. -/
theorem translated_electric (k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector))
    (x : Maxwell.Space) (i : Fin 3) :
    AngularHerglotz.electric k (fun n j => translatedAmplitude k a A n j) x i =
      AngularHerglotz.electric k (fun n j => A n j) (x-a) i := by
  unfold AngularHerglotz.electric SphereWaveCalculus.moment
  apply integral_congr_ae
  filter_upwards with n
  change (SphereReactionKernel.wave k a n * A n i) * SphereReactionKernel.wave (-k) x n =
    A n i * SphereReactionKernel.wave (-k) (x-a) n
  have hw : SphereReactionKernel.wave k a n * SphereReactionKernel.wave (-k) x n =
      SphereReactionKernel.wave (-k) (x-a) n := by
    unfold SphereReactionKernel.wave
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_right, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_sub]
    ring
  rw [← hw]
  ring

/-- The same phase modulation gives the exact translated magnetic field. -/
theorem translated_magnetic (k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector))
    (x : Maxwell.Space) (i : Fin 3) :
    AngularHerglotz.magnetic k (fun n j => translatedAmplitude k a A n j) x i =
      AngularHerglotz.magnetic k (fun n j => A n j) (x-a) i := by
  unfold AngularHerglotz.magnetic AngularHerglotz.electric SphereWaveCalculus.moment
  apply integral_congr_ae
  filter_upwards with n
  have hm : AngularHerglotz.magneticAmplitude (fun n j => translatedAmplitude k a A n j) n i =
      SphereReactionKernel.wave k a n * AngularHerglotz.magneticAmplitude (fun n j => A n j) n i := by
    fin_cases i <;> simp [AngularHerglotz.magneticAmplitude, translatedAmplitude, phase, cross_apply] <;> ring
  rw [hm]
  have hw : SphereReactionKernel.wave k a n * SphereReactionKernel.wave (-k) x n =
      SphereReactionKernel.wave (-k) (x-a) n := by
    unfold SphereReactionKernel.wave
    rw [← Complex.exp_add]
    congr 1
    simp only [inner_sub_right, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_sub]
    ring
  rw [← hw]
  ring

/-- Translation preserves the physical transverse-polarization condition. -/
theorem translated_tangent (k : ℝ) (a : Maxwell.Space) (A : C(Sphere,Vector))
    (hA : ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (A n) = 0) :
    ∀ n, @inner ℂ Vector _ (TransversePlaneFields.normal n) (translatedAmplitude k a A n) = 0 := by
  intro n
  change inner _ (phase k a n • A n) = 0
  rw [inner_smul_right, hA n, mul_zero]

/-- Translation preserves the exact standard angular incoming-power normalization
    of a finite harmonic illumination at its physical frequency. -/
theorem translated_unit_angular_power (k : ℝ) (hk : 0 < k) (a : Maxwell.Space)
    (c : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hpower : Filter.Tendsto (FiniteMixedScaledFlux.inwardPowerK k c) Filter.atTop (𝓝 1)) :
    (2 * Real.pi^2 / k^2) *
      ‖ContinuousMap.toLp 2 angularMeasure ℂ
        (translatedAmplitude k a (FiniteVectorAngular.amplitude c))‖^2 = 1 := by
  have hlim := FiniteMixedScaledFlux.inwardPowerK_limit_E k hk c
  have hE : FiniteMixedScaledFlux.E c / k^2 = 1 := tendsto_nhds_unique hlim hpower
  rw [translated_norm]
  have hh := FiniteVectorAngular.amplitude_energy c
  have henergy : FiniteMixedScaledFlux.energyIntegral c =
      ‖ContinuousMap.toLp 2 angularMeasure ℂ (FiniteVectorAngular.amplitude c)‖^2 := by
    exact hh
  unfold FiniteMixedScaledFlux.E at hE
  rw [henergy] at hE
  convert hE using 1; ring

end OQ14.Packet07AngularTranslation
#print axioms OQ14.Packet07AngularTranslation.phase_norm
#print axioms OQ14.Packet07AngularTranslation.translated_norm
#print axioms OQ14.Packet07AngularTranslation.translated_electric
#print axioms OQ14.Packet07AngularTranslation.translated_magnetic

#print axioms OQ14.Packet07AngularTranslation.translated_tangent
#print axioms OQ14.Packet07AngularTranslation.translated_unit_angular_power
