import FrequencyScalingMaxwell
import RestrictedTEIncoming
import RestrictedTEMaterial
import MaxwellFarField

/-! # Frequency scaling of the inward power, the incident Maxwell property and the far amplitude

Under the amplitude-normalized dilation `scaleField k F x = k • F (k x)` the
inward power flux of the finite TE incident pair through the sphere of radius
`r` equals the frequency-`1` flux through the sphere of radius `k r`, hence it
has the same limit `physicalPower A` as `r → ∞`.  The vacuum weak Maxwell
property of the finite TE incident fields transfers to frequency `k`, and the
far-field amplitude of a compactly supported scattered field is unchanged by
the dilation.  All statements are pointwise algebra on top of the frozen
theorems `testMaxwell_vacuum_scale`, `actual_power_limit` and
`electric_far_vector_limit`.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.FrequencyScalingPower

open Filter MeasureTheory OQ14.FrequencyScalingMaxwell OQ14.MaterialMaxwell
open scoped Topology ComplexConjugate

/-- The index set of the finite TE data. -/
abbrev Index := SymmetricHarmonicJets.Index

/-- The unit sphere carrying the surface measure. -/
abbrev Sphere := SphereReactionKernel.Sphere

/-- Complex conjugation of a vector commutes with multiplication by a real
scalar. -/
theorem conjugate_real_smul (k : ℝ) (v : Maxwell.Vector) :
    Maxwell.conjugate ((k : ℂ) • v) = (k : ℂ) • Maxwell.conjugate v := by
  funext j
  simp [Maxwell.conjugate, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]

/-- The radial power density of the pair `(k E, k H)` is `k ^ 2` times that of
`(E, H)`, for a real amplitude factor `k`. -/
theorem radialPower_smul (k : ℝ) (n : Maxwell.Space) (e h : Maxwell.Vector) :
    FarFieldPower.radialPower n ((k : ℂ) • e) ((k : ℂ) • h) =
      k ^ 2 * FarFieldPower.radialPower n e h := by
  have he : ∀ d : Maxwell.Vector,
      Maxwell.dot d (crossProduct ((k : ℂ) • e) (Maxwell.conjugate ((k : ℂ) • h))) =
        ((k ^ 2 : ℝ) : ℂ) * Maxwell.dot d (crossProduct e (Maxwell.conjugate h)) := by
    intro d
    rw [conjugate_real_smul, LinearMap.map_smul₂, map_smul, smul_smul]
    simp only [Maxwell.dot, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  unfold FarFieldPower.radialPower
  rw [he, Complex.re_ofReal_mul]
  ring

/-- The inward flux through the sphere of radius `r` of the pair obtained from
the finite TE incident fields by the amplitude-normalized dilation of
frequency `k`. -/
def scaledInwardPower (k : ℝ) (A : Index →₀ ℂ) (r : ℝ) : ℝ :=
  ∫ n : Sphere, -r ^ 2 * FarFieldPower.radialPower (n : Maxwell.Space)
    (scaleField k (RestrictedTEIncoming.incomingElectric A) (r • (n : Maxwell.Space)))
    (scaleField k (RestrictedTEIncoming.incomingMagnetic A) (r • (n : Maxwell.Space)))
    ∂SphereReactionKernel.surface

/-- The frequency-`k` inward flux through radius `r` is the frequency-`1`
inward flux through radius `k r`. -/
theorem scaledInwardPower_eq (k : ℝ) (A : Index →₀ ℂ) (r : ℝ) :
    scaledInwardPower k A r =
      ∫ n : Sphere, -(k * r) ^ 2 * FarFieldPower.radialPower (n : Maxwell.Space)
        (RestrictedTEIncoming.incomingElectric A ((k * r) • (n : Maxwell.Space)))
        (RestrictedTEIncoming.incomingMagnetic A ((k * r) • (n : Maxwell.Space)))
        ∂SphereReactionKernel.surface := by
  unfold scaledInwardPower
  congr 1
  funext n
  have e : k • r • (n : Maxwell.Space) = (k * r) • (n : Maxwell.Space) := smul_smul k r _
  show -r ^ 2 * FarFieldPower.radialPower (n : Maxwell.Space)
      ((k : ℂ) • RestrictedTEIncoming.incomingElectric A (k • r • (n : Maxwell.Space)))
      ((k : ℂ) • RestrictedTEIncoming.incomingMagnetic A (k • r • (n : Maxwell.Space))) =
    -(k * r) ^ 2 * FarFieldPower.radialPower (n : Maxwell.Space)
      (RestrictedTEIncoming.incomingElectric A ((k * r) • (n : Maxwell.Space)))
      (RestrictedTEIncoming.incomingMagnetic A ((k * r) • (n : Maxwell.Space)))
  rw [e, radialPower_smul]
  ring

/-- The inward power of the frequency-`k` dilated incident pair tends to the
same physical power `physicalPower A` as the frequency-`1` pair. -/
theorem scaledInwardPower_limit (k : ℝ) (hk : 0 < k) (A : Index →₀ ℂ) :
    Tendsto (scaledInwardPower k A) atTop (𝓝 (RestrictedTEIncoming.physicalPower A)) := by
  have h := (RestrictedTEIncoming.actual_power_limit A).comp (tendsto_id.const_mul_atTop hk)
  exact h.congr (fun r => (scaledInwardPower_eq k A r).symm)

/-- The finite TE incident pair dilated to frequency `k` is a weak vacuum
Maxwell solution at frequency `k`. -/
theorem incident_testMaxwell_scale (k : ℝ) (hk : 0 < k) (A : Index →₀ ℂ) :
    TestMaxwell k (fun _ => 1) (scaleField k (RestrictedTEPlaneLocal.electric A))
      (scaleField k (RestrictedTEPlaneLocal.magnetic A)) :=
  testMaxwell_vacuum_scale k hk _ _ (RestrictedTEMaterial.testMaxwell A)

/-- The far-field normalization factor at frequency `k` times `k` is the
frequency-`1` factor at radius `k r`. -/
theorem factor_scale (k r : ℝ) :
    MaxwellFarField.factor k r * (k : ℂ) = MaxwellFarField.factor 1 (k * r) := by
  unfold MaxwellFarField.factor
  have h : -Complex.I * ((1 : ℝ) : ℂ) * ((k * r : ℝ) : ℂ) = -Complex.I * (k : ℂ) * (r : ℂ) := by
    push_cast
    ring
  rw [h]
  push_cast
  ring

/-- If a frequency-`1` field has far amplitude `A` along the ray `d`, then its
amplitude-normalized dilation to frequency `k` has the same far amplitude `A`
with the frequency-`k` normalization. -/
theorem far_limit_scale (k : ℝ) (hk : 0 < k) (F : Maxwell.Field) (d : Maxwell.Space)
    (A : Maxwell.Vector)
    (hF : Tendsto (fun r : ℝ => MaxwellFarField.factor 1 r • F (r • d)) atTop (𝓝 A)) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor k r • scaleField k F (r • d)) atTop
      (𝓝 A) := by
  have h := hF.comp (tendsto_id.const_mul_atTop hk)
  refine h.congr (fun r => ?_)
  show MaxwellFarField.factor 1 (k * r) • F ((k * r) • d) =
    MaxwellFarField.factor k r • ((k : ℂ) • F (k • r • d))
  simp only [smul_smul, factor_scale]

/-- The far-field amplitude of the electric field radiated by a compactly
supported integrable source is unchanged by the amplitude-normalized
dilation to frequency `k`. -/
theorem scattered_far_scale (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Maxwell.Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ Metric.closedBall 0 R → ρ j y = 0)
    (n : Maxwell.Space) (hn : ‖n‖ = 1) :
    Tendsto (fun r : ℝ => MaxwellFarField.factor k r •
      scaleField k (ExteriorContinuity.electric 1 ρ) (r • n)) atTop
      (𝓝 (MaxwellFarField.electricAmplitude 1 ρ n)) :=
  far_limit_scale k hk _ n _ (MaxwellFarField.electric_far_vector_limit 1 R hR ρ hρ hc n hn)

end OQ14.FrequencyScalingPower

#print axioms OQ14.FrequencyScalingPower.conjugate_real_smul
#print axioms OQ14.FrequencyScalingPower.radialPower_smul
#print axioms OQ14.FrequencyScalingPower.scaledInwardPower_eq
#print axioms OQ14.FrequencyScalingPower.scaledInwardPower_limit
#print axioms OQ14.FrequencyScalingPower.incident_testMaxwell_scale
#print axioms OQ14.FrequencyScalingPower.factor_scale
#print axioms OQ14.FrequencyScalingPower.far_limit_scale
#print axioms OQ14.FrequencyScalingPower.scattered_far_scale
