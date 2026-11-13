import Packet07PatchDilation

/-! Power-normalized affine transfer of the actual compact dielectric Maxwell system. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07AffineMaxwell
open MeasureTheory Maxwell MaterialMaxwell FrequencyScalingMaxwell
abbrev Space := Maxwell.Space

/-- Actual susceptibility obtained by first dilating and then translating a device. -/
def affineCoeff (s : ℝ) (a : Space) (c : StaticCoefficient.Coefficient) : StaticCoefficient.Coefficient where
  value ξ := c.value (s • (ξ - VectorFourier.coordinateMap a))
  bound := c.bound
  measurable := c.measurable.comp ((measurable_const_smul s).comp (measurable_id.sub measurable_const))
  nonnegative _ := c.nonnegative _
  bounded _ := c.bounded _

/-- Power-normalized affine field: spatial dilation followed by translation. -/
def affineField (s : ℝ) (a : Space) (F : Maxwell.Field) : Maxwell.Field :=
  fun x => scaleField s F (x-a)

theorem dielectric_affine (s : ℝ) (a : Space) (c : StaticCoefficient.Coefficient) (x : Space) :
    dielectric (affineCoeff s a c) x = dielectric (scaleCoeff s c) (x-a) := by
  rfl

/-- Spatial dilation of a weak Maxwell field at an arbitrary initial frequency. -/
theorem testMaxwell_scale_any (s k : ℝ) (hs : 0 < s) (ε : Space → ℝ) (E H : Maxwell.Field)
    (hM : TestMaxwell k ε E H) :
    TestMaxwell (s*k) (fun x => ε (s • x)) (PuncturedMaxwellScaling.fieldAtFrequency s E)
      (PuncturedMaxwellScaling.fieldAtFrequency s H) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  intro i f
  obtain ⟨h1,h2⟩ := hM i (dilateTest s hs f)
  constructor
  · rw [curlPair_scale s hs E i f, h1, fieldPair_scale s hs H i f]
    push_cast
    field_simp
    ring
  · have h3 := coeff_integral_scale s hs ε E i f
    change MagneticResponse.curlPair (fieldPair (PuncturedMaxwellScaling.fieldAtFrequency s H)) i f =
      -(Complex.I * ((s*k : ℝ) : ℂ)) * (∫ x, ((ε (s • x) : ℝ) : ℂ) * E (s • x) i * f.val x)
    rw [h3, curlPair_scale s hs H i f, h2]
    push_cast
    field_simp
    ring

/-- Affine transformation takes the actual frequency-k dielectric Maxwell pair
    to frequency sk with the literal transformed positive dielectric. -/
theorem affine_maxwell (s k : ℝ) (hs : 0 < s) (c : StaticCoefficient.Coefficient)
    (E H : Maxwell.Field) (hM : TestMaxwell k (dielectric c) E H) (a : Space) :
    TestMaxwell (s*k) (dielectric (affineCoeff s a c)) (affineField s a E) (affineField s a H) := by
  have hm := testMaxwell_scale_any s k hs (dielectric c) E H hM
  have hsM := FrequencyScalingMaxwell.testMaxwell_smul (s*k) (fun x => dielectric c (s • x))
    (PuncturedMaxwellScaling.fieldAtFrequency s E) (PuncturedMaxwellScaling.fieldAtFrequency s H) (s : ℂ) hm
  have ht := Packet07MaxwellTranslation.testMaxwell_translate (s*k)
    (fun x => dielectric c (s • x)) _ _ hsM a
  exact ht

/-- Power-normalized affine device transfer preserves each positive-volume peak. -/
theorem affine_peak (s : ℝ) (hs : 0 < s) (a c : Space) (r M : ℝ) (E : Maxwell.Field) (i : Fin 3)
    (hpeak : 0 < (volume.restrict (Metric.ball c r)) {x | M/s < ‖E x i‖}) :
    0 < (volume.restrict (Metric.ball (s⁻¹ • c + a) (r/s)))
      {x | M < ‖affineField s a E x i‖} := by
  have h := Packet07ScaleMeasure.positive_peak_dilation s hs c r M E i hpeak
  exact Packet07ScaleMeasure.positive_peak_translate a (s⁻¹ • c) (r/s) M (scaleField s E) i h

end OQ14.Packet07AffineMaxwell
#print axioms OQ14.Packet07AffineMaxwell.dielectric_affine
#print axioms OQ14.Packet07AffineMaxwell.affine_maxwell

#print axioms OQ14.Packet07AffineMaxwell.testMaxwell_scale_any

#print axioms OQ14.Packet07AffineMaxwell.affine_peak
