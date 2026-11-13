import Packet06GlobalMaxwell
import Packet07MaxwellTranslation

/-! Complex-frequency weak Maxwell equations under affine dilations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet06ComplexAffine
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse KernelConvolution FrequencyScalingMaxwell

def TestMaxwellC (z : ℂ) (ε : Space → ℝ) (E H : Field) : Prop :=
  ∀ (i : Fin 3) (f : Test),
    curlPair (fieldPair E) i f = Complex.I*z * fieldPair H i f ∧
    curlPair (fieldPair H) i f = -(Complex.I*z) *
      ∫ x, (ε x : ℂ) * E x i * f.val x

theorem global_actual_test (c : StaticCoefficient.Coefficient) (z : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ Metric.closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u = 0) :
    TestMaxwellC z (MaterialMaxwell.dielectric c) (Packet06GlobalField.electric c z R u)
      (ComplexMagneticLocal.magnetic z (DynamicVolume.source c u)) := by
  intro i f
  simpa only [curlPair, fieldPair, dielectric, Complex.ofReal_add, Complex.ofReal_one] using
    Packet06GlobalMaxwell.global_first_order c z R hR u hc hu i f

theorem translate (z : ℂ) (ε : Space → ℝ) (E H : Field)
    (hM : TestMaxwellC z ε E H) (a : Space) :
    TestMaxwellC z (fun x => ε (x-a)) (fun x => E (x-a)) (fun x => H (x-a)) := by
  have hp (F : Field) (i : Fin 3) (f : Test) :
      fieldPair (fun x => F (x-a)) i f = fieldPair F i (KernelConvolution.translate a f) := by
    unfold fieldPair
    exact (translated_pairing (fun x => F x i) a f).symm
  have hc (F : Field) (i : Fin 3) (f : Test) :
      curlPair (fieldPair (fun x => F (x-a))) i f = curlPair (fieldPair F) i (KernelConvolution.translate a f) := by
    unfold curlPair
    rw [hp, hp, translate_partial, translate_partial]
  intro i f
  have h := hM i (KernelConvolution.translate a f)
  constructor
  · rw [hc, hp]
    exact h.1
  · rw [hc]
    have hi : (∫ x, ((ε (x-a) : ℝ) : ℂ) * E (x-a) i * f.val x) =
        ∫ x, ((ε x : ℝ) : ℂ) * E x i * (KernelConvolution.translate a f).val x := by
      exact (translated_pairing (fun x => ((ε x : ℝ) : ℂ) * E x i) a f).symm
    rw [hi]
    exact h.2

theorem dilate (z : ℂ) (s : ℝ) (hs : 0 < s) (ε : Space → ℝ) (E H : Field)
    (hM : TestMaxwellC z ε E H) :
    TestMaxwellC ((s : ℂ)*z) (fun x => ε (s • x))
      (PuncturedMaxwellScaling.fieldAtFrequency s E) (PuncturedMaxwellScaling.fieldAtFrequency s H) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  intro i f
  obtain ⟨h1,h2⟩ := hM i (dilateTest s hs f)
  constructor
  · rw [curlPair_scale s hs E i f, h1, fieldPair_scale s hs H i f]
    push_cast
    field_simp
    ring
  · have h3 := coeff_integral_scale s hs ε E i f
    change curlPair (fieldPair (PuncturedMaxwellScaling.fieldAtFrequency s H)) i f =
      -(Complex.I * ((s : ℂ)*z)) * (∫ x, ((ε (s • x) : ℝ) : ℂ) * E (s • x) i * f.val x)
    rw [h3, curlPair_scale s hs H i f, h2]
    push_cast
    field_simp
    ring

end OQ14.Packet06ComplexAffine
#print axioms OQ14.Packet06ComplexAffine.global_actual_test
#print axioms OQ14.Packet06ComplexAffine.translate
#print axioms OQ14.Packet06ComplexAffine.dilate
