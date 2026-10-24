import MaterialMaxwell
import ModalScaling
import PuncturedMaxwellScaling

/-! # Frequency scaling of the weak dielectric Maxwell system

Maxwell's equations are scale invariant. If `(E, H)` solves the weak
frequency-1 system with dielectric `ε`, then `x ↦ E (k x)`, `x ↦ H (k x)`
solve the weak frequency-`k` system with dielectric `x ↦ ε (k x)`, and so does
the pair multiplied by any complex constant. The statements are about the
frozen predicate `MaterialMaxwell.TestMaxwell`; the proof is the change of
variables `x ↦ k x` in the test pairings together with the chain rule for the
dilated compact smooth test.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.FrequencyScalingMaxwell

open MeasureTheory OQ14.Maxwell OQ14.DynamicSource OQ14.MagneticResponse
  OQ14.MaterialMaxwell
open OQ14.WeakCurl (next previous)
open scoped SchwartzMap

/-- Amplitude-and-frequency rescaling of a field: `x ↦ k • F (k x)`. -/
def scaleField (k : ℝ) (F : Field) : Field := fun x => (k : ℂ) • F (k • x)

theorem scaleField_apply (k : ℝ) (F : Field) (x : Space) (i : Fin 3) :
    scaleField k F x i = (k : ℂ) * F (k • x) i := rfl

/-- Frequency rescaling of a static coefficient: `value ξ ↦ value (k ξ)`. -/
def scaleCoeff (k : ℝ) (c : Coefficient) : Coefficient where
  value := fun ξ => c.value (k • ξ)
  bound := c.bound
  measurable := c.measurable.comp (measurable_const_smul k)
  nonnegative := fun ξ => c.nonnegative (k • ξ)
  bounded := fun ξ => c.bounded (k • ξ)

theorem scaleCoeff_value (k : ℝ) (c : Coefficient) (ξ : VectorFourier.Frequency) :
    (scaleCoeff k c).value ξ = c.value (k • ξ) := rfl

theorem coordinateMap_smul (k : ℝ) (x : Space) :
    VectorFourier.coordinateMap (k • x) = k • VectorFourier.coordinateMap x := rfl

theorem dielectric_scaleCoeff (k : ℝ) (c : Coefficient) (x : Space) :
    dielectric (scaleCoeff k c) x = dielectric c (k • x) := by
  unfold dielectric
  rw [scaleCoeff_value, coordinateMap_smul]

theorem dielectric_scaleCoeff_bounds (k : ℝ) (c : Coefficient) (x : Space) :
    1 ≤ dielectric (scaleCoeff k c) x ∧ dielectric (scaleCoeff k c) x ≤ 1 + c.bound := by
  rw [dielectric_scaleCoeff]
  exact dielectric_bounds c (k • x)

theorem dielectric_scaleCoeff_eq (k : ℝ) (c : Coefficient) :
    dielectric (scaleCoeff k c) = fun x => dielectric c (k • x) := by
  funext x
  exact dielectric_scaleCoeff k c x

/-- The Schwartz function `x ↦ f (k⁻¹ x)`. -/
def dilateSchwartz (k : ℝ) (hk : 0 < k) (f : 𝓢(Space, ℂ)) : 𝓢(Space, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearEquiv.smulOfNeZero ℝ Space k⁻¹ (inv_ne_zero hk.ne')).toContinuousLinearEquiv f

theorem dilateSchwartz_apply (k : ℝ) (hk : 0 < k) (f : 𝓢(Space, ℂ)) (x : Space) :
    dilateSchwartz k hk f x = f (k⁻¹ • x) := rfl

/-- The compactly supported test `x ↦ f (k⁻¹ x)`. -/
def dilateTest (k : ℝ) (hk : 0 < k) (f : Test) : Test :=
  ⟨dilateSchwartz k hk f.val, by
    have h := ModalScaling.dilated_test_compact k⁻¹ (inv_ne_zero hk.ne')
      (f.val : Space → ℂ) f.property
    exact h⟩

theorem dilateTest_apply (k : ℝ) (hk : 0 < k) (f : Test) (x : Space) :
    (dilateTest k hk f).val x = f.val (k⁻¹ • x) := rfl

theorem dilateTest_val (k : ℝ) (hk : 0 < k) (f : Test) :
    ((dilateTest k hk f).val : Space → ℂ) = fun y => f.val (k⁻¹ • y) := by
  funext y
  exact dilateTest_apply k hk f y

theorem testPartial_dilateTest (k : ℝ) (hk : 0 < k) (j : Fin 3) (f : Test) (x : Space) :
    (testPartial j (dilateTest k hk f)).val x =
      ((k⁻¹ : ℝ) : ℂ) * (testPartial j f).val (k⁻¹ • x) := by
  change GradientProjection.pderivative j (dilateTest k hk f).val x =
    ((k⁻¹ : ℝ) : ℂ) * GradientProjection.pderivative j f.val (k⁻¹ • x)
  rw [GradientProjection.pderivative_apply, GradientProjection.pderivative_apply,
    dilateTest_val]
  exact ModalScaling.dcoord_comp_smul k⁻¹ f.val x f.val.differentiableAt j

theorem fieldPair_scale (k : ℝ) (hk : 0 < k) (E : Field) (i : Fin 3) (f : Test) :
    fieldPair (PuncturedMaxwellScaling.fieldAtFrequency k E) i f =
      (((k ^ 3)⁻¹ : ℝ) : ℂ) * fieldPair E i (dilateTest k hk f) := by
  unfold fieldPair PuncturedMaxwellScaling.fieldAtFrequency
  have h : (fun x : Space => E (k • x) i * f.val x) =
      fun x : Space => (fun y : Space => E y i * f.val (k⁻¹ • y)) (k • x) := by
    funext x
    simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [h, Measure.integral_comp_smul (volume : Measure Space)
    (fun y : Space => E y i * f.val (k⁻¹ • y)) k]
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hk 3)), Complex.real_smul]
  rfl

theorem testPartial_pair_scale (k : ℝ) (hk : 0 < k) (E : Field) (i j : Fin 3) (f : Test) :
    fieldPair E i (testPartial j (dilateTest k hk f)) =
      ((k⁻¹ : ℝ) : ℂ) * fieldPair E i (dilateTest k hk (testPartial j f)) := by
  unfold fieldPair
  rw [← integral_const_mul]
  congr 1
  funext x
  rw [testPartial_dilateTest, dilateTest_apply]
  ring

theorem testPartial_pair_scale' (k : ℝ) (hk : 0 < k) (E : Field) (i j : Fin 3) (f : Test) :
    fieldPair E i (dilateTest k hk (testPartial j f)) =
      (k : ℂ) * fieldPair E i (testPartial j (dilateTest k hk f)) := by
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  rw [testPartial_pair_scale k hk E i j f]
  push_cast
  field_simp

theorem curlPair_scale (k : ℝ) (hk : 0 < k) (E : Field) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (PuncturedMaxwellScaling.fieldAtFrequency k E)) i f =
      (((k ^ 2)⁻¹ : ℝ) : ℂ) * curlPair (fieldPair E) i (dilateTest k hk f) := by
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  unfold curlPair
  rw [fieldPair_scale k hk E (next i) (testPartial (previous i) f),
    fieldPair_scale k hk E (previous i) (testPartial (next i) f),
    testPartial_pair_scale' k hk E (next i) (previous i) f,
    testPartial_pair_scale' k hk E (previous i) (next i) f]
  push_cast
  field_simp
  ring

theorem coeff_integral_scale (k : ℝ) (hk : 0 < k) (ε : Space → ℝ) (E : Field) (i : Fin 3)
    (f : Test) :
    (∫ x, ((ε (k • x) : ℝ) : ℂ) * E (k • x) i * f.val x) =
      (((k ^ 3)⁻¹ : ℝ) : ℂ) * ∫ x, ((ε x : ℝ) : ℂ) * E x i * (dilateTest k hk f).val x := by
  have h : (fun x : Space => ((ε (k • x) : ℝ) : ℂ) * E (k • x) i * f.val x) =
      fun x : Space => (fun y : Space =>
        ((ε y : ℝ) : ℂ) * E y i * f.val (k⁻¹ • y)) (k • x) := by
    funext x
    simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul]
  rw [h, Measure.integral_comp_smul (volume : Measure Space)
    (fun y : Space => ((ε y : ℝ) : ℂ) * E y i * f.val (k⁻¹ • y)) k]
  simp only [finrank_euclideanSpace, Fintype.card_fin,
    abs_of_pos (inv_pos.mpr (pow_pos hk 3)), Complex.real_smul]
  rfl

theorem testMaxwell_scale (k : ℝ) (hk : 0 < k) (ε : Space → ℝ) (E H : Field)
    (hM : TestMaxwell 1 ε E H) :
    TestMaxwell k (fun x => ε (k • x)) (PuncturedMaxwellScaling.fieldAtFrequency k E)
      (PuncturedMaxwellScaling.fieldAtFrequency k H) := by
  have hk0 : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk.ne'
  intro i f
  obtain ⟨h1, h2⟩ := hM i (dilateTest k hk f)
  simp only [Complex.ofReal_one, mul_one] at h1 h2
  constructor
  · rw [curlPair_scale k hk E i f, h1, fieldPair_scale k hk H i f]
    push_cast
    field_simp
    ring
  · have h3 := coeff_integral_scale k hk ε E i f
    change curlPair (fieldPair (PuncturedMaxwellScaling.fieldAtFrequency k H)) i f =
      -(Complex.I * (k : ℂ)) * (∫ x, ((ε (k • x) : ℝ) : ℂ) * E (k • x) i * f.val x)
    rw [h3, curlPair_scale k hk H i f, h2]
    push_cast
    field_simp
    ring

theorem fieldPair_smul (E : Field) (z : ℂ) (i : Fin 3) (f : Test) :
    fieldPair (fun x => z • E x) i f = z * fieldPair E i f := by
  unfold fieldPair
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem curlPair_smul (E : Field) (z : ℂ) (i : Fin 3) (f : Test) :
    curlPair (fieldPair (fun x => z • E x)) i f = z * curlPair (fieldPair E) i f := by
  unfold curlPair
  rw [fieldPair_smul, fieldPair_smul]
  ring

theorem coeff_integral_smul (ε : Space → ℝ) (E : Field) (z : ℂ) (i : Fin 3) (f : Test) :
    (∫ x, (ε x : ℂ) * (z • E x) i * f.val x) = z * ∫ x, (ε x : ℂ) * E x i * f.val x := by
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem testMaxwell_smul (k : ℝ) (ε : Space → ℝ) (E H : Field) (z : ℂ)
    (hM : TestMaxwell k ε E H) :
    TestMaxwell k ε (fun x => z • E x) (fun x => z • H x) := by
  intro i f
  obtain ⟨h1, h2⟩ := hM i f
  constructor
  · rw [curlPair_smul, fieldPair_smul, h1]
    ring
  · rw [curlPair_smul, coeff_integral_smul, h2]
    ring

theorem testMaxwell_scaleField (k : ℝ) (hk : 0 < k) (ε : Space → ℝ) (E H : Field)
    (hM : TestMaxwell 1 ε E H) :
    TestMaxwell k (fun x => ε (k • x)) (scaleField k E) (scaleField k H) :=
  testMaxwell_smul k (fun x => ε (k • x)) (PuncturedMaxwellScaling.fieldAtFrequency k E)
    (PuncturedMaxwellScaling.fieldAtFrequency k H) (k : ℂ) (testMaxwell_scale k hk ε E H hM)

theorem testMaxwell_scaleCoeff (k : ℝ) (hk : 0 < k) (c : Coefficient) (E H : Field)
    (hM : TestMaxwell 1 (dielectric c) E H) :
    TestMaxwell k (dielectric (scaleCoeff k c)) (scaleField k E) (scaleField k H) := by
  rw [dielectric_scaleCoeff_eq]
  exact testMaxwell_scaleField k hk (dielectric c) E H hM

theorem testMaxwell_vacuum_scale (k : ℝ) (hk : 0 < k) (E H : Field)
    (hM : TestMaxwell 1 (fun _ => 1) E H) :
    TestMaxwell k (fun _ => 1) (scaleField k E) (scaleField k H) :=
  testMaxwell_scaleField k hk (fun _ => 1) E H hM

end OQ14.FrequencyScalingMaxwell

#print axioms OQ14.FrequencyScalingMaxwell.scaleField_apply
#print axioms OQ14.FrequencyScalingMaxwell.scaleCoeff_value
#print axioms OQ14.FrequencyScalingMaxwell.coordinateMap_smul
#print axioms OQ14.FrequencyScalingMaxwell.dielectric_scaleCoeff
#print axioms OQ14.FrequencyScalingMaxwell.dielectric_scaleCoeff_bounds
#print axioms OQ14.FrequencyScalingMaxwell.dielectric_scaleCoeff_eq
#print axioms OQ14.FrequencyScalingMaxwell.dilateSchwartz_apply
#print axioms OQ14.FrequencyScalingMaxwell.dilateTest_apply
#print axioms OQ14.FrequencyScalingMaxwell.dilateTest_val
#print axioms OQ14.FrequencyScalingMaxwell.testPartial_dilateTest
#print axioms OQ14.FrequencyScalingMaxwell.fieldPair_scale
#print axioms OQ14.FrequencyScalingMaxwell.testPartial_pair_scale
#print axioms OQ14.FrequencyScalingMaxwell.testPartial_pair_scale'
#print axioms OQ14.FrequencyScalingMaxwell.curlPair_scale
#print axioms OQ14.FrequencyScalingMaxwell.coeff_integral_scale
#print axioms OQ14.FrequencyScalingMaxwell.testMaxwell_scale
#print axioms OQ14.FrequencyScalingMaxwell.fieldPair_smul
#print axioms OQ14.FrequencyScalingMaxwell.curlPair_smul
#print axioms OQ14.FrequencyScalingMaxwell.coeff_integral_smul
#print axioms OQ14.FrequencyScalingMaxwell.testMaxwell_smul
#print axioms OQ14.FrequencyScalingMaxwell.testMaxwell_scaleField
#print axioms OQ14.FrequencyScalingMaxwell.testMaxwell_scaleCoeff
#print axioms OQ14.FrequencyScalingMaxwell.testMaxwell_vacuum_scale
