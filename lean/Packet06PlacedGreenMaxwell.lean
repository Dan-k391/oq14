import Packet06CyclicRotationMaxwell
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedGreenMaxwell
open MeasureTheory Maxwell DynamicSource MagneticResponse MaterialMaxwell Packet06CyclicRotation
open Packet06CyclicRotationTests Packet06CyclicRotationMaxwell FrequencyScalingMaxwell KernelConvolution
open WeakCurl (next previous)
open scoped SchwartzMap

/-- Exact second-order weak Maxwell equation for an electric source. -/
def weakSecond (z : ℂ) (ε : Space → ℝ) (E J : Field) : Prop :=
  ∀ (i : Fin 3) (φ : Test),
    (∑ l : Fin 3, fieldPair E l (testPartial l (testPartial i φ))) -
    (∑ l : Fin 3, fieldPair E i (testPartial l (testPartial l φ))) -
    z^2*(∫ x : Space, (ε x : ℂ)*E x i*φ.val x) = fieldPair J i φ

theorem second_rotate_pair (E : Field) (i : Fin 3) (φ : Test) :
    (∑ l : Fin 3, fieldPair (rotateField E) l (testPartial l (testPartial i φ))) -
    (∑ l : Fin 3, fieldPair (rotateField E) i (testPartial l (testPartial l φ))) =
    (∑ l : Fin 3, fieldPair E l (testPartial l (testPartial (previous i) (rotateTest φ)))) -
    (∑ l : Fin 3, fieldPair E (previous i) (testPartial l (testPartial l (rotateTest φ)))) := by
  simp only [Fin.sum_univ_three]
  simp_rw [fieldPair_rotate,rotateTest_partial_comm]
  fin_cases i <;> simp [previous] <;> ring

theorem rotate (z : ℂ) (ε : Space → ℝ) (E J : Field) (h : weakSecond z ε E J) :
    weakSecond z (fun x => ε (unrotate x)) (rotateField E) (rotateField J) := by
  intro i φ
  rw [second_rotate_pair,dielectric_pair_rotate,fieldPair_rotate]
  exact h (previous i) (rotateTest φ)

theorem second_dilate_pair (s : ℝ) (hs : 0 < s) (E : Field) (i : Fin 3) (φ : Test) :
    (∑ l : Fin 3, fieldPair (PuncturedMaxwellScaling.fieldAtFrequency s E) l (testPartial l (testPartial i φ))) -
    (∑ l : Fin 3, fieldPair (PuncturedMaxwellScaling.fieldAtFrequency s E) i (testPartial l (testPartial l φ))) =
    ((s⁻¹ : ℝ) : ℂ) *
      ((∑ l : Fin 3, fieldPair E l (testPartial l (testPartial i (dilateTest s hs φ)))) -
       (∑ l : Fin 3, fieldPair E i (testPartial l (testPartial l (dilateTest s hs φ))))) := by
  have hp (j k l : Fin 3) : fieldPair (PuncturedMaxwellScaling.fieldAtFrequency s E) j
      (testPartial k (testPartial l φ)) = ((s⁻¹ : ℝ) : ℂ) *
        fieldPair E j (testPartial k (testPartial l (dilateTest s hs φ))) := by
    have hsch : (testPartial l (dilateTest s hs φ)).val =
        ((s⁻¹ : ℝ) : ℂ) • (dilateTest s hs (testPartial l φ)).val := by
      ext x
      simp only [testPartial_dilateTest,dilateTest_apply,SchwartzMap.smul_apply,smul_eq_mul]
    have hpder := congrArg (GradientProjection.pderivative k) hsch
    simp only [GradientProjection.pderivative,map_smul] at hpder
    have hpair : fieldPair E j (testPartial k (testPartial l (dilateTest s hs φ))) =
        ((s⁻¹ : ℝ) : ℂ) * fieldPair E j (testPartial k (dilateTest s hs (testPartial l φ))) := by
      unfold fieldPair
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      have hx := congrArg (fun f : 𝓢(Space, ℂ) => f x) hpder
      simp only [SchwartzMap.smul_apply,smul_eq_mul] at hx
      change E x j * ((SchwartzMap.pderivCLM ℂ (basis k)) (testPartial l (dilateTest s hs φ)).val) x =
        ((s⁻¹ : ℝ) : ℂ) * (E x j * ((SchwartzMap.pderivCLM ℂ (basis k))
          (dilateTest s hs (testPartial l φ)).val) x)
      rw [hx]
      ring
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    rw [fieldPair_scale s hs E j, testPartial_pair_scale' s hs E j k (testPartial l φ),hpair]
    push_cast
    field_simp
    ring
  simp_rw [hp]
  simp only [Finset.mul_sum,mul_sub]

theorem dilate (z : ℂ) (s : ℝ) (hs : 0 < s) (ε : Space → ℝ) (E J : Field)
    (h : weakSecond z ε E J) :
    weakSecond ((s : ℂ)*z) (fun x => ε (s • x))
      (PuncturedMaxwellScaling.fieldAtFrequency s E)
      (fun x i => (s : ℂ)^2 * J (s • x) i) := by
  intro i φ
  have he := h i (dilateTest s hs φ)
  have hsrc : fieldPair (fun x i => (s : ℂ)^2 * J (s • x) i) i φ =
      ((s⁻¹ : ℝ) : ℂ) * fieldPair J i (dilateTest s hs φ) := by
    have hh := fieldPair_scale s hs J i φ
    unfold fieldPair
    have he : (fun x : Space => (s : ℂ)^2 * J (s • x) i * φ.val x) =
        (fun x => (s : ℂ)^2 * (J (s • x) i * φ.val x)) := by funext x; ring
    rw [he,integral_const_mul]
    change (s : ℂ)^2 * fieldPair (PuncturedMaxwellScaling.fieldAtFrequency s J) i φ = _
    rw [hh]
    push_cast
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
    simp only [fieldPair]
    ring
  rw [second_dilate_pair s hs]
  change _ - ((s : ℂ)*z)^2 * (∫ x, (ε (s • x) : ℂ)*E (s • x) i*φ.val x) = _
  rw [coeff_integral_scale s hs ε E i φ,hsrc]
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have hfactor : ((s : ℂ)*z)^2 * (((s^3)⁻¹ : ℝ) : ℂ) = ((s⁻¹ : ℝ) : ℂ)*z^2 := by
    push_cast
    field_simp
    ring
  rw [← mul_assoc,hfactor]
  linear_combination (((s⁻¹ : ℝ) : ℂ)) * he

theorem translate (z : ℂ) (ε : Space → ℝ) (E J : Field)
    (h : weakSecond z ε E J) (a : Space) :
    weakSecond z (fun x => ε (x-a)) (fun x => E (x-a)) (fun x => J (x-a)) := by
  have hp (F : Field) (i : Fin 3) (φ : Test) :
      fieldPair (fun x => F (x-a)) i φ = fieldPair F i (KernelConvolution.translate a φ) := by
    unfold fieldPair
    exact (translated_pairing (fun x => F x i) a φ).symm
  intro i φ
  have hi : (∫ x, (ε (x-a) : ℂ) * E (x-a) i * φ.val x) =
      ∫ x, (ε x : ℂ) * E x i * (KernelConvolution.translate a φ).val x := by
    exact (translated_pairing (fun x => (ε x : ℂ) * E x i) a φ).symm
  simp_rw [hp, translate_partial]
  rw [hi]
  exact h i (KernelConvolution.translate a φ)

theorem amplitude (z α : ℂ) (ε : Space → ℝ) (E J : Field)
    (h : weakSecond z ε E J) :
    weakSecond z ε (fun x => α • E x) (fun x => α • J x) := by
  intro i φ
  simp_rw [fieldPair_smul, coeff_integral_smul, ← Finset.mul_sum]
  have hh := h i φ
  linear_combination α * hh

/-- Simultaneous rigid placement, frequency dilation and amplitude transport. -/
theorem placed (z α : ℂ) (s : ℝ) (hs : 0 < s) (a : Space)
    (ε : Space → ℝ) (E J : Field) (h : weakSecond z ε E J) :
    weakSecond ((s : ℂ)*z) (fun x => ε (unrotate (s • (x-a))))
      (fun x => α • rotateField E (s • (x-a)))
      (fun x => α • ((s : ℂ)^2 • rotateField J (s • (x-a)))) := by
  have hr := rotate z ε E J h
  have hd := dilate z s hs _ _ _ hr
  have ht := translate ((s : ℂ)*z) _ _ _ hd a
  have ha := amplitude ((s : ℂ)*z) α _ _ _ ht
  simpa [PuncturedMaxwellScaling.fieldAtFrequency, Pi.smul_apply, smul_eq_mul] using ha

#print axioms OQ14.Packet06PlacedGreenMaxwell.placed
#print axioms OQ14.Packet06PlacedGreenMaxwell.amplitude
#print axioms OQ14.Packet06PlacedGreenMaxwell.translate
#print axioms OQ14.Packet06PlacedGreenMaxwell.second_dilate_pair
#print axioms OQ14.Packet06PlacedGreenMaxwell.dilate
#print axioms OQ14.Packet06PlacedGreenMaxwell.second_rotate_pair
#print axioms OQ14.Packet06PlacedGreenMaxwell.rotate
end OQ14.Packet06PlacedGreenMaxwell
