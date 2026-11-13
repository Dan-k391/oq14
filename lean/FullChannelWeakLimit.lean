import FullChannelMagnetic

/-! Stability of weak Maxwell test pairings under uniform field approximation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FullChannelWeakLimit
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse
open WeakCurl (next previous)

/-- A compact smooth test gives an integrable product with every continuous field. -/
theorem test_integrable (f : Test) : Integrable (fun x : Maxwell.Space => ‖f.val x‖) :=
  f.val.continuous.norm.integrable_of_hasCompactSupport f.property.norm

/-- Uniform field error transfers to the exact weak test pairing. -/
theorem pair_difference_bound (E G : Maxwell.Field) (i : Fin 3) (f : Test) (M : ℝ)
    (hE : Continuous (fun x => E x i)) (hG : Continuous (fun x => G x i))
    (hM : ∀ x, ‖E x i - G x i‖ ≤ M) :
    ‖fieldPair E i f - fieldPair G i f‖ ≤ M * ∫ x, ‖f.val x‖ := by
  have he : Integrable (fun x => E x i * f.val x) :=
    (hE.mul f.val.continuous).integrable_of_hasCompactSupport f.property.mul_left
  have hg : Integrable (fun x => G x i * f.val x) :=
    (hG.mul f.val.continuous).integrable_of_hasCompactSupport f.property.mul_left
  rw [fieldPair, fieldPair, ← integral_sub he hg]
  calc
    _ ≤ ∫ x, ‖E x i * f.val x - G x i * f.val x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, M * ‖f.val x‖ := by
      apply integral_mono_ae (he.sub hg).norm ((test_integrable f).const_mul M)
      filter_upwards with x
      change ‖E x i * f.val x - G x i * f.val x‖ ≤ _
      rw [← sub_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- Uniform field approximation also controls the distributional curl pairing. -/
theorem curl_difference_bound (E G : Maxwell.Field) (i : Fin 3) (f : Test) (M : ℝ)
    (hE : ∀ j, Continuous (fun x => E x j)) (hG : ∀ j, Continuous (fun x => G x j))
    (hM : ∀ x j, ‖E x j - G x j‖ ≤ M) :
    ‖curlPair (fieldPair E) i f - curlPair (fieldPair G) i f‖ ≤
      M * (∫ x, ‖(testPartial (previous i) f).val x‖) +
      M * (∫ x, ‖(testPartial (next i) f).val x‖) := by
  have h1 := pair_difference_bound E G (next i) (testPartial (previous i) f) M
    (hE _) (hG _) (fun x => hM x _)
  have h2 := pair_difference_bound E G (previous i) (testPartial (next i) f) M
    (hE _) (hG _) (fun x => hM x _)
  unfold curlPair
  have he : fieldPair E (next i) (testPartial (previous i) f) -
      fieldPair E (previous i) (testPartial (next i) f) -
      (fieldPair G (next i) (testPartial (previous i) f) -
       fieldPair G (previous i) (testPartial (next i) f)) =
      (fieldPair E (next i) (testPartial (previous i) f) - fieldPair G (next i) (testPartial (previous i) f)) -
      (fieldPair E (previous i) (testPartial (next i) f) - fieldPair G (previous i) (testPartial (next i) f)) := by ring
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add h1 h2)

/-- Weak curl identities are closed under uniform approximation by actual solutions. -/
theorem weak_curl_closed (E H : Maxwell.Field) (a : ℂ)
    (hE : ∀ j, Continuous (fun x => E x j)) (hH : ∀ j, Continuous (fun x => H x j))
    (happrox : ∀ ε > 0, ∃ E' H' : Maxwell.Field,
      (∀ j, Continuous (fun x => E' x j)) ∧ (∀ j, Continuous (fun x => H' x j)) ∧
      (∀ x j, ‖E x j-E' x j‖ ≤ ε) ∧ (∀ x j, ‖H x j-H' x j‖ ≤ ε) ∧
      ∀ i f, curlPair (fieldPair E') i f = a * fieldPair H' i f) :
    ∀ i f, curlPair (fieldPair E) i f = a * fieldPair H i f := by
  intro i f
  let C : ℝ := (∫ x, ‖(testPartial (previous i) f).val x‖) +
    (∫ x, ‖(testPartial (next i) f).val x‖) + ‖a‖ * (∫ x, ‖f.val x‖)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hz : ‖curlPair (fieldPair E) i f - a * fieldPair H i f‖ ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro δ hδ
    let ε := δ / (C + 1)
    have hε : 0 < ε := div_pos hδ (by linarith)
    obtain ⟨E', H', hE', hH', he, hh, hidentity⟩ := happrox ε hε
    have hc := curl_difference_bound E E' i f ε hE hE' he
    have hp := pair_difference_bound H H' i f ε (hH i) (hH' i) (fun x => hh x i)
    have heq : curlPair (fieldPair E) i f - a * fieldPair H i f =
      (curlPair (fieldPair E) i f - curlPair (fieldPair E') i f) -
        a * (fieldPair H i f - fieldPair H' i f) := by rw [hidentity i f]; ring
    rw [heq]
    calc
      _ ≤ ‖curlPair (fieldPair E) i f - curlPair (fieldPair E') i f‖ +
            ‖a * (fieldPair H i f - fieldPair H' i f)‖ := norm_sub_le _ _
      _ ≤ ε * (∫ x, ‖(testPartial (previous i) f).val x‖) +
          ε * (∫ x, ‖(testPartial (next i) f).val x‖) +
          ‖a‖ * (ε * (∫ x, ‖f.val x‖)) := by rw [norm_mul]; exact add_le_add hc (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
      _ = ε * C := by dsimp [C]; ring
      _ ≤ 0 + δ := by
        dsimp [ε]
        have hdiv : δ / (C+1) * C ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : 0 < C+1)]
          nlinarith
        linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- Magnetic L² evaluation agrees with the actual finite transverse-harmonic incident field. -/
theorem finite_magnetic_value (k : ℝ) (c : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (x : Maxwell.Space) (i : Fin 3) :
    FullChannelMagnetic.magnetic k (HerglotzAngularL2.finiteAmplitude c) x i =
      (FiniteAngularHerglotz.incident k c).H x i := by
  unfold FullChannelMagnetic.magnetic
  have hc : ContinuousMap.toLp 2 SphereHarmonicBasis.angularMeasure ℂ (FiniteVectorAngular.amplitude c) =
      HerglotzAngularL2.finiteAmplitude c := by
    simpa only [HerglotzAngularL2.finiteAmplitude, Finsupp.sum] using FiniteVectorAngular.amplitude_toLp c
  rw [← hc]
  exact FullChannelMagnetic.magnetic_value_toLp k (FiniteVectorAngular.amplitude c) x i

/-- One finite Maxwell illumination approximates both general electric and magnetic fields uniformly. -/
theorem simultaneous_finite_approximation (k : ℝ) (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ComplexTransverseExpansion.ModeIndex →₀ ℂ,
      (∀ x i, ‖HerglotzAngularL2.value k x i F - (FiniteAngularHerglotz.incident k c).E x i‖ ≤ ε) ∧
      (∀ x i, ‖FullChannelMagnetic.magnetic k F x i - (FiniteAngularHerglotz.incident k c).H x i‖ ≤ ε) := by
  let K := 7 * (HerglotzAngularL2.bound + 1)
  have hB := HerglotzAngularL2.bound_nonnegative
  have hK : 0 < K := by dsimp [K]; linarith
  obtain ⟨c, hc⟩ := HerglotzAngularL2.finite_approximation F hF (ε / K) (div_pos hε hK)
  have hnorm : ‖F - HerglotzAngularL2.finiteAmplitude c‖ < ε / K := by
    rwa [norm_sub_rev]
  have hb : HerglotzAngularL2.bound * ‖F - HerglotzAngularL2.finiteAmplitude c‖ ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hnorm.le hB
    have hk : HerglotzAngularL2.bound ≤ K := by dsimp [K]; linarith
    have hn := mul_le_mul_of_nonneg_right hk (le_of_lt (div_pos hε hK))
    calc
      _ ≤ HerglotzAngularL2.bound * (ε / K) := hm
      _ ≤ K * (ε / K) := hn
      _ = ε := by field_simp
  have hb6 : (6 * HerglotzAngularL2.bound) * ‖F - HerglotzAngularL2.finiteAmplitude c‖ ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hnorm.le (by positivity : 0 ≤ 6 * HerglotzAngularL2.bound)
    have hk : 6 * HerglotzAngularL2.bound ≤ K := by dsimp [K]; linarith
    have hn := mul_le_mul_of_nonneg_right hk (le_of_lt (div_pos hε hK))
    calc
      _ ≤ (6 * HerglotzAngularL2.bound) * (ε / K) := hm
      _ ≤ K * (ε / K) := hn
      _ = ε := by field_simp
  refine ⟨c, ?_, ?_⟩
  · intro x i
    rw [FiniteAngularHerglotz.electric_value]
    exact (HerglotzAngularL2.value_difference_bound k x i F _).trans hb
  · intro x i
    rw [← finite_magnetic_value]
    exact (FullChannelMagnetic.magnetic_difference_bound k F _ x i).trans hb6

/-- Every transverse angular L² amplitude generates an actual weak vacuum Maxwell pair. -/
theorem herglotz_testMaxwell (k : ℝ) (F : ComplexVectorSphere.Ambient)
    (hF : ComplexVectorSphere.IsTangential F) :
    MaterialMaxwell.TestMaxwell k (fun _ => 1)
      (fun x i => HerglotzAngularL2.value k x i F) (FullChannelMagnetic.magnetic k F) := by
  let E : Maxwell.Field := fun x i => HerglotzAngularL2.value k x i F
  let H : Maxwell.Field := FullChannelMagnetic.magnetic k F
  have hE : ∀ j, Continuous (fun x => E x j) := fun j => FullChannelHerglotz.electric_continuous k F hF j
  have hH : ∀ j, Continuous (fun x => H x j) := fun j => FullChannelMagnetic.magnetic_continuous k F j
  have ha : ∀ ε > 0, ∃ E' H' : Maxwell.Field,
      (∀ j, Continuous (fun x => E' x j)) ∧ (∀ j, Continuous (fun x => H' x j)) ∧
      (∀ x j, ‖E x j-E' x j‖ ≤ ε) ∧ (∀ x j, ‖H x j-H' x j‖ ≤ ε) ∧
      MaterialMaxwell.TestMaxwell k (fun _ => 1) E' H' := by
    intro ε hε
    obtain ⟨c, he, hh⟩ := simultaneous_finite_approximation k F hF ε hε
    let I := FiniteAngularHerglotz.incident k c
    refine ⟨I.E, I.H, (fun j => (I.smoothE j).continuous), (fun j => (I.smoothH j).continuous), he, hh, ?_⟩
    exact MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H
      (fun j => (I.smoothE j).of_le (by simp)) (fun j => (I.smoothH j).of_le (by simp)) I.maxwell
  have h1 := weak_curl_closed E H (Complex.I * (k : ℂ)) hE hH (by
    intro ε hε
    obtain ⟨E', H', he, hh, hde, hdh, hm⟩ := ha ε hε
    exact ⟨E', H', he, hh, hde, hdh, fun i f => (hm i f).1⟩)
  have h2 := weak_curl_closed H E (-(Complex.I * (k : ℂ))) hH hE (by
    intro ε hε
    obtain ⟨E', H', he, hh, hde, hdh, hm⟩ := ha ε hε
    refine ⟨H', E', hh, he, hdh, hde, ?_⟩
    intro i f
    simpa only [Complex.ofReal_one, one_mul, MaterialMaxwell.fieldPair] using (hm i f).2)
  intro i f
  refine ⟨h1 i f, ?_⟩
  simpa only [Complex.ofReal_one, one_mul, MaterialMaxwell.fieldPair] using h2 i f

end OQ14.FullChannelWeakLimit
#print axioms OQ14.FullChannelWeakLimit.test_integrable
#print axioms OQ14.FullChannelWeakLimit.pair_difference_bound

#print axioms OQ14.FullChannelWeakLimit.curl_difference_bound

#print axioms OQ14.FullChannelWeakLimit.weak_curl_closed

#print axioms OQ14.FullChannelWeakLimit.finite_magnetic_value
#print axioms OQ14.FullChannelWeakLimit.simultaneous_finite_approximation

#print axioms OQ14.FullChannelWeakLimit.herglotz_testMaxwell
