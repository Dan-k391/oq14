import CapSturmLiouville

/-! Genuine endpoint integration by parts for the actual cap profile and integrable interior test slopes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.CapSturmEndpointTest
open MeasureTheory Set Real OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology

theorem legendre_ibp (f fD fDD v vD : ℝ → ℝ) (a A B : ℝ) (hAB : A ≤ B)
    (hf : ∀ z ∈ Icc A B, HasDerivAt f (fD z) z)
    (hD : ∀ z ∈ Icc A B, HasDerivAt fD (fDD z) z)
    (hode : ∀ z ∈ Icc A B, (1-z^2)*fDD z-2*z*fD z+a*f z=0)
    (hv : ∀ z ∈ Ioo A B, HasDerivAt v (vD z) z)
    (hvc : ContinuousOn v (Icc A B)) (hvi : IntervalIntegrable vD volume A B) :
    (∫ z in A..B, (1-z^2)*fD z*vD z) =
      (1-B^2)*fD B*v B - (1-A^2)*fD A*v A + a*∫ z in A..B, f z*v z := by
  have hfc : ContinuousOn f (Icc A B) := fun z hz => (hf z hz).continuousAt.continuousWithinAt
  have hDc : ContinuousOn fD (Icc A B) := fun z hz => (hD z hz).continuousAt.continuousWithinAt
  have hU : ContinuousOn (fun z => (1-z^2)*fD z) (Icc A B) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn.mul hDc
  have hd (z : ℝ) (hz : z ∈ Icc A B) :
      HasDerivAt (fun z => (1-z^2)*fD z) (-a*f z) z := by
    convert (((hasDerivAt_id z).pow 2).const_sub 1).mul (hD z hz) using 1
    simp only [id_eq]
    norm_num
    nlinarith [hode z hz]
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := A) (b := B) (u' := fun z => -a*f z) (v := v) (v' := vD)
    (by simpa only [uIcc_of_le hAB] using hU)
    (by simpa only [uIcc_of_le hAB] using hvc)
    (fun z hz => hd z (Ioo_subset_Icc_self (by simpa [min_eq_left hAB,max_eq_right hAB] using hz)))
    (fun z hz => hv z (by simpa [min_eq_left hAB,max_eq_right hAB] using hz))
    (by simpa only [uIcc_of_le hAB] using (continuousOn_const.mul hfc).intervalIntegrable_of_Icc hAB)
    hvi
  dsimp only at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at h
  simpa only [mul_assoc, neg_mul, sub_neg_eq_add] using h

theorem weighted_weak_identity (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : determinant d t a = 0)
    (v vD : ℝ → ℝ) (hv : ∀ z ∈ Ioo (-1 : ℝ) 1, HasDerivAt v (vD z) z)
    (hvc : ContinuousOn v (Icc (-1 : ℝ) 1)) (hvi : IntervalIntegrable vD volume (-1) 1) :
    (∫ z in (-1 : ℝ)..1, coefficient d t z*((1-z^2)*slope a t z*vD z)) =
      a*∫ z in (-1 : ℝ)..1, coefficient d t z*(profile a t z*v z) := by
  have hL (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) (-t)) := negative_hasDerivAt a t z ha (left_argument t z ht ht1 hz)
  have hLD (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) (-t)) := negativeD_hasDerivAt a t z ha (left_argument t z ht ht1 hz)
  have hM (z : ℝ) (hz : z ∈ Icc (-t) t) := interior_hasDerivAt a t z ha (middle_argument t z ht1 hz)
  have hMD (z : ℝ) (hz : z ∈ Icc (-t) t) := interiorD_hasDerivAt a t z ha (middle_argument t z ht1 hz)
  have hR (z : ℝ) (hz : z ∈ Icc t 1) := exterior_hasDerivAt a t z ha (right_argument t z ht ht1 hz)
  have hRD (z : ℝ) (hz : z ∈ Icc t 1) := exteriorD_hasDerivAt a t z ha (right_argument t z ht ht1 hz)
  have sL : Icc (-1 : ℝ) (-t) ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc le_rfl (by linarith)
  have sM : Icc (-t) t ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by linarith) ht1.le
  have sR : Icc t 1 ⊆ Icc (-1 : ℝ) 1 := Icc_subset_Icc (by linarith) le_rfl
  have iL : IntervalIntegrable vD volume (-1) (-t) := hvi.mono_set (by simpa [uIcc_of_le (show (-1:ℝ)≤1 by norm_num), uIcc_of_le (show (-1:ℝ)≤-t by linarith)] using sL)
  have iM : IntervalIntegrable vD volume (-t) t := hvi.mono_set (by simpa [uIcc_of_le (show (-1:ℝ)≤1 by norm_num), uIcc_of_le (show -t≤t by linarith)] using sM)
  have iR : IntervalIntegrable vD volume t 1 := hvi.mono_set (by simpa [uIcc_of_le (show (-1:ℝ)≤1 by norm_num), uIcc_of_le ht1.le] using sR)
  have cL : ContinuousOn (negative a t) (Icc (-1 : ℝ) (-t)) := fun z hz => (hL z hz).continuousAt.continuousWithinAt
  have cLD : ContinuousOn (negativeD a t) (Icc (-1 : ℝ) (-t)) := fun z hz => (hLD z hz).continuousAt.continuousWithinAt
  have cM : ContinuousOn (CapAngularShooting.interior a t) (Icc (-t) t) := fun z hz => (hM z hz).continuousAt.continuousWithinAt
  have cMD : ContinuousOn (interiorD a t) (Icc (-t) t) := fun z hz => (hMD z hz).continuousAt.continuousWithinAt
  have cR : ContinuousOn (exterior a t) (Icc t 1) := fun z hz => (hR z hz).continuousAt.continuousWithinAt
  have cRD : ContinuousOn (exteriorD a t) (Icc t 1) := fun z hz => (hRD z hz).continuousAt.continuousWithinAt
  have eL : IntervalIntegrable (fun z => (1+d)*((1-z^2)*negativeD a t z*vD z)) volume (-1) (-t) := by
    have h := iL.continuousOn_mul (by simpa only [uIcc_of_le (show (-1:ℝ)≤-t by linarith)] using (show ContinuousOn (fun z:ℝ => (1-z^2)*negativeD a t z) (Icc (-1) (-t)) from (continuous_const.sub (continuous_id.pow 2)).continuousOn.mul cLD))
    have h' := h.const_mul (1+d)
    simpa only [uIcc_of_le (show (-1:ℝ)≤-t by linarith)] using h'
  have eM : IntervalIntegrable (fun z => (1-z^2)*interiorD a t z*vD z) volume (-t) t := by
    apply iM.continuousOn_mul
    simpa only [uIcc_of_le (show -t≤t by linarith)] using (continuous_const.sub (continuous_id.pow 2)).continuousOn.mul cMD
  have eR : IntervalIntegrable (fun z => (1+d)*((1-z^2)*exteriorD a t z*vD z)) volume t 1 := by
    have h := iR.continuousOn_mul (by simpa only [uIcc_of_le ht1.le] using (show ContinuousOn (fun z:ℝ => (1-z^2)*exteriorD a t z) (Icc t 1) from (continuous_const.sub (continuous_id.pow 2)).continuousOn.mul cRD))
    exact h.const_mul (1+d)
  have mL : IntervalIntegrable (fun z => (1+d)*(negative a t z*v z)) volume (-1) (-t) :=
    (continuousOn_const.mul (cL.mul (hvc.mono sL))).intervalIntegrable_of_Icc (by linarith)
  have mM : IntervalIntegrable (fun z => CapAngularShooting.interior a t z*v z) volume (-t) t :=
    (cM.mul (hvc.mono sM)).intervalIntegrable_of_Icc (by linarith)
  have mR : IntervalIntegrable (fun z => (1+d)*(exterior a t z*v z)) volume t 1 :=
    (continuousOn_const.mul (cR.mul (hvc.mono sR))).intervalIntegrable_of_Icc ht1.le
  have hne : ∀ᵐ z : ℝ, z ≠ -t := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  have splitE := integral_three (fun z => coefficient d t z*((1-z^2)*slope a t z*vD z))
    (fun z => (1+d)*((1-z^2)*negativeD a t z*vD z))
    (fun z => (1-z^2)*interiorD a t z*vD z)
    (fun z => (1+d)*((1-z^2)*exteriorD a t z*vD z)) t ht ht1 eL eM eR (by
      filter_upwards [hne] with z hzne
      intro hz
      have hzt : z < -t := lt_of_le_of_ne hz.2 hzne
      simp [coefficient_left d t z hzt ht, CapSturmLiouville.slope, hzt]) (by
      filter_upwards with z
      intro hz
      simp [coefficient_middle d t z ⟨hz.1.le,hz.2⟩, CapSturmLiouville.slope, not_lt.mpr hz.1.le, hz.2]) (by
      filter_upwards with z
      intro hz
      simp [coefficient_right d t z hz.1 ht, CapSturmLiouville.slope, not_le.mpr hz.1, show ¬z < -t by linarith [hz.1]])
  have splitM := integral_three (fun z => coefficient d t z*(profile a t z*v z))
    (fun z => (1+d)*(negative a t z*v z))
    (fun z => CapAngularShooting.interior a t z*v z)
    (fun z => (1+d)*(exterior a t z*v z)) t ht ht1 mL mM mR (by
      filter_upwards [hne] with z hzne
      intro hz
      have hzt : z < -t := lt_of_le_of_ne hz.2 hzne
      simp [coefficient_left d t z hzt ht, profile, hzt]) (by
      filter_upwards with z
      intro hz
      simp [coefficient_middle d t z ⟨hz.1.le,hz.2⟩, profile_middle a t z ⟨hz.1.le,hz.2⟩]) (by
      filter_upwards with z
      intro hz
      simp [coefficient_right d t z hz.1 ht, profile_right a t z ht ⟨hz.1.le,hz.2⟩])
  have ibL := legendre_ibp _ _ _ v vD a (-1) (-t) (by linarith) hL hLD
    (fun z hz => negative_legendre a t z ha (left_argument t z ht ht1 hz)) (fun z hz => hv z ⟨by linarith [hz.1], by linarith [hz.2]⟩) (hvc.mono sL) iL
  have ibM := legendre_ibp _ _ _ v vD a (-t) t (by linarith) hM hMD
    (fun z hz => interior_legendre a t z ha (middle_argument t z ht1 hz)) (fun z hz => hv z ⟨by linarith [hz.1], by linarith [hz.2]⟩) (hvc.mono sM) iM
  have ibR := legendre_ibp _ _ _ v vD a t 1 ht1.le hR hRD
    (fun z hz => exterior_legendre a t z ha (right_argument t z ht ht1 hz)) (fun z hz => hv z ⟨by linarith [hz.1], by linarith [hz.2]⟩) (hvc.mono sR) iR
  rw [splitE, splitM]
  simp only [intervalIntegral.integral_const_mul]
  rw [ibL,ibM,ibR]
  simp only [neg_sq, one_pow, sub_self, zero_mul, sub_zero, negativeD, neg_neg,
    interiorD_even, flux_matching d t a hroot]
  ring


end OQ14.CapSturmEndpointTest

#print axioms OQ14.CapSturmEndpointTest.legendre_ibp
#print axioms OQ14.CapSturmEndpointTest.weighted_weak_identity
