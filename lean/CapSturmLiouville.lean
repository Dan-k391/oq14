import CapAngularShooting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! Actual piecewise Legendre profile and its one-dimensional transmission equation. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.CapSturmLiouville
open MeasureTheory Set OQ14.CapLegendreSeries OQ14.CapAngularShooting
open scoped Topology

def negative (a t z : ℝ) : ℝ := -exterior a t (-z)
def negativeD (a t z : ℝ) : ℝ := exteriorD a t (-z)
def negativeDD (a t z : ℝ) : ℝ := -exteriorDD a t (-z)
def profile (a t z : ℝ) : ℝ :=
  if z < -t then negative a t z else if z ≤ t then interior a t z else exterior a t z
def slope (a t z : ℝ) : ℝ :=
  if z < -t then negativeD a t z else if z ≤ t then interiorD a t z else exteriorD a t z
def coefficient (d t z : ℝ) : ℝ := if |z| ≤ t then 1 else 1+d

theorem interior_odd (a t z : ℝ) : interior a t (-z) = -interior a t z := by
  simp [CapAngularShooting.interior, CapLegendreSeries.odd, neg_sq]

theorem interiorD_even (a t z : ℝ) : interiorD a t (-z) = interiorD a t z := by
  simp [interiorD, oddD, neg_sq]

theorem negative_matching (a t : ℝ) : negative a t (-t) = interior a t (-t) := by
  rw [negative, neg_neg, interior_odd, value_matching]

theorem negative_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1+z)/2| < 1) :
    HasDerivAt (negative a t) (negativeD a t z) z := by
  have h := ((exterior_hasDerivAt a t (-z) ha (by simpa using hz)).comp
    (h := fun y : ℝ => -y) z ((hasDerivAt_id z).neg)).neg
  simpa [negative, negativeD, Function.comp_def] using h

theorem negativeD_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1+z)/2| < 1) :
    HasDerivAt (negativeD a t) (negativeDD a t z) z := by
  have h := (exteriorD_hasDerivAt a t (-z) ha (by simpa using hz)).comp
    (h := fun y : ℝ => -y) z ((hasDerivAt_id z).neg)
  simpa [negativeD, negativeDD, Function.comp_def] using h

theorem negative_legendre (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hz : |(1+z)/2| < 1) :
    (1-z^2)*negativeDD a t z - 2*z*negativeD a t z + a*negative a t z = 0 := by
  have h := exterior_legendre a t (-z) ha (by simpa using hz)
  dsimp only [negative, negativeD, negativeDD]
  linear_combination -h

theorem left_argument (t z : ℝ) (ht : 0 < t) (ht1 : t < 1) (hz : z ∈ Icc (-1 : ℝ) (-t)) :
    |(1+z)/2| < 1 := by rw [abs_of_nonneg (by linarith [hz.1])]; linarith [hz.2]

theorem middle_argument (t z : ℝ) (ht1 : t < 1) (hz : z ∈ Icc (-t) t) : |z| < 1 :=
  abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩

theorem right_argument (t z : ℝ) (ht : 0 < t) (ht1 : t < 1) (hz : z ∈ Icc t 1) :
    |(1-z)/2| < 1 := by rw [abs_of_nonneg (by linarith [hz.2])]; linarith [hz.1]

theorem profile_left (a t z : ℝ) (ht : 0 < t) (hz : z ∈ Icc (-1 : ℝ) (-t)) :
    profile a t z = negative a t z := by
  by_cases h : z < -t
  · simp [profile, h]
  · have he : z = -t := by linarith [hz.2]
    subst z
    simp only [profile, lt_self_iff_false, ite_false, neg_le_self ht.le, ite_true]
    exact (negative_matching a t).symm

theorem profile_middle (a t z : ℝ) (hz : z ∈ Icc (-t) t) : profile a t z = interior a t z := by
  simp [profile, not_lt.mpr hz.1, hz.2]

theorem profile_right (a t z : ℝ) (ht : 0 < t) (hz : z ∈ Icc t 1) :
    profile a t z = exterior a t z := by
  by_cases h : z ≤ t
  · have he : z = t := by linarith [hz.1]
    subst z
    rw [profile_middle a t t ⟨by linarith, le_rfl⟩, value_matching]
  · simp [profile, h, show ¬z < -t by linarith [hz.1]]

theorem profile_continuousOn (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ContinuousOn (profile a t) (Icc (-1 : ℝ) 1) := by
  have hL : ContinuousOn (profile a t) (Icc (-1 : ℝ) (-t)) :=
    (show ContinuousOn (negative a t) (Icc (-1 : ℝ) (-t)) from
      fun z hz => (negative_hasDerivAt a t z ha (left_argument t z ht ht1 hz)).continuousAt.continuousWithinAt).congr
      (fun z hz => profile_left a t z ht hz)
  have hM : ContinuousOn (profile a t) (Icc (-t) t) :=
    (show ContinuousOn (CapAngularShooting.interior a t) (Icc (-t) t) from
      fun z hz => (interior_hasDerivAt a t z ha (middle_argument t z ht1 hz)).continuousAt.continuousWithinAt).congr
      (fun z hz => profile_middle a t z hz)
  have hR : ContinuousOn (profile a t) (Icc t 1) :=
    (show ContinuousOn (exterior a t) (Icc t 1) from
      fun z hz => (exterior_hasDerivAt a t z ha (right_argument t z ht ht1 hz)).continuousAt.continuousWithinAt).congr
      (fun z hz => profile_right a t z ht hz)
  have he : Icc (-1 : ℝ) (-t) ∪ Icc (-t) t ∪ Icc t 1 = Icc (-1 : ℝ) 1 := by
    ext z
    simp only [mem_union, mem_Icc]
    constructor
    · rintro ((h|h)|h) <;> constructor <;> linarith [h.1,h.2]
    · intro hz
      by_cases h : z ≤ -t
      · exact Or.inl (Or.inl ⟨hz.1,h⟩)
      · by_cases h' : z ≤ t
        · exact Or.inl (Or.inr ⟨by linarith,h'⟩)
        · exact Or.inr ⟨by linarith,hz.2⟩
  rw [← he]
  exact ContinuousOn.union_isClosed (isClosed_Icc.union isClosed_Icc) isClosed_Icc
    (ContinuousOn.union_isClosed isClosed_Icc isClosed_Icc hL hM) hR

theorem profile_at_one (a t : ℝ) (ht : 0 < t) (ht1 : t < 1) : profile a t 1 = odd a t := by
  rw [profile_right a t 1 ht ⟨ht1.le,le_rfl⟩, exterior_at_one]

theorem profile_nonzero (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    0 < profile a t 1 := by rw [profile_at_one a t ht ht1]; exact odd_positive a t ha ht ht1

theorem legendre_ibp (f fD fDD v vD : ℝ → ℝ) (a A B : ℝ) (hAB : A ≤ B)
    (hf : ∀ z ∈ Icc A B, HasDerivAt f (fD z) z)
    (hD : ∀ z ∈ Icc A B, HasDerivAt fD (fDD z) z)
    (hode : ∀ z ∈ Icc A B, (1-z^2)*fDD z-2*z*fD z+a*f z=0)
    (hv : ∀ z : ℝ, HasDerivAt v (vD z) z) (hc : Continuous vD) :
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
    (fun z _ => (hv z).continuousAt.continuousWithinAt)
    (fun z hz => hd z (Ioo_subset_Icc_self (by simpa [min_eq_left hAB,max_eq_right hAB] using hz)))
    (fun z _ => hv z)
    (by simpa only [uIcc_of_le hAB] using (continuousOn_const.mul hfc).intervalIntegrable_of_Icc hAB)
    (hc.intervalIntegrable A B)
  dsimp only at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at h
  simpa only [mul_assoc, neg_mul, sub_neg_eq_add] using h

theorem integral_three (g L M R : ℝ → ℝ) (t : ℝ) (ht : 0 < t) (ht1 : t < 1)
    (hL : IntervalIntegrable L volume (-1) (-t))
    (hM : IntervalIntegrable M volume (-t) t)
    (hR : IntervalIntegrable R volume t 1)
    (heL : ∀ᵐ z : ℝ, z ∈ Ioc (-1 : ℝ) (-t) → g z = L z)
    (heM : ∀ᵐ z : ℝ, z ∈ Ioc (-t) t → g z = M z)
    (heR : ∀ᵐ z : ℝ, z ∈ Ioc t 1 → g z = R z) :
    (∫ z in (-1 : ℝ)..1, g z) = (∫ z in (-1 : ℝ)..(-t), L z) +
      (∫ z in (-t)..t, M z) + ∫ z in t..1, R z := by
  have h1 : (-1 : ℝ) ≤ -t := by linarith
  have h2 : -t ≤ t := by linarith
  have h3 : t ≤ (1 : ℝ) := ht1.le
  have eL : g =ᵐ[volume.restrict (uIoc (-1 : ℝ) (-t))] L := by
    change ∀ᵐ z ∂volume.restrict (uIoc (-1 : ℝ) (-t)), g z = L z
    rw [ae_restrict_iff' measurableSet_uIoc]
    simpa only [uIoc_of_le h1] using heL
  have eM : g =ᵐ[volume.restrict (uIoc (-t) t)] M := by
    change ∀ᵐ z ∂volume.restrict (uIoc (-t) t), g z = M z
    rw [ae_restrict_iff' measurableSet_uIoc]
    simpa only [uIoc_of_le h2] using heM
  have eR : g =ᵐ[volume.restrict (uIoc t 1)] R := by
    change ∀ᵐ z ∂volume.restrict (uIoc t 1), g z = R z
    rw [ae_restrict_iff' measurableSet_uIoc]
    simpa only [uIoc_of_le h3] using heR
  have iL := hL.congr eL.symm
  have iM := hM.congr eM.symm
  have iR := hR.congr eR.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (iL.trans iM) iR,
    ← intervalIntegral.integral_add_adjacent_intervals iL iM,
    intervalIntegral.integral_congr_ae_restrict eL,
    intervalIntegral.integral_congr_ae_restrict eM,
    intervalIntegral.integral_congr_ae_restrict eR]

theorem coefficient_left (d t z : ℝ) (hz : z < -t) (ht : 0 < t) : coefficient d t z = 1+d := by
  have hn : z < 0 := by linarith
  simp [coefficient, abs_of_neg hn, show ¬-z ≤ t by linarith]

theorem coefficient_middle (d t z : ℝ) (hz : z ∈ Icc (-t) t) : coefficient d t z = 1 := by
  simp [coefficient, abs_le.mpr hz]

theorem coefficient_right (d t z : ℝ) (hz : t < z) (ht : 0 < t) : coefficient d t z = 1+d := by
  simp [coefficient, abs_of_pos (lt_trans ht hz), not_le.mpr hz]

theorem weighted_weak_identity (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : determinant d t a = 0)
    (v vD : ℝ → ℝ) (hv : ∀ z : ℝ, HasDerivAt v (vD z) z) (hc : Continuous vD) :
    (∫ z in (-1 : ℝ)..1, coefficient d t z*((1-z^2)*slope a t z*vD z)) =
      a*∫ z in (-1 : ℝ)..1, coefficient d t z*(profile a t z*v z) := by
  have hL (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) (-t)) := negative_hasDerivAt a t z ha (left_argument t z ht ht1 hz)
  have hLD (z : ℝ) (hz : z ∈ Icc (-1 : ℝ) (-t)) := negativeD_hasDerivAt a t z ha (left_argument t z ht ht1 hz)
  have hM (z : ℝ) (hz : z ∈ Icc (-t) t) := interior_hasDerivAt a t z ha (middle_argument t z ht1 hz)
  have hMD (z : ℝ) (hz : z ∈ Icc (-t) t) := interiorD_hasDerivAt a t z ha (middle_argument t z ht1 hz)
  have hR (z : ℝ) (hz : z ∈ Icc t 1) := exterior_hasDerivAt a t z ha (right_argument t z ht ht1 hz)
  have hRD (z : ℝ) (hz : z ∈ Icc t 1) := exteriorD_hasDerivAt a t z ha (right_argument t z ht ht1 hz)
  have cv : Continuous v := continuous_iff_continuousAt.mpr (fun z => (hv z).continuousAt)
  have cL : ContinuousOn (negative a t) (Icc (-1 : ℝ) (-t)) := fun z hz => (hL z hz).continuousAt.continuousWithinAt
  have cLD : ContinuousOn (negativeD a t) (Icc (-1 : ℝ) (-t)) := fun z hz => (hLD z hz).continuousAt.continuousWithinAt
  have cM : ContinuousOn (CapAngularShooting.interior a t) (Icc (-t) t) := fun z hz => (hM z hz).continuousAt.continuousWithinAt
  have cMD : ContinuousOn (interiorD a t) (Icc (-t) t) := fun z hz => (hMD z hz).continuousAt.continuousWithinAt
  have cR : ContinuousOn (exterior a t) (Icc t 1) := fun z hz => (hR z hz).continuousAt.continuousWithinAt
  have cRD : ContinuousOn (exteriorD a t) (Icc t 1) := fun z hz => (hRD z hz).continuousAt.continuousWithinAt
  have eL : IntervalIntegrable (fun z => (1+d)*((1-z^2)*negativeD a t z*vD z)) volume (-1) (-t) :=
    ((continuousOn_const.mul (((continuous_const.sub (continuous_id.pow 2)).continuousOn.mul cLD).mul hc.continuousOn))).intervalIntegrable_of_Icc (by linarith)
  have eM : IntervalIntegrable (fun z => (1-z^2)*interiorD a t z*vD z) volume (-t) t :=
    (((continuous_const.sub (continuous_id.pow 2)).continuousOn.mul cMD).mul hc.continuousOn).intervalIntegrable_of_Icc (by linarith)
  have eR : IntervalIntegrable (fun z => (1+d)*((1-z^2)*exteriorD a t z*vD z)) volume t 1 :=
    ((continuousOn_const.mul (((continuous_const.sub (continuous_id.pow 2)).continuousOn.mul cRD).mul hc.continuousOn))).intervalIntegrable_of_Icc ht1.le
  have mL : IntervalIntegrable (fun z => (1+d)*(negative a t z*v z)) volume (-1) (-t) :=
    (continuousOn_const.mul (cL.mul cv.continuousOn)).intervalIntegrable_of_Icc (by linarith)
  have mM : IntervalIntegrable (fun z => CapAngularShooting.interior a t z*v z) volume (-t) t :=
    (cM.mul cv.continuousOn).intervalIntegrable_of_Icc (by linarith)
  have mR : IntervalIntegrable (fun z => (1+d)*(exterior a t z*v z)) volume t 1 :=
    (continuousOn_const.mul (cR.mul cv.continuousOn)).intervalIntegrable_of_Icc ht1.le
  have hne : ∀ᵐ z : ℝ, z ≠ -t := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  have splitE := integral_three (fun z => coefficient d t z*((1-z^2)*slope a t z*vD z))
    (fun z => (1+d)*((1-z^2)*negativeD a t z*vD z))
    (fun z => (1-z^2)*interiorD a t z*vD z)
    (fun z => (1+d)*((1-z^2)*exteriorD a t z*vD z)) t ht ht1 eL eM eR (by
      filter_upwards [hne] with z hzne
      intro hz
      have hzt : z < -t := lt_of_le_of_ne hz.2 hzne
      simp [coefficient_left d t z hzt ht, slope, hzt]) (by
      filter_upwards with z
      intro hz
      simp [coefficient_middle d t z ⟨hz.1.le,hz.2⟩, slope, not_lt.mpr hz.1.le, hz.2]) (by
      filter_upwards with z
      intro hz
      simp [coefficient_right d t z hz.1 ht, slope, not_le.mpr hz.1, show ¬z < -t by linarith [hz.1]])
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
  have iL := legendre_ibp _ _ _ v vD a (-1) (-t) (by linarith) hL hLD
    (fun z hz => negative_legendre a t z ha (left_argument t z ht ht1 hz)) hv hc
  have iM := legendre_ibp _ _ _ v vD a (-t) t (by linarith) hM hMD
    (fun z hz => interior_legendre a t z ha (middle_argument t z ht1 hz)) hv hc
  have iR := legendre_ibp _ _ _ v vD a t 1 ht1.le hR hRD
    (fun z hz => exterior_legendre a t z ha (right_argument t z ht ht1 hz)) hv hc
  rw [splitE, splitM]
  simp only [intervalIntegral.integral_const_mul]
  rw [iL,iM,iR]
  simp only [neg_sq, one_pow, sub_self, zero_mul, sub_zero, negativeD, neg_neg,
    interiorD_even, flux_matching d t a hroot]
  ring

theorem profile_odd (a t z : ℝ) (ht : 0 < t) : profile a t (-z) = -profile a t z := by
  have hpos (x : ℝ) (hx : 0 ≤ x) : profile a t (-x) = -profile a t x := by
    by_cases hxt : x ≤ t
    · rw [profile_middle a t x ⟨by linarith,hxt⟩,
        profile_middle a t (-x) ⟨by linarith,by linarith⟩, interior_odd]
    · have hxp : t < x := lt_of_not_ge hxt
      simp only [profile, negative, show -x < -t by linarith, ite_true,
        show ¬x < -t by linarith, ite_false, hxt, neg_neg]
  by_cases hz : 0 ≤ z
  · exact hpos z hz
  · have h := hpos (-z) (by linarith)
    rw [neg_neg] at h
    linarith

theorem profile_hasDerivAt (a t z : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (hz : z ∈ Ioo (-1 : ℝ) 1) (hl : z ≠ -t) (hr : z ≠ t) :
    HasDerivAt (profile a t) (slope a t z) z := by
  by_cases hL : z < -t
  · rw [slope, if_pos hL]
    apply (negative_hasDerivAt a t z ha (left_argument t z ht ht1 ⟨hz.1.le,hL.le⟩)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hL] with y hy
    change y < -t at hy
    simp [profile, hy]
  · have hzl : -t < z := lt_of_le_of_ne (le_of_not_gt hL) hl.symm
    by_cases hR : z ≤ t
    · have hzr : z < t := lt_of_le_of_ne hR hr
      simp only [slope, hL, ite_false, hR, ite_true]
      apply (interior_hasDerivAt a t z ha (middle_argument t z ht1 ⟨hzl.le,hR⟩)).congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds hzl hzr] with y hy
      simp [profile, not_lt.mpr hy.1.le, hy.2.le]
    · have hzr : t < z := lt_of_not_ge hR
      simp only [slope, hL, ite_false, hR]
      apply (exterior_hasDerivAt a t z ha (right_argument t z ht ht1 ⟨hzr.le,hz.2.le⟩)).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hzr] with y hy
      change t < y at hy
      simp [profile, not_le.mpr hy, show ¬y < -t by linarith]

theorem profile_hasDerivAt_ae (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ∀ᵐ z ∂volume.restrict (Ioo (-1 : ℝ) 1), HasDerivAt (profile a t) (slope a t z) z := by
  have hL : ∀ᵐ z : ℝ, z ≠ -t := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  have hR : ∀ᵐ z : ℝ, z ≠ t := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [ae_restrict_mem measurableSet_Ioo, ae_restrict_of_ae hL, ae_restrict_of_ae hR] with z hz hl hr
  exact profile_hasDerivAt a t z ha ht ht1 hz hl hr

def flux (a d t z : ℝ) : ℝ := coefficient d t z*((1-z^2)*slope a t z)

theorem flux_at_poles (a d t : ℝ) : flux a d t (-1) = 0 ∧ flux a d t 1 = 0 := by
  simp [flux]

theorem weighted_intervalIntegrable (f : ℝ → ℝ) (d t : ℝ)
    (hf : IntervalIntegrable f volume (-1) 1) :
    IntervalIntegrable (fun z => coefficient d t z*f z) volume (-1) 1 := by
  let S : Set ℝ := {z | t < |z|}
  have hS : MeasurableSet S := (isOpen_lt continuous_const continuous_abs).measurableSet
  have hi : IntervalIntegrable (S.indicator f) volume (-1) 1 :=
    ⟨hf.1.indicator hS, hf.2.indicator hS⟩
  have he : (fun z => coefficient d t z*f z) = fun z => f z+d*S.indicator f z := by
    funext z
    by_cases hz : |z| ≤ t
    · simp [coefficient, S, hz, not_lt.mpr hz]
    · simp only [coefficient, hz, ite_false, indicator_of_mem (show z ∈ S from lt_of_not_ge hz)]
      ring
  rw [he]
  exact hf.add (hi.const_mul d)

def mass (a d t : ℝ) : ℝ := ∫ z in (-1 : ℝ)..1, coefficient d t z*profile a t z^2

theorem mass_positive (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) : 0 < mass a d t := by
  have hcont := (profile_continuousOn a t ha ht ht1).pow 2
  have hi : IntervalIntegrable (fun z => profile a t z^2) volume (-1) 1 :=
    hcont.intervalIntegrable_of_Icc (by norm_num : (-1 : ℝ) ≤ 1)
  have hp : 0 < ∫ z in (-1 : ℝ)..1, profile a t z^2 :=
    intervalIntegral.integral_pos (by norm_num) hcont (fun _ _ => sq_nonneg _)
      ⟨1, by norm_num, sq_pos_of_pos (profile_nonzero a t ha ht ht1)⟩
  apply hp.trans_le
  apply intervalIntegral.integral_mono (by norm_num : (-1 : ℝ) ≤ 1) hi
    (weighted_intervalIntegrable _ d t hi)
  intro z
  by_cases hz : |z| ≤ t
  · simp [coefficient, hz]
  · simp only [coefficient, hz, ite_false]
    nlinarith [sq_nonneg (profile a t z)]

def normalized (a d t z : ℝ) : ℝ := profile a t z / Real.sqrt (mass a d t)
def normalizedSlope (a d t z : ℝ) : ℝ := slope a t z / Real.sqrt (mass a d t)

theorem normalized_mass (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (hd : 0 ≤ d)
    (ht : 0 < t) (ht1 : t < 1) :
    (∫ z in (-1 : ℝ)..1, coefficient d t z*normalized a d t z^2) = 1 := by
  have hp := mass_positive a d t ha hd ht ht1
  have he : (fun z => coefficient d t z*normalized a d t z^2) =
      fun z => (coefficient d t z*profile a t z^2)/mass a d t := by
    funext z
    rw [normalized, div_pow, Real.sq_sqrt hp.le, mul_div_assoc]
  rw [he, intervalIntegral.integral_div]
  exact div_self hp.ne'

theorem normalized_weak_identity (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : determinant d t a = 0)
    (v vD : ℝ → ℝ) (hv : ∀ z : ℝ, HasDerivAt v (vD z) z) (hc : Continuous vD) :
    (∫ z in (-1 : ℝ)..1, coefficient d t z*((1-z^2)*normalizedSlope a d t z*vD z)) =
      a*∫ z in (-1 : ℝ)..1, coefficient d t z*(normalized a d t z*v z) := by
  have he : (fun z => coefficient d t z*((1-z^2)*normalizedSlope a d t z*vD z)) =
      fun z => (coefficient d t z*((1-z^2)*slope a t z*vD z))/Real.sqrt (mass a d t) := by
    funext z
    unfold normalizedSlope
    ring
  have hm : (fun z => coefficient d t z*(normalized a d t z*v z)) =
      fun z => (coefficient d t z*(profile a t z*v z))/Real.sqrt (mass a d t) := by
    funext z
    unfold normalized
    ring
  rw [he,hm,intervalIntegral.integral_div,intervalIntegral.integral_div,
    weighted_weak_identity a d t ha ht ht1 hroot v vD hv hc]
  ring

theorem exists_normalized_weak_profile (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ a ∈ Ioo (0 : ℝ) 2, exponent a ∈ Ioo (0 : ℝ) 1 ∧
      (∫ z in (-1 : ℝ)..1, coefficient d t z*normalized a d t z^2) = 1 ∧
      ∀ v vD : ℝ → ℝ, (∀ z, HasDerivAt v (vD z) z) → Continuous vD →
        (∫ z in (-1 : ℝ)..1, coefficient d t z*((1-z^2)*normalizedSlope a d t z*vD z)) =
          a*∫ z in (-1 : ℝ)..1, coefficient d t z*(normalized a d t z*v z) := by
  obtain ⟨a, ha, hr⟩ := exists_root d t hd ht ht1
  refine ⟨a,ha,exponent_range a ha,normalized_mass a d t ⟨ha.1.le,ha.2.le⟩ hd.le ht ht1,?_⟩
  intro v vD hv hc
  exact normalized_weak_identity a d t ⟨ha.1.le,ha.2.le⟩ ht ht1 hr v vD hv hc

end OQ14.CapSturmLiouville

#print axioms OQ14.CapSturmLiouville.interior_odd
#print axioms OQ14.CapSturmLiouville.interiorD_even
#print axioms OQ14.CapSturmLiouville.negative_matching
#print axioms OQ14.CapSturmLiouville.negative_hasDerivAt
#print axioms OQ14.CapSturmLiouville.negativeD_hasDerivAt
#print axioms OQ14.CapSturmLiouville.negative_legendre
#print axioms OQ14.CapSturmLiouville.left_argument
#print axioms OQ14.CapSturmLiouville.middle_argument
#print axioms OQ14.CapSturmLiouville.right_argument
#print axioms OQ14.CapSturmLiouville.profile_left
#print axioms OQ14.CapSturmLiouville.profile_middle
#print axioms OQ14.CapSturmLiouville.profile_right
#print axioms OQ14.CapSturmLiouville.profile_continuousOn
#print axioms OQ14.CapSturmLiouville.profile_at_one
#print axioms OQ14.CapSturmLiouville.profile_nonzero
#print axioms OQ14.CapSturmLiouville.legendre_ibp
#print axioms OQ14.CapSturmLiouville.integral_three
#print axioms OQ14.CapSturmLiouville.coefficient_left
#print axioms OQ14.CapSturmLiouville.coefficient_middle
#print axioms OQ14.CapSturmLiouville.coefficient_right
#print axioms OQ14.CapSturmLiouville.weighted_weak_identity
#print axioms OQ14.CapSturmLiouville.profile_odd
#print axioms OQ14.CapSturmLiouville.profile_hasDerivAt
#print axioms OQ14.CapSturmLiouville.profile_hasDerivAt_ae
#print axioms OQ14.CapSturmLiouville.flux_at_poles
#print axioms OQ14.CapSturmLiouville.weighted_intervalIntegrable
#print axioms OQ14.CapSturmLiouville.mass_positive
#print axioms OQ14.CapSturmLiouville.normalized_mass
#print axioms OQ14.CapSturmLiouville.normalized_weak_identity
#print axioms OQ14.CapSturmLiouville.exists_normalized_weak_profile
