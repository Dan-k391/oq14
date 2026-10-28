import MaxwellDifferenceQuotient

/-! Literal translations of weak L² curls and their difference quotients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaxwellWeakTranslation
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting

def shifted (φ : Test) (a : Space) : Test := shiftedTest (shiftedTest φ 0) a

theorem shifted_value (φ : Test) (a x : Space) : (shifted φ a).function x = φ.function (x-a) := by
  simp only [shifted, shiftedTest]
  congr 1
  abel

theorem shifted_partial (φ : Test) (a x : Space) (i : Fin 3) :
    dcoord (shifted φ a).function x i = dcoord φ.function (x-a) i := by
  rw [shifted, shiftedTest_partial, shiftedTest_partial]
  have he : (0 : Space) - (a-x) = x-a := by abel
  rw [he, neg_neg]

theorem translated_integral (u : L2Scalar) (g : Space → ℂ) (a : Space) :
    (∫ x, translateL2 u a x * g x) = ∫ x, u x * g (x-a) := by
  calc
    _ = ∫ x, u (x+a)*g x := by
      apply integral_congr_ae
      filter_upwards [translateL2_ae u a] with x hx
      rw [hx]
    _ = _ := by
      simpa only [add_sub_cancel_right] using
        integral_add_right_eq_self (fun x => u x * g (x-a)) a

def translateVector (E : L2Vector) (a : Space) : L2Vector := fun j => translateL2 (E j) a

theorem translate_weakCurl (E C : L2Vector) (h : HasWeakCurl E C) (a : Space) :
    HasWeakCurl (translateVector E a) (translateVector C a) := by
  apply (hasWeakCurl_iff_integral _ _).mpr
  intro φ j
  have ht := (hasWeakCurl_iff_integral E C).mp h (shifted φ a) j
  simp only [shifted_value, shifted_partial] at ht
  simpa only [translateVector, translated_integral] using ht

def quotientVector (E : L2Vector) (i : Fin 3) (h : ℝ) : L2Vector :=
  fun j => MaxwellDifferenceQuotient.quotient (E j) i h

theorem quotient_weakCurl (E C : L2Vector) (hcurl : HasWeakCurl E C) (i : Fin 3) (h : ℝ) :
    HasWeakCurl (quotientVector E i h) (quotientVector C i h) := by
  have ht : (translateVector E (h • basis i), translateVector C (h • basis i)) ∈ WeakCurl.graph :=
    translate_weakCurl E C hcurl (h • basis i)
  have hc : (E,C) ∈ WeakCurl.graph := hcurl
  have hd := WeakCurl.graph.sub_mem ht hc
  have hs := WeakCurl.graph.smul_mem ((h : ℂ)⁻¹) hd
  change HasWeakCurl (quotientVector E i h) (quotientVector C i h) at hs
  exact hs

theorem quotient_commutes_invariant_weight (W C : L2Vector) (w : Space → ℂ)
    (i : Fin 3) (h : ℝ) (hweight : ∀ x, w (x + h • basis i) = w x)
    (hWC : ∀ j, (fun x => W j x) =ᵐ[volume] fun x => w x * C j x) :
    ∀ j, (fun x => quotientVector W i h j x) =ᵐ[volume]
      fun x => w x * quotientVector C i h j x := by
  intro j
  have ht := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae (hWC j)
  have hwq := Lp.coeFn_smul ((h : ℂ)⁻¹) (translateL2 (W j) (h • basis i) - W j)
  have hcq := Lp.coeFn_smul ((h : ℂ)⁻¹) (translateL2 (C j) (h • basis i) - C j)
  filter_upwards [hWC j, ht, translateL2_ae (W j) (h • basis i), translateL2_ae (C j) (h • basis i),
    Lp.coeFn_sub (translateL2 (W j) (h • basis i)) (W j),
    Lp.coeFn_sub (translateL2 (C j) (h • basis i)) (C j), hwq, hcq] with x hw htw hwtrans hctrans hwsub hcsub hwsm hcsm
  change (((h : ℂ)⁻¹ • (translateL2 (W j) (h • basis i) - W j) : L2Scalar) : Space → ℂ) x =
    w x * (((h : ℂ)⁻¹ • (translateL2 (C j) (h • basis i) - C j) : L2Scalar) : Space → ℂ) x
  rw [hwsm,hcsm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hwsub,hcsub]
  simp only [Pi.sub_apply]
  rw [hwtrans,hctrans,htw,hw,hweight]
  ring

def flatWeight (d : ℝ) (x : Space) : ℂ :=
  if x 2 < 0 then 1 else ((1+d)⁻¹ : ℝ)

theorem flatWeight_tangential (d : ℝ) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (x : Space) :
    flatWeight d (x + h • basis i) = flatWeight d x := by
  fin_cases i <;> simp [flatWeight, basis, EuclideanSpace.single_apply] at hi ⊢

theorem flat_curlcurl_quotient (H C W : L2Vector) (d k : ℝ)
    (hcurl : HasWeakCurl W ((k^2 : ℂ) • H))
    (hWC : ∀ j, (fun x => W j x) =ᵐ[volume] fun x => flatWeight d x * C j x)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) :
    HasWeakCurl (quotientVector W i h) (quotientVector ((k^2 : ℂ) • H) i h) ∧
      ∀ j, (fun x => quotientVector W i h j x) =ᵐ[volume]
        fun x => flatWeight d x * quotientVector C i h j x :=
  ⟨quotient_weakCurl W _ hcurl i h,
    quotient_commutes_invariant_weight W C (flatWeight d) i h (flatWeight_tangential d i hi h) hWC⟩

end OQ14.MaxwellWeakTranslation
#print axioms OQ14.MaxwellWeakTranslation.translate_weakCurl
#print axioms OQ14.MaxwellWeakTranslation.quotient_weakCurl
#print axioms OQ14.MaxwellWeakTranslation.quotient_commutes_invariant_weight
#print axioms OQ14.MaxwellWeakTranslation.flat_curlcurl_quotient
