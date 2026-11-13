import MaxwellCutoffCommutator

/-! Explicit L² bounds for differentiated curl-cutoff source terms. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.MaxwellCurlCutoffSource
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator

theorem quotient_sub (u v : L2Scalar) (i : Fin 3) (h : ℝ) :
    quotient (u-v) i h = quotient u i h - quotient v i h := by
  apply Lp.ext
  have hshift := (measurePreserving_add_right (volume : Measure Space) (h • basis i)).quasiMeasurePreserving.ae
    (Lp.coeFn_sub u v)
  filter_upwards [quotient_ae (u-v) i h, quotient_ae u i h, quotient_ae v i h,
    Lp.coeFn_sub u v, hshift, Lp.coeFn_sub (quotient u i h) (quotient v i h)] with x hab ha hb hs ht hq
  rw [hq]
  simp only [Pi.sub_apply]
  rw [hab,ha,hb,hs,ht]
  simp only [Pi.sub_apply]
  ring

def source (χ : Test) (hχ : ContDiff ℝ 2 χ.function) (W : L2Vector) (j : Fin 3) : L2Scalar :=
  scaleL2 (derivativeCutoff χ hχ (next j)).function
      (derivativeCutoff χ hχ (next j)).regular.continuous (derivativeCutoff χ hχ (next j)).compact (W (previous j)) -
    scaleL2 (derivativeCutoff χ hχ (previous j)).function
      (derivativeCutoff χ hχ (previous j)).regular.continuous (derivativeCutoff χ hχ (previous j)).compact (W (next j))

theorem source_ae (χ : Test) (hχ : ContDiff ℝ 2 χ.function) (W : L2Vector) (j : Fin 3) :
    (fun x => source χ hχ W j x) =ᵐ[volume]
      fun x => dcoord χ.function x (next j) * W (previous j) x -
        dcoord χ.function x (previous j) * W (next j) x := by
  filter_upwards [Lp.coeFn_sub
    (scaleL2 (derivativeCutoff χ hχ (next j)).function _ _ (W (previous j)))
    (scaleL2 (derivativeCutoff χ hχ (previous j)).function _ _ (W (next j))),
    scaleL2_ae (derivativeCutoff χ hχ (next j)).function _ _ (W (previous j)),
    scaleL2_ae (derivativeCutoff χ hχ (previous j)).function _ _ (W (next j))] with x hs ha hb
  change ((scaleL2 _ _ _ (W (previous j)) - scaleL2 _ _ _ (W (next j)) : L2Scalar) : Space → ℂ) x = _
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ha,hb]
  rfl

theorem quotient_source_bound (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (W : L2Vector) (i j : Fin 3) (h : ℝ) (hh : h ≠ 0) (A B : ℝ)
    (hA : ∀ l x, ‖dcoord χ.function x l‖ ≤ A)
    (hB : ∀ l m x, ‖dcoord (fun y => dcoord χ.function y l) x m‖ ≤ B) :
    ‖quotient (source χ hχ W j) i h‖ ≤
      A * (‖quotient (W (previous j)) i h‖ + ‖quotient (W (next j)) i h‖) +
        3*B*(‖W (previous j)‖ + ‖W (next j)‖) := by
  unfold source
  rw [quotient_sub]
  have hp := cutoff_quotient_norm (derivativeCutoff χ hχ (next j)) (W (previous j)) i h hh A B
    (hA (next j)) (hB (next j))
  have hn := cutoff_quotient_norm (derivativeCutoff χ hχ (previous j)) (W (next j)) i h hh A B
    (hA (previous j)) (hB (previous j))
  calc
    _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add hp hn
    _ = _ := by ring

theorem flat_weight_norm (d : ℝ) (hd : 0 ≤ d) (x : Space) :
    ‖MaxwellWeakTranslation.flatWeight d x‖ ≤ 1 := by
  unfold MaxwellWeakTranslation.flatWeight
  split_ifs
  · simp
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact (inv_le_one₀ (by linarith)).2 (by linarith)

theorem flat_quotient_weight_bound (W C : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (i j : Fin 3) (hi : i ≠ 2) (h : ℝ)
    (hWC : ∀ l, (fun x => W l x) =ᵐ[volume] fun x => MaxwellWeakTranslation.flatWeight d x * C l x) :
    ‖quotient (W j) i h‖ ≤ ‖quotient (C j) i h‖ := by
  have he := MaxwellWeakTranslation.quotient_commutes_invariant_weight W C
    (MaxwellWeakTranslation.flatWeight d) i h (MaxwellWeakTranslation.flatWeight_tangential d i hi h) hWC j
  have hn : ‖quotient (W j) i h‖ ≤ 1*‖quotient (C j) i h‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [he] with x hx
    change quotient (W j) i h x = _ at hx
    rw [hx, norm_mul]
    exact mul_le_mul_of_nonneg_right (flat_weight_norm d hd x) (norm_nonneg _)
  simpa using hn

theorem flat_quotient_source_bound (χ : Test) (hχ : ContDiff ℝ 2 χ.function)
    (W C : L2Vector) (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (hi : i ≠ 2)
    (h : ℝ) (hh : h ≠ 0) (A B : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ l x, ‖dcoord χ.function x l‖ ≤ A)
    (hB : ∀ l m x, ‖dcoord (fun y => dcoord χ.function y l) x m‖ ≤ B)
    (hWC : ∀ l, (fun x => W l x) =ᵐ[volume] fun x => MaxwellWeakTranslation.flatWeight d x * C l x) :
    ‖quotient (source χ hχ W j) i h‖ ≤
      A * (‖quotient (C (previous j)) i h‖ + ‖quotient (C (next j)) i h‖) +
        3*B*(‖W (previous j)‖ + ‖W (next j)‖) := by
  have hs := quotient_source_bound χ hχ W i j h hh A B hA hB
  have hprev := flat_quotient_weight_bound W C d hd i (previous j) hi h hWC
  have hnext := flat_quotient_weight_bound W C d hd i (next j) hi h hWC
  exact hs.trans (add_le_add_right (mul_le_mul_of_nonneg_left (add_le_add hprev hnext) hA0) _)

end OQ14.MaxwellCurlCutoffSource
#print axioms OQ14.MaxwellCurlCutoffSource.source_ae
#print axioms OQ14.MaxwellCurlCutoffSource.quotient_source_bound
#print axioms OQ14.MaxwellCurlCutoffSource.flat_quotient_weight_bound
#print axioms OQ14.MaxwellCurlCutoffSource.flat_quotient_source_bound
