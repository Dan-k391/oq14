import ModalTMIsolation
import ModalSphereVolumePoles
import ModalVolumeNormalization

/-! One fixed algebraic contrast below any positive bound, with isolated high-Q TM poles. -/
noncomputable section
set_option autoImplicit false

namespace OQ14.ModalBoundedContrastIsolation
open Complex OQ14.ModalAlgebra OQ14.ModalMatching OQ14.ComplexConvolutionAnalytic
open scoped Topology

/-- Algebraic indices are available below every strictly positive contrast bound. -/
theorem exists_index (B : ℝ) (hB : 0 < B) :
    ∃ n : ℝ, 1 < n ∧ IsAlgebraic ℚ (n : ℂ) ∧ n ^ 2 - 1 < B := by
  let d : ℝ := min B 1 / 4
  have hd : 0 < d := div_pos (lt_min hB (by norm_num)) (by norm_num)
  have hdB : 4 * d ≤ B := by dsimp [d]; linarith [min_le_left B 1]
  have hd1 : d ≤ 1 / 4 := by dsimp [d]; linarith [min_le_right B 1]
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (1 : ℝ) < 1 + d by linarith)
  refine ⟨(q : ℝ), hq1, ?_, ?_⟩
  · simpa only [Complex.ofReal_ratCast] using (isAlgebraic_rat ℚ (A := ℂ) q)
  · have hqpos : 0 < (q : ℝ) := by linarith
    have hqsmall : (q : ℝ) < 2 := by linarith
    nlinarith [mul_pos (sub_pos.mpr hq2) (show (0 : ℝ) < (q : ℝ) + 1 by linarith)]

/-- The same actual sphere mode has all-degree isolated matching and unit reciprocal pairing. -/
theorem normalized_isolated_poles (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ k : ModalShell.Frequency, ∃ f : Amplitudes, ∃ a : ℂ,
      L < k.val.re ∧ k.val.im < 0 ∧ Q < k.val.re / (-2 * k.val.im) ∧
      (∀ j : ℕ, tmDet j (n : ℂ) k.val = 0 ↔ j = 1) ∧
      deriv (tmDet 1 (n : ℂ)) k.val ≠ 0 ∧
      a • ModalWeightedMode.weightedMode n hn k f ≠ 0 ∧
      volumeBlock (ModalWeightedMode.coefficient n hn) k.val 1
        (a • ModalWeightedMode.weightedMode n hn k f) = 0 ∧
      ComplexVolumeReciprocity.pairFunctional (a • ModalWeightedMode.weightedMode n hn k f)
        (deriv (fun z => volumeBlock (ModalWeightedMode.coefficient n hn) z 1) k.val
          (a • ModalWeightedMode.weightedMode n hn k f)) = 1 ∧
      (∃ hm : MeromorphicAt
        (fun z => Ring.inverse (volumeBlock (ModalWeightedMode.coefficient n hn) z 1)) k.val,
        hm.order < 0) := by
  obtain ⟨k, _, hL, hi, hQk, hd, hs, _, _, hmer, _⟩ :=
    ModalSphereVolumePoles.high_quality_volume_poles n hn L Q hQ
  obtain ⟨f, a, _, hu, hker, _, _, hunit⟩ :=
    ModalVolumeNormalization.exists_normalized_weighted_mode n hn k hd hs
  have hn0 : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hn1 : (n : ℂ) ≠ 1 := by exact_mod_cast (show n ≠ 1 by linarith)
  have hnm : (n : ℂ) ≠ -1 := by exact_mod_cast (show n ≠ -1 by linarith)
  have hiso := ModalTMIsolation.isolated_degree 1 (n : ℂ) k.val hna hn0 hn1 hnm k.property hd
  exact ⟨k, f, a, hL, hi, hQk, hiso.2, hiso.1, hu, hker, hunit, hmer⟩

end OQ14.ModalBoundedContrastIsolation

#print axioms OQ14.ModalBoundedContrastIsolation.exists_index
#print axioms OQ14.ModalBoundedContrastIsolation.normalized_isolated_poles
