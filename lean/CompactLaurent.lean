import AnalyticCompactInverse
import FiniteRankAnalyticJets

/-! # A convergent Laurent correction with actual finite-rank coefficients

The finite-dimensional Schur inverse supplies a pole-clearing power. Its
analytic Woodbury numerator factors through that fixed finite-dimensional
space. Actual Taylor coefficients are finite rank by the proved jet theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.CompactLaurent

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem finite_rank_laurent (T : ℂ → H →L[ℂ] H) (hT : Differentiable ℂ T)
    (hc : ∀ z : ℂ, IsCompactOperator (T z)) (hunit : ∃ z : ℂ, IsUnit (1-T z)) (z₀ : ℂ) :
    ∃ (n : ℕ) (G : ℂ → H →L[ℂ] H) (p : FormalMultilinearSeries ℂ ℂ (H →L[ℂ] H)),
      AnalyticAt ℂ G z₀ ∧
      (∀ j : ℕ, FiniteDimensional ℂ (LinearMap.range (p.coeff j))) ∧
      ∀ᶠ z in 𝓝[≠] z₀,
        HasSum (fun j : ℕ => ((z-z₀)^n)⁻¹ • ((z-z₀)^j • p.coeff j))
          (Ring.inverse (1-T z) - G z) := by
  obtain ⟨W, hW, B, hz₀, hregular⟩ := LocalFredholmReduction.exists_local_factor T hT z₀ (hc z₀)
  letI : FiniteDimensional ℂ W := hW
  letI : CompleteSpace W := FiniteDimensional.complete ℂ W
  let I : W →L[ℂ] H := W.subtypeL
  let A := LocalFredholmReduction.regularPart T (I.comp B)
  let D := LocalFredholmReduction.reduced T I B
  let G : ℂ → H →L[ℂ] H := fun z => Ring.inverse (A z)
  have hG : AnalyticAt ℂ G z₀ :=
    LocalFredholmReduction.regularInverse_analyticAt T hT (I.comp B) z₀ hz₀
  obtain ⟨n, hC⟩ := FiniteMeromorphicInverse.inverse_meromorphicAt D z₀
    (LocalFredholmReduction.reduced_analyticAt T hT I B z₀ hz₀)
  let C : ℂ → W →L[ℂ] W := fun z => (z-z₀)^n • Ring.inverse (D z)
  let U : ℂ → W →L[ℂ] H := fun z => (G z).comp I
  let V : ℂ → H →L[ℂ] W := fun z => B.comp (G z)
  let Q : ℂ → H →L[ℂ] W := fun z => (C z).comp (V z)
  have hU : AnalyticAt ℂ U z₀ :=
    (((ContinuousLinearMap.compL ℂ W H H).flip I).analyticAt (G z₀)).comp (f := G) hG
  have hV : AnalyticAt ℂ V z₀ :=
    ((ContinuousLinearMap.compL ℂ H H W B).analyticAt (G z₀)).comp (f := G) hG
  have hQ : AnalyticAt ℂ Q z₀ :=
    ((ContinuousLinearMap.compL ℂ H W W).analyticAt_bilinear (C z₀, V z₀)).comp
      (f := fun z : ℂ => (C z, V z)) (hC.prod hV)
  have hS := FiniteRankAnalyticJets.comp_analyticAt U Q z₀ hU hQ
  obtain ⟨p, hp⟩ := hS
  refine ⟨n, G, p, hG, fun j => FiniteRankAnalyticJets.coefficient_comp_finite U Q z₀ hU hQ p hp j, ?_⟩
  have hseries := hasFPowerSeriesAt_iff'.mp hp
  filter_upwards [nhdsWithin_le_nhds hseries, nhdsWithin_le_nhds hregular,
    LocalFredholmReduction.anchored_punctured_isUnit T hT hc hunit z₀,
    self_mem_nhdsWithin] with z hs hz hu hne
  have hn : (z-z₀)^n ≠ 0 := pow_ne_zero n (sub_ne_zero.mpr hne)
  have hw := LocalFredholmReduction.inverse_woodbury T I B z hz
    ((LocalFredholmReduction.isUnit_iff_reduced T I B z hz).mp hu)
  have hwood : Ring.inverse (1-T z) = G z + (U z).comp ((Ring.inverse (D z)).comp (V z)) := by
    simpa only [FiniteRankSchur.woodbury, G, U, V, A, D, ContinuousLinearMap.comp_assoc] using hw
  have hclear : ((z-z₀)^n)⁻¹ • (U z).comp (Q z) =
      (U z).comp ((Ring.inverse (D z)).comp (V z)) := by
    simp only [Q, C, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hsum := hs.const_smul (((z-z₀)^n)⁻¹)
  convert hsum using 1
  rw [hclear, hwood]
  abel

end OQ14.CompactLaurent

#print axioms OQ14.CompactLaurent.finite_rank_laurent
