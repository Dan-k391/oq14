import LocalFredholmReduction
import FiniteMeromorphicInverse
import MeromorphicOperator

/-! # Genuine meromorphic inverse of an anchored analytic compact pencil

Local finite-dimensional reduction and the actual Woodbury identity transfer
the finite-dimensional meromorphic inverse to the original Hilbert operator.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.AnalyticCompactInverse

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem inverse_meromorphicAt (T : ℂ → H →L[ℂ] H) (hT : Differentiable ℂ T)
    (hc : ∀ z : ℂ, IsCompactOperator (T z)) (hunit : ∃ z : ℂ, IsUnit (1-T z)) (z₀ : ℂ) :
    MeromorphicAt (fun z => Ring.inverse (1-T z)) z₀ := by
  obtain ⟨W, hW, B, hz₀, hU⟩ := LocalFredholmReduction.exists_local_factor T hT z₀ (hc z₀)
  letI : FiniteDimensional ℂ W := hW
  letI : CompleteSpace W := FiniteDimensional.complete ℂ W
  let I : W →L[ℂ] H := W.subtypeL
  let A : ℂ → H →L[ℂ] H := LocalFredholmReduction.regularPart T (I.comp B)
  let D : ℂ → W →L[ℂ] W := LocalFredholmReduction.reduced T I B
  have hA : MeromorphicAt (fun z => Ring.inverse (A z)) z₀ :=
    (LocalFredholmReduction.regularInverse_analyticAt T hT (I.comp B) z₀ hz₀).meromorphicAt
  have hD : MeromorphicAt (fun z => Ring.inverse (D z)) z₀ :=
    FiniteMeromorphicInverse.inverse_meromorphicAt D z₀
      (LocalFredholmReduction.reduced_analyticAt T hT I B z₀ hz₀)
  have hBA := MeromorphicOperator.clm_comp (fun _ : ℂ => B)
    (fun z => Ring.inverse (A z)) z₀ (MeromorphicAt.const B z₀) hA
  have hDBA := MeromorphicOperator.clm_comp (fun z => Ring.inverse (D z))
    (fun z => B.comp (Ring.inverse (A z))) z₀ hD hBA
  have hIDBA := MeromorphicOperator.clm_comp (fun _ : ℂ => I)
    (fun z => (Ring.inverse (D z)).comp (B.comp (Ring.inverse (A z)))) z₀
      (MeromorphicAt.const I z₀) hDBA
  have hAIDBA := MeromorphicOperator.clm_comp (fun z => Ring.inverse (A z))
    (fun z => I.comp ((Ring.inverse (D z)).comp (B.comp (Ring.inverse (A z))))) z₀ hA hIDBA
  apply (hA.add' hAIDBA).congr
  filter_upwards [LocalFredholmReduction.anchored_punctured_isUnit T hT hc hunit z₀,
    nhdsWithin_le_nhds hU] with z hu hz
  change FiniteRankSchur.woodbury (A z) I B = Ring.inverse (1-T z)
  exact (LocalFredholmReduction.inverse_woodbury T I B z hz
    ((LocalFredholmReduction.isUnit_iff_reduced T I B z hz).mp hu)).symm

theorem inverse_meromorphicOn (T : ℂ → H →L[ℂ] H) (hT : Differentiable ℂ T)
    (hc : ∀ z : ℂ, IsCompactOperator (T z)) (hunit : ∃ z : ℂ, IsUnit (1-T z)) :
    MeromorphicOn (fun z => Ring.inverse (1-T z)) Set.univ :=
  fun z _ => inverse_meromorphicAt T hT hc hunit z

end OQ14.AnalyticCompactInverse

#print axioms OQ14.AnalyticCompactInverse.inverse_meromorphicAt
#print axioms OQ14.AnalyticCompactInverse.inverse_meromorphicOn
