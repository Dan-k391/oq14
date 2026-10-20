import HilbertFiniteRank
import FiniteRankSchur
import FiniteDimensionalDeterminant
import LocalDichotomy
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # The analytic regular factor in a local finite-dimensional reduction

The finite-rank approximation is fixed at the center. Its complement has
norm less than one nearby, giving an actual analytic inverse regular factor.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace OQ14.LocalFredholmReduction

open Metric
open scoped Topology

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

def regularPart (T : ℂ → E →L[ℂ] E) (F : E →L[ℂ] E) (z : ℂ) : E →L[ℂ] E :=
  1 - (T z - F)

def regularSet (T : ℂ → E →L[ℂ] E) (F : E →L[ℂ] E) : Set ℂ :=
  {z | ‖T z - F‖ < 1}

def reduced (T : ℂ → E →L[ℂ] E) (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ) :
    V →L[ℂ] V :=
  1 - B.comp ((Ring.inverse (regularPart T (I.comp B) z)).comp I)

omit [CompleteSpace E] in
theorem regularPart_differentiable (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (F : E →L[ℂ] E) :
    Differentiable ℂ (regularPart T F) :=
  (differentiable_const (1 : E →L[ℂ] E)).sub (hT.sub (differentiable_const F))

omit [CompleteSpace E] in
theorem regularSet_isOpen (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (F : E →L[ℂ] E) : IsOpen (regularSet T F) :=
  isOpen_lt ((hT.continuous.sub continuous_const).norm) continuous_const

theorem regularPart_isUnit (T : ℂ → E →L[ℂ] E) (F : E →L[ℂ] E) (z : ℂ)
    (hz : z ∈ regularSet T F) : IsUnit (regularPart T F z) :=
  isUnit_one_sub_of_norm_lt_one hz

theorem regularInverse_analyticAt (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (F : E →L[ℂ] E) (z : ℂ)
    (hz : z ∈ regularSet T F) :
    AnalyticAt ℂ (fun w => Ring.inverse (regularPart T F w)) z :=
  (analyticOnNhd_inverse (𝕜 := ℂ) _ (regularPart_isUnit T F z hz)).comp
    ((regularPart_differentiable T hT F).analyticAt z)

omit [CompleteSpace E] in
theorem regularPart_sub_finiteRank (T : ℂ → E →L[ℂ] E)
    (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ) :
    regularPart T (I.comp B) z - I.comp B = 1 - T z := by
  unfold regularPart
  abel

theorem reduced_differentiableOn (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (I : V →L[ℂ] E) (B : E →L[ℂ] V) :
    DifferentiableOn ℂ (reduced T I B) (regularSet T (I.comp B)) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_const (1 : V →L[ℂ] V)).sub
    ((differentiableAt_const B).clm_comp
      ((regularInverse_analyticAt T hT (I.comp B) z hz).differentiableAt.clm_comp
        (differentiableAt_const I)))

theorem reduced_analyticAt [CompleteSpace V] (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ)
    (hz : z ∈ regularSet T (I.comp B)) : AnalyticAt ℂ (reduced T I B) z :=
  (reduced_differentiableOn T hT I B).analyticAt
    ((regularSet_isOpen T hT (I.comp B)).mem_nhds hz)

theorem exists_local_factor {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : ℂ → H →L[ℂ] H) (hT : Differentiable ℂ T) (z₀ : ℂ)
    (hc : IsCompactOperator (T z₀)) :
    ∃ (W : Submodule ℂ H), ∃ _ : FiniteDimensional ℂ W, ∃ B : H →L[ℂ] W,
      z₀ ∈ regularSet T (W.subtypeL.comp B) ∧
      regularSet T (W.subtypeL.comp B) ∈ 𝓝 z₀ := by
  obtain ⟨W, hW, B, hB⟩ := HilbertFiniteRank.factor_approx (T z₀) hc (1/2) (by norm_num)
  have hz : z₀ ∈ regularSet T (W.subtypeL.comp B) := lt_trans hB (by norm_num)
  exact ⟨W, hW, B, hz, (regularSet_isOpen T hT _).mem_nhds hz⟩

theorem isUnit_iff_reduced (T : ℂ → E →L[ℂ] E)
    (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ)
    (hz : z ∈ regularSet T (I.comp B)) :
    IsUnit (1 - T z) ↔ IsUnit (reduced T I B z) := by
  rw [← regularPart_sub_finiteRank T I B z]
  exact FiniteRankSchur.isUnit_iff_schur _ (regularPart_isUnit T _ z hz) I B

theorem inverse_woodbury (T : ℂ → E →L[ℂ] E)
    (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ)
    (hz : z ∈ regularSet T (I.comp B)) (hD : IsUnit (reduced T I B z)) :
    Ring.inverse (1 - T z) = FiniteRankSchur.woodbury (regularPart T (I.comp B) z) I B := by
  rw [← regularPart_sub_finiteRank T I B z]
  exact FiniteRankSchur.inverse_woodbury _ (regularPart_isUnit T _ z hz) I B hD

theorem determinant_analyticAt [FiniteDimensional ℂ V] (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ)
    (hz : z ∈ regularSet T (I.comp B)) :
    AnalyticAt ℂ (fun w => FiniteDimensionalDeterminant.determinant (reduced T I B w)) z := by
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  exact FiniteDimensionalDeterminant.determinant_analyticAt _ z (reduced_analyticAt T hT I B z hz)

theorem isUnit_iff_determinant_ne_zero [FiniteDimensional ℂ V] (T : ℂ → E →L[ℂ] E)
    (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z : ℂ)
    (hz : z ∈ regularSet T (I.comp B)) :
    IsUnit (1-T z) ↔ FiniteDimensionalDeterminant.determinant (reduced T I B z) ≠ 0 :=
  (isUnit_iff_reduced T I B z hz).trans
    (FiniteDimensionalDeterminant.isUnit_iff_determinant_ne_zero _)

theorem local_dichotomy [FiniteDimensional ℂ V] (T : ℂ → E →L[ℂ] E)
    (hT : Differentiable ℂ T) (I : V →L[ℂ] E) (B : E →L[ℂ] V) (z₀ : ℂ)
    (hz₀ : z₀ ∈ regularSet T (I.comp B)) :
    (∀ᶠ z in 𝓝 z₀, ¬ IsUnit (1-T z)) ∨ ∀ᶠ z in 𝓝[≠] z₀, IsUnit (1-T z) := by
  have hU := (regularSet_isOpen T hT (I.comp B)).mem_nhds hz₀
  rcases (determinant_analyticAt T hT I B z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with
    hzero | hnonzero
  · left
    filter_upwards [hU, hzero] with z hz hd
    exact fun hu => (isUnit_iff_determinant_ne_zero T I B z hz).mp hu hd
  · right
    filter_upwards [nhdsWithin_le_nhds hU, hnonzero] with z hz hd
    exact (isUnit_iff_determinant_ne_zero T I B z hz).mpr hd

theorem compact_local_dichotomy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : ℂ → H →L[ℂ] H) (hT : Differentiable ℂ T) (z₀ : ℂ)
    (hc : IsCompactOperator (T z₀)) :
    (∀ᶠ z in 𝓝 z₀, ¬ IsUnit (1-T z)) ∨ ∀ᶠ z in 𝓝[≠] z₀, IsUnit (1-T z) := by
  obtain ⟨W, hW, B, hz, _⟩ := exists_local_factor T hT z₀ hc
  letI : FiniteDimensional ℂ W := hW
  exact local_dichotomy T hT W.subtypeL B z₀ hz

theorem anchored_punctured_isUnit {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : ℂ → H →L[ℂ] H) (hT : Differentiable ℂ T)
    (hc : ∀ z : ℂ, IsCompactOperator (T z)) (hunit : ∃ z : ℂ, IsUnit (1-T z)) (z₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₀, IsUnit (1-T z) :=
  LocalDichotomy.punctured_of_nonempty {z | IsUnit (1-T z)} hunit
    (fun z => compact_local_dichotomy T hT z (hc z)) z₀

omit [CompleteSpace E] in
theorem exceptional_isClosed (T : ℂ → E →L[ℂ] E) [CompleteSpace E]
    (hT : Differentiable ℂ T) : IsClosed {z : ℂ | ¬ IsUnit (1-T z)} := by
  exact (Units.isOpen.preimage (continuous_const.sub hT.continuous)).isClosed_compl

end OQ14.LocalFredholmReduction

#print axioms OQ14.LocalFredholmReduction.regularPart_differentiable
#print axioms OQ14.LocalFredholmReduction.regularSet_isOpen
#print axioms OQ14.LocalFredholmReduction.regularPart_isUnit
#print axioms OQ14.LocalFredholmReduction.regularInverse_analyticAt
#print axioms OQ14.LocalFredholmReduction.regularPart_sub_finiteRank
#print axioms OQ14.LocalFredholmReduction.reduced_differentiableOn
#print axioms OQ14.LocalFredholmReduction.reduced_analyticAt
#print axioms OQ14.LocalFredholmReduction.exists_local_factor
#print axioms OQ14.LocalFredholmReduction.isUnit_iff_reduced
#print axioms OQ14.LocalFredholmReduction.inverse_woodbury
#print axioms OQ14.LocalFredholmReduction.determinant_analyticAt
#print axioms OQ14.LocalFredholmReduction.isUnit_iff_determinant_ne_zero
#print axioms OQ14.LocalFredholmReduction.local_dichotomy
#print axioms OQ14.LocalFredholmReduction.compact_local_dichotomy
#print axioms OQ14.LocalFredholmReduction.anchored_punctured_isUnit
#print axioms OQ14.LocalFredholmReduction.exceptional_isClosed
