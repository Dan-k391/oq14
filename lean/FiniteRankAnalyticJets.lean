import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.FiniteRankAnalyticJets

open Filter
open scoped Topology

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]

omit [CompleteSpace E] in
theorem range_comp_finite (A : W →L[ℂ] E) (B : E →L[ℂ] W) :
    FiniteDimensional ℂ (LinearMap.range (A.comp B)) := by
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A)
  exact LinearMap.range_comp_le_range B.toLinearMap A.toLinearMap

omit [CompleteSpace E] in
theorem range_add_finite (A B : E →L[ℂ] E)
    (hA : FiniteDimensional ℂ (LinearMap.range A))
    (hB : FiniteDimensional ℂ (LinearMap.range B)) :
    FiniteDimensional ℂ (LinearMap.range (A+B)) := by
  letI := hA
  letI := hB
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range A ⊔ LinearMap.range B)
  rintro y ⟨x, rfl⟩
  exact (LinearMap.range A ⊔ LinearMap.range B).add_mem
    (Submodule.mem_sup_left (show A x ∈ LinearMap.range A from ⟨x,rfl⟩))
    (Submodule.mem_sup_right (show B x ∈ LinearMap.range B from ⟨x,rfl⟩))

omit [CompleteSpace E] [FiniteDimensional ℂ W] in
theorem comp_analyticAt (A : ℂ → W →L[ℂ] E) (B : ℂ → E →L[ℂ] W) (z₀ : ℂ)
    (hA : AnalyticAt ℂ A z₀) (hB : AnalyticAt ℂ B z₀) :
    AnalyticAt ℂ (fun z => (A z).comp (B z)) z₀ :=
  ((ContinuousLinearMap.compL ℂ E W E).analyticAt_bilinear (A z₀, B z₀)).comp
    (f := fun z : ℂ => (A z, B z)) (hA.prod hB)

/-- Every actual Taylor jet of an analytic product through a fixed
finite-dimensional space has finite-dimensional range. -/
theorem iteratedDeriv_comp_finite (n : ℕ) (A : ℂ → W →L[ℂ] E) (B : ℂ → E →L[ℂ] W)
    (z₀ : ℂ) (hA : AnalyticAt ℂ A z₀) (hB : AnalyticAt ℂ B z₀) :
    FiniteDimensional ℂ (LinearMap.range (iteratedDeriv n (fun z => (A z).comp (B z)) z₀)) := by
  letI : CompleteSpace W := FiniteDimensional.complete ℂ W
  induction n generalizing A B with
  | zero => exact range_comp_finite (A z₀) (B z₀)
  | succ n ih =>
    have hprod : deriv (fun z => (A z).comp (B z)) =ᶠ[𝓝 z₀]
        (fun z => (deriv A z).comp (B z) + (A z).comp (deriv B z)) := by
      filter_upwards [hA.eventually_analyticAt, hB.eventually_analyticAt] with z ha hb
      exact (ha.differentiableAt.hasDerivAt.clm_comp hb.differentiableAt.hasDerivAt).deriv
    have hj := hprod.iteratedDeriv_eq n
    rw [iteratedDeriv_succ', hj]
    have ha := comp_analyticAt (deriv A) B z₀ hA.deriv hB
    have hb := comp_analyticAt A (deriv B) z₀ hA hB.deriv
    rw [show (fun z => (deriv A z).comp (B z) + (A z).comp (deriv B z)) =
      (fun z => (deriv A z).comp (B z)) + (fun z => (A z).comp (deriv B z)) from rfl,
      iteratedDeriv_add ha.contDiffAt hb.contDiffAt]
    exact range_add_finite _ _ (ih (deriv A) B hA.deriv hB) (ih A (deriv B) hA hB.deriv)

theorem coefficient_eq_iteratedDeriv (f : ℂ → E →L[ℂ] E)
    (p : FormalMultilinearSeries ℂ ℂ (E →L[ℂ] E)) (z₀ : ℂ)
    (hp : HasFPowerSeriesAt f p z₀) (n : ℕ) :
    p.coeff n = ((n.factorial : ℂ)⁻¹) • iteratedDeriv n f z₀ := by
  obtain ⟨r, hr⟩ := hp
  have hh := hr.factorial_smul (1 : ℂ) n
  change n.factorial • p.coeff n = iteratedDeriv n f z₀ at hh
  have hc : (n.factorial : ℂ) • p.coeff n = iteratedDeriv n f z₀ := by
    simpa only [Nat.cast_smul_eq_nsmul] using hh
  rw [← hc, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast Nat.factorial_ne_zero n

theorem coefficient_comp_finite (A : ℂ → W →L[ℂ] E) (B : ℂ → E →L[ℂ] W)
    (z₀ : ℂ) (hA : AnalyticAt ℂ A z₀) (hB : AnalyticAt ℂ B z₀)
    (p : FormalMultilinearSeries ℂ ℂ (E →L[ℂ] E))
    (hp : HasFPowerSeriesAt (fun z => (A z).comp (B z)) p z₀) (n : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (p.coeff n)) := by
  rw [coefficient_eq_iteratedDeriv _ p z₀ hp n]
  let J := iteratedDeriv n (fun z => (A z).comp (B z)) z₀
  letI : FiniteDimensional ℂ (LinearMap.range J) := iteratedDeriv_comp_finite n A B z₀ hA hB
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range J)
  rintro y ⟨x, rfl⟩
  exact (LinearMap.range J).smul_mem _ (show J x ∈ LinearMap.range J from ⟨x, rfl⟩)

end OQ14.FiniteRankAnalyticJets

#print axioms OQ14.FiniteRankAnalyticJets.range_comp_finite
#print axioms OQ14.FiniteRankAnalyticJets.range_add_finite
#print axioms OQ14.FiniteRankAnalyticJets.comp_analyticAt
#print axioms OQ14.FiniteRankAnalyticJets.iteratedDeriv_comp_finite
#print axioms OQ14.FiniteRankAnalyticJets.coefficient_eq_iteratedDeriv
#print axioms OQ14.FiniteRankAnalyticJets.coefficient_comp_finite
