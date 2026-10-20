import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.MeromorphicOperator

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedAddCommGroup G] [NormedSpace ℂ G]

theorem map (L : E →L[ℂ] F) (f : ℂ → E) (z₀ : ℂ) (hf : MeromorphicAt f z₀) :
    MeromorphicAt (fun z => L (f z)) z₀ := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have hh := (L.analyticAt ((z₀-z₀)^n • f z₀)).comp
    (f := fun z : ℂ => (z-z₀)^n • f z) hn
  simpa only [Function.comp_def, map_smul] using hh

theorem clm_comp (f : ℂ → F →L[ℂ] G) (g : ℂ → E →L[ℂ] F) (z₀ : ℂ)
    (hf : MeromorphicAt f z₀) (hg : MeromorphicAt g z₀) :
    MeromorphicAt (fun z => (f z).comp (g z)) z₀ := by
  obtain ⟨m, hm⟩ := hf
  obtain ⟨n, hn⟩ := hg
  refine ⟨m+n, ?_⟩
  have hc := (ContinuousLinearMap.compL ℂ E F G).analyticAt_bilinear
    ((z₀-z₀)^m • f z₀, (z₀-z₀)^n • g z₀)
  have hh := hc.comp (f := fun z : ℂ => ((z-z₀)^m • f z, (z-z₀)^n • g z)) (hm.prod hn)
  convert hh using 1
  funext z
  simp [pow_add, ContinuousLinearMap.compL_apply, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul, smul_smul, mul_comm]

end OQ14.MeromorphicOperator

#print axioms OQ14.MeromorphicOperator.map
#print axioms OQ14.MeromorphicOperator.clm_comp
