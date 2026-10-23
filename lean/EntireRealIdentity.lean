import EntireExponentialPackets
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecificLimits.Basic

/-! Actual real-interval uniqueness for entire functions and finite exponential packets. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.EntireRealIdentity
open Set Filter EntireExponentialPackets
open scoped Topology

theorem zero_of_real_interval (f : Entire) (δ : ℝ) (hδ : 0 < δ)
    (hz : ∀ t : ℝ, -δ < t → t < δ → (f : ℂ → ℂ) t=0) : ∀ z : ℂ, (f : ℂ → ℂ) z=0 := by
  have hf : ContDiff ℂ (⊤ : ℕ∞) (f : ℂ → ℂ) := f.property
  have ha : AnalyticOnNhd ℂ (f : ℂ → ℂ) univ :=
    fun z _ => (hf.differentiable (by simp)).analyticAt z
  have hlim : Tendsto (fun n : ℕ => δ/((n : ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlimC : Tendsto (fun n : ℕ => ((δ/((n : ℝ)+2) : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hlim
  have hcl : (0 : ℂ) ∈ closure ({z : ℂ | (f : ℂ → ℂ) z=0}\{0}) := by
    apply mem_closure_of_tendsto hlimC
    filter_upwards with n
    have hden : 0 < (n : ℝ)+2 := by positivity
    have hp : 0 < δ/((n : ℝ)+2) := div_pos hδ hden
    have hu : δ/((n : ℝ)+2) < δ := (div_lt_iff₀ hden).mpr (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; nlinarith)
    exact ⟨hz _ (by linarith) hu,by simpa only [mem_singleton_iff] using Complex.ofReal_ne_zero.mpr (ne_of_gt hp)⟩
  have he := ha.eqOn_zero_of_preconnected_of_mem_closure isPreconnected_univ (mem_univ (0 : ℂ)) hcl
  exact fun z => he (mem_univ z)

theorem distinct_packets_on_interval {ι : Type*} [Fintype ι] (ζ a b c : ι → ℂ)
    (hζ : Function.Injective ζ) (δ : ℝ) (hδ : 0 < δ)
    (hz : ∀ t : ℝ, -δ < t → t < δ →
      ∑ i, (a i+b i*(t : ℂ)+c i*(t : ℂ)^2)*Complex.exp (ζ i*(t : ℂ))=0) :
    ∀ i, a i=0 ∧ b i=0 ∧ c i=0 := by
  let f : Entire := ∑ i, packet (ζ i) (a i) (b i) (c i)
  have he : ∀ z : ℂ, (f : ℂ → ℂ) z=∑ i, (a i+b i*z+c i*z^2)*Complex.exp (ζ i*z) := by
    intro z
    simp only [f,Submodule.coe_sum,Finset.sum_apply,packet]
  apply distinct_packets ζ a b c hζ
  have hall := zero_of_real_interval f δ hδ (fun t hl hu => (he t).trans (hz t hl hu))
  exact fun z => (he z).symm.trans (hall z)

end OQ14.EntireRealIdentity
#print axioms OQ14.EntireRealIdentity.zero_of_real_interval
#print axioms OQ14.EntireRealIdentity.distinct_packets_on_interval
