import Packet07DrivenUniformPhaseBranches
import Packet05NestedCutoffSupport
import Packet05ChartMetricData

/-! Every open compact-C4 material graph chart supplies all cutoff, metric and
bounded-slope inputs for actual mode phase continuity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet07DrivenUniformOpenChart
open MeasureTheory Metric Set Maxwell WeakCurl WeakConservation
  Packet05NestedChartCutoffs Packet05NestedCutoffSupport
  Packet05ChartBasis Packet05GraphChartMap Packet05PhysicalGraphChart
  Packet05GraphSlopeMultiplier Packet07DrivenUniformPhaseBranches
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := ConicalSmoothJunction.Plane

theorem open_driven_chart
    {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {contrast threshold : ℝ}
    (setup : Packet07PlanarSetup.Setup N Pset contrast threshold) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius contrast setup.enclosing) (j0 : ℕ)
    (body : Set Space) (host : ℂ) (hhost : host ≠ 0) (d : ℝ) (hd : 0 ≤ d)
    (outer : ContDiffBump (0 : Space)) (up : Bool) (axis : Fin 3)
    (g : Plane → ℝ) (hg : ContDiff ℝ 4 g) (hgcompact : HasCompactSupport g)
    (Vchart Wgraph : Set Space) (hWopen : IsOpen Wgraph) (p : Space) (hp : p ∈ Wgraph)
    (hmapV : ∀ x ∈ Vchart, inverseOriented up axis x ∈ ball (0 : Space) outer.rIn)
    (hmapW : ∀ x ∈ Wgraph, graphMap (liftedHeight g) x ∈ Vchart)
    (hside : ∀ x ∈ Wgraph, inverseOriented up axis (graphMap (liftedHeight g) x) ∈ body ↔ 0 < x 2)
    (hmaterial : ∀ x ∈ Wgraph, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0)
      (inverseOriented up axis (graphMap (liftedHeight g) x)) =
        host * (by classical exact if inverseOriented up axis (graphMap (liftedHeight g) x) ∈ body
          then (1+d : ℂ) else 1)) :
    let E := setup.electric k j0 input
    ∃ (T : Set Space) (lower upper : Fin 3 → Space → ℂ),
      IsOpen T ∧ p ∈ T ∧ T ⊆ Wgraph ∧
      (∀ j, Continuous (lower j)) ∧ (∀ j, Continuous (upper j)) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict
        (Packet05PhysicalChartBranches.physicalFlatMap up axis g ⁻¹' (T ∩ {x | x 2 < 0}))] lower j) ∧
      (∀ j, (fun x => E x j) =ᵐ[volume.restrict
        (Packet05PhysicalChartBranches.physicalFlatMap up axis g ⁻¹' (T ∩ {x | 0 < x 2}))] upper j) := by
  classical
  dsimp only
  obtain ⟨R,hR,hRW⟩ := Metric.isOpen_iff.mp hWopen p hp
  let Ω : Set Space := ball p R
  have hpΩ : p ∈ Ω := mem_ball_self hR
  obtain ⟨q₀⟩ := exists_nested Ω isOpen_ball p hpΩ
  let S₀ : Set Space := ball p (8*q₀.r)
  let V : Set Space := ball p (4*q₀.r)
  let S : Set Space := ball p (2*q₀.r)
  obtain ⟨q₁⟩ := exists_nested S isOpen_ball p (mem_ball_self (by linarith [q₀.positive]))
  let V₁ : Set Space := ball p (4*q₁.r)
  let S₁ : Set Space := ball p (2*q₁.r)
  obtain ⟨q₂⟩ := exists_nested S₁ isOpen_ball p (mem_ball_self (by linarith [q₁.positive]))
  let W₁ : Set Space := ball p (4*q₂.r)
  obtain ⟨q₃⟩ := exists_nested W₁ isOpen_ball p (mem_ball_self (by linarith [q₂.positive]))
  let V₂ : Set Space := ball p (8*q₃.r)
  let U₂ : Set Space := ball p (4*q₃.r)
  let T : Set Space := ball p (2*q₃.r)
  have hSΩ : S ⊆ Ω := small_ball_subset q₀ 2 (by norm_num)
  have hV₁S : V₁ ⊆ S := small_ball_subset q₁ 4 (by norm_num)
  have hS₁V₁ : S₁ ⊆ V₁ := ball_subset_ball (by linarith [q₁.positive])
  have hW₁S₁ : W₁ ⊆ S₁ := small_ball_subset q₂ 4 (by norm_num)
  have hW₁V₁ : W₁ ⊆ V₁ := hW₁S₁.trans hS₁V₁
  have hV₂W₁ : V₂ ⊆ W₁ := ball8_subset q₃
  have hU₂V₂ : U₂ ⊆ V₂ := ball_subset_ball (by linarith [q₃.positive])
  have hTU₂ : T ⊆ U₂ := ball_subset_ball (by linarith [q₃.positive])
  have hTS : T ⊆ S := hTU₂.trans (hU₂V₂.trans (hV₂W₁.trans (hW₁V₁.trans hV₁S)))
  have hTΩ : T ⊆ Ω := hTS.trans hSΩ
  have hm₀ : tsupport q₀.middle.function ⊆ Ω := middle_support q₀
  have hm₁ : tsupport q₁.middle.function ⊆ Ω := (middle_support q₁).trans hSΩ
  have hm₂ : tsupport q₂.middle.function ⊆ Ω := (middle_support q₂).trans (hS₁V₁.trans (hV₁S.trans hSΩ))
  obtain ⟨A,a,b,M,B,hA3,hAg,ha0,hb0,hM0,ha,hb,hM,hB⟩ :=
    Packet05ChartMetricData.actual_metric_data g hg hgcompact p R hR.le
  have hAΩ : ∀ x ∈ Ω, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ) :=
    fun x hx => hAg x (ball_subset_closedBall hx)
  obtain ⟨⟨B3,hB3⟩,hdi,hdd⟩ := Packet05GraphSlopeBounds.slope_bounds g (hg.of_le (by decide)) hgcompact
  obtain ⟨C₀,hC₀,hD₀⟩ := q₀.derivative_bound
  obtain ⟨C₁,hC₁,hD₁⟩ := q₁.derivative_bound
  obtain ⟨C₂,hC₂,hD₂⟩ := q₂.derivative_bound
  have hbranches := actual_driven_phase_branches setup k hk0 input hk j0 body host hhost d hd
    outer up axis g (hg.of_le (by decide)) (hg.of_le (by decide)) Vchart Ω hmapV
    (fun x hx => hmapW x (hRW hx)) (fun x hx => hside x (hRW hx))
    (fun x hx => hmaterial x (hRW hx)) B3 hB3 hdi hdd A
    (fun j k => (hA3 j k).of_le (by decide)) hA3 hAΩ
    Ω S₀ V S (Subset.refl _) q₀.outer.complexTest.toTest
    (by simpa only [complex_support] using q₀.outer_support) q₀.outer_one
    q₀.middle q₀.middle_one q₀.r q₀.positive
    (fun t _ h hh x hx => q₀.shifted_support t h hh x hx)
    b hb M hM B hB (fun x hx => hAΩ x (hm₀ hx)) a 1 C₀ ha
    (fun x => (q₀.value_bound x).2.1) (fun j x => (hD₀ j x).2.1)
    q₀.inner (q₀.regular 2).2.2 (q₀.regular 3).2.2 q₀.inner_support q₀.inner_middle q₀.inner_one
    V₁ S₁ W₁ V₂ U₂ T isOpen_ball isOpen_ball hW₁V₁ hV₁S isOpen_ball isOpen_ball
    hV₂W₁ hU₂V₂ hTU₂ hTS q₁.middle (q₁.regular 2).2.1 q₁.middle_one q₁.r q₁.positive
    (fun h hh x hx => ⟨ball8_subset q₁ (q₁.shifted_support 0 h hh x hx).1,
      ball8_subset q₁ (q₁.shifted_support 0 h hh x hx).2⟩)
    (fun h hh x hx => ⟨ball8_subset q₁ (q₁.shifted_support 1 h hh x hx).1,
      ball8_subset q₁ (q₁.shifted_support 1 h hh x hx).2⟩)
    q₁.inner (q₁.regular 2).2.2 q₁.inner_middle q₁.inner_one q₂.middle q₂.r q₂.positive
    (fun h hh x hx => ⟨ball8_subset q₂ (q₂.shifted_support 0 h hh x hx).1,
      ball8_subset q₂ (q₂.shifted_support 0 h hh x hx).2⟩)
    (fun h hh x hx => ⟨ball8_subset q₂ (q₂.shifted_support 1 h hh x hx).1,
      ball8_subset q₂ (q₂.shifted_support 1 h hh x hx).2⟩)
    (fun x hx => (q₁.inner_one x (hW₁S₁ hx)).eq_of_nhds) q₂.middle_one
    (fun x hx => hAΩ x (hm₁ hx)) (fun x hx => hAΩ x (hm₂ hx))
    1 C₁ 1 C₂ (fun x => (q₁.value_bound x).2.1) (fun j x => (hD₁ j x).2.1)
    (fun x => (q₂.value_bound x).2.1) (fun j x => (hD₂ j x).2.1)
    q₃.outer.complexTest.toTest q₃.middle.complexTest.toTest q₃.inner.complexTest.toTest
    (complex_regular q₃.outer 2 (q₃.regular 2).1)
    (by simpa only [complex_support] using q₃.outer_support)
    (fun x hx => (q₃.outer_one x hx).eq_of_nhds)
    (by
      rw [complex_support]
      exact fun x hx => (q₃.shifted_support 0 0 (by simpa using q₃.positive) x hx).1)
    (fun x hx => real_one_complex q₃.middle (q₃.middle_one x hx))
    (by simpa only [complex_support] using q₃.inner_middle)
    (complex_regular q₃.inner 2 (q₃.regular 2).2.2)
    (fun x hx => real_one_complex q₃.inner (q₃.inner_one x hx).eq_of_nhds) hTΩ
  obtain ⟨lower,upper,hl,hu,hle,hue⟩ := hbranches
  exact ⟨T,lower,upper,isOpen_ball,mem_ball_self (by linarith [q₃.positive]),hTΩ.trans hRW,hl,hu,hle,hue⟩

end OQ14.Packet07DrivenUniformOpenChart
#print axioms OQ14.Packet07DrivenUniformOpenChart.open_driven_chart
