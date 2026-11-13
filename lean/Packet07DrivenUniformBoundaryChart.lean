import Packet07DrivenUniformBoundary

/-! Retain the actual material-side identity when constructing boundary mode branches. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet07DrivenUniformBoundaryChart
open MeasureTheory Metric Set Filter Maxwell Packet05ChartBasis Packet05GraphChartMap
  Packet05PhysicalGraphChart Packet05ActualFlatNeighborhood Packet05ActualOrientedGraph
open scoped Topology

theorem actual_boundary_chart
    {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {contrast threshold : ℝ}
    (setup : Packet07PlanarSetup.Setup N Pset contrast threshold) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius contrast setup.enclosing) (j0 : ℕ)
    (body : Set Space) (x : Space) (hx : x ∈ frontier body)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ body ↔ 0 < F y))
    (host : ℂ) (hhost : host ≠ 0) (d : ℝ) (hd : 0 ≤ d)
    (outer : ContDiffBump (0 : Space)) (hxouter : x ∈ ball (0 : Space) outer.rIn)
    (hmaterial : ∀ᶠ y in 𝓝 x, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0) y =
      host * (by classical exact if y ∈ body then (1+d : ℂ) else 1)) :
    let E := setup.electric k j0 input
    ∃ (up : Bool) (axis : Fin 3) (g : ConicalSmoothJunction.Plane → ℝ) (T : Set Space)
      (lower upper : Fin 3 → Space → ℂ),
      ContDiff ℝ 4 g ∧ HasCompactSupport g ∧ IsOpen T ∧
      chartPoint up axis g x ∈ T ∧ chartPoint up axis g x 2 = 0 ∧
      (∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight g) y) ∈ body ↔ 0 < y 2) ∧
      (∀ j, Continuous (lower j)) ∧ (∀ j, Continuous (upper j)) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict
        (Packet05PhysicalChartBranches.physicalFlatMap up axis g ⁻¹' (T ∩ {y | y 2 < 0}))] lower j) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict
        (Packet05PhysicalChartBranches.physicalFlatMap up axis g ⁻¹' (T ∩ {y | 0 < y 2}))] upper j) := by
  classical
  dsimp only
  obtain ⟨up,axis,g,hg,hgc,hzero,hside⟩ := actual_oriented_graph body x hx hcert
  have hΩexists : ∃ Ω : Set Space, IsOpen Ω ∧ x ∈ Ω ∧
      (∀ y ∈ Ω, y ∈ ball (0 : Space) outer.rIn) ∧
      (∀ y ∈ Ω, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0) y =
        host * (if y ∈ body then (1+d : ℂ) else 1)) := by
    have hn : ball (0 : Space) outer.rIn ∩ {y | Packet06MaxwellScalarEquation.epsilon (setup.rounded j0) y =
        host * (if y ∈ body then (1+d : ℂ) else 1)} ∈ 𝓝 x :=
      inter_mem (isOpen_ball.mem_nhds hxouter) hmaterial
    obtain ⟨Ω,hsub,hopen,hxΩ⟩ := _root_.mem_nhds_iff.mp hn
    exact ⟨Ω,hopen,hxΩ,fun y hy => (hsub hy).1,fun y hy => (hsub hy).2⟩
  obtain ⟨Ω,hΩ,hxΩ,hΩball,hΩmat⟩ := hΩexists
  obtain ⟨r,hr,hpzero,hflat⟩ := actual_flat_neighborhood body Ω x hΩ hxΩ up axis g hg hzero hside
  let p := chartPoint up axis g x
  let W : Set Space := ball p r
  let V : Set Space := {y | inverseOriented up axis y ∈ ball (0 : Space) outer.rIn}
  obtain ⟨T,lower,upper,hT,hpT,hTW,hl,hu,hle,hue⟩ :=
    Packet07DrivenUniformOpenChart.open_driven_chart setup k hk0 input hk j0 body host hhost d hd
      outer up axis g hg hgc V W isOpen_ball p (mem_ball_self hr)
      (fun y hy => hy) (fun y hy => hΩball _ (hflat y hy).1)
      (fun y hy => (hflat y hy).2) (fun y hy => hΩmat _ (hflat y hy).1)
  exact ⟨up,axis,g,T,lower,upper,hg,hgc,hT,hpT,hpzero,(fun y hy => (hflat y (hTW hy)).2),hl,hu,hle,hue⟩

end OQ14.Packet07DrivenUniformBoundaryChart
#print axioms OQ14.Packet07DrivenUniformBoundaryChart.actual_boundary_chart
