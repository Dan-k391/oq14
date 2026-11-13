import Packet05ChartMaterialPhases
import Packet07DrivenUniformBoundaryChart
import Packet05BoundaryMaterialMode

/-! Actual regular material boundaries have one-sided continuous mode fields
on literal material phases, with every chart and localization chosen. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformBoundaryMaterial
open MeasureTheory Set Metric Filter Maxwell Packet05BoundaryMaterialMode
open scoped Topology

theorem boundary_material_driven
    {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {contrast threshold : ℝ}
    (setup : Packet07PlanarSetup.Setup N Pset contrast threshold) (k : ℝ) (hk0 : k ≠ 0)
    (input : ComplexTransverseExpansion.ModeIndex →₀ ℂ)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius contrast setup.enclosing) (j0 : ℕ)
    (body : Set Space) (x : Space) (hx : x ∈ frontier body)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ body ↔ 0 < F y))
    (host : ℂ) (hhost : host ≠ 0) (d : ℝ) (hd : 0 ≤ d)
    (hmaterial : ∀ᶠ y in 𝓝 x, Packet06MaxwellScalarEquation.epsilon (setup.rounded j0) y=
      host*(by classical exact if y ∈ body then (1+d : ℂ) else 1)) :
    HasPhaseRepresentatives
      (setup.electric k j0 input) body x := by
  let χ : ContDiffBump (0 : Space) := ⟨‖x‖+1,‖x‖+2,by positivity,by linarith⟩
  have hxχ : x ∈ ball (0 : Space) χ.rIn := by
    simp only [mem_ball,dist_zero_right]
    change ‖x‖ < ‖x‖+1
    linarith
  obtain ⟨up,axis,g,T,lower,upper,hg,hgc,hT,hxT,hzero,hside,hl,hu,hle,hue⟩ :=
    Packet07DrivenUniformBoundaryChart.actual_boundary_chart setup k hk0 input hk j0
      body x hx hcert host hhost d hd χ hxχ hmaterial
  obtain ⟨V,hV,hxV,hu',hl',hinside,houtside⟩ :=
    Packet05ChartMaterialPhases.actual_material_phases body up axis g (hg.of_le (by decide)) T hT x
      hxT hside _ lower upper hl hu hle hue
  exact ⟨V,upper,lower,hV,hxV,hu',hl',hinside,houtside⟩

end OQ14.Packet07DrivenUniformBoundaryMaterial
#print axioms OQ14.Packet07DrivenUniformBoundaryMaterial.boundary_material_driven
