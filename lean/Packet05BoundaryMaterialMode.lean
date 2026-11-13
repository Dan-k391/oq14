import Packet05ChartMaterialPhases

/-! Actual regular material boundaries have one-sided continuous mode fields
on literal material phases, with every chart and localization chosen. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05BoundaryMaterialMode
open MeasureTheory Set Metric Filter Maxwell
open scoped Topology

def HasPhaseRepresentatives (E : Field) (body : Set Space) (x : Space) : Prop :=
  ∃ (V : Set Space) (inside outside : Fin 3 → Space → ℂ), IsOpen V ∧ x ∈ V ∧
    (∀ j, Continuous (inside j)) ∧ (∀ j, Continuous (outside j)) ∧
    (∀ j, (fun y => E y j) =ᵐ[volume.restrict (V ∩ body)] inside j) ∧
    (∀ j, (fun y => E y j) =ᵐ[volume.restrict (V ∩ bodyᶜ)] outside j)

theorem boundary_material_mode
    (c : StaticCoefficient.Coefficient) (z : ℂ) (hz : z ≠ 0) (Rsource : ℝ)
    (mode : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 Rsource → c.value (VectorFourier.coordinateMap x)=0)
    (hmode : ComplexConvolutionAnalytic.volumeBlock c z Rsource mode=0)
    (body : Set Space) (x : Space) (hx : x ∈ frontier body)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ body ↔ 0 < F y))
    (host : ℂ) (hhost : host ≠ 0) (d : ℝ) (hd : 0 ≤ d)
    (hmaterial : ∀ᶠ y in 𝓝 x, Packet06MaxwellScalarEquation.epsilon c y=
      host*(by classical exact if y ∈ body then (1+d : ℂ) else 1)) :
    HasPhaseRepresentatives
      (Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c mode) (DynamicVolume.source c mode)) body x := by
  let χ : ContDiffBump (0 : Space) := ⟨‖x‖+1,‖x‖+2,by positivity,by linarith⟩
  have hxχ : x ∈ ball (0 : Space) χ.rIn := by
    simp only [mem_ball,dist_zero_right]
    change ‖x‖ < ‖x‖+1
    linarith
  obtain ⟨up,axis,g,T,lower,upper,hg,hgc,hT,hxT,hzero,hside,hl,hu,hle,hue⟩ :=
    Packet05BoundaryPhaseChart.actual_boundary_chart c z hz Rsource mode hc hmode
      body x hx hcert host hhost d hd χ hxχ hmaterial
  obtain ⟨V,hV,hxV,hu',hl',hinside,houtside⟩ :=
    Packet05ChartMaterialPhases.actual_material_phases body up axis g (hg.of_le (by decide)) T hT x
      hxT hside _ lower upper hl hu hle hue
  exact ⟨V,upper,lower,hV,hxV,hu',hl',hinside,houtside⟩

end OQ14.Packet05BoundaryMaterialMode
#print axioms OQ14.Packet05BoundaryMaterialMode.boundary_material_mode
