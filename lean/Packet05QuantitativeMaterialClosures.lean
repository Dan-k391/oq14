import Packet05QuantitativeMaterialPhases

/-! Literal material-side quantitative bounds extend to phase closures. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05QuantitativeMaterialClosures
open MeasureTheory Set Maxwell Packet05ChartBasis Packet05ChartLinearEquiv
  Packet05GraphChartMap Packet05PhysicalGraphChart Packet05PhysicalChartBranches
  Packet05GraphSmooth Packet05LocalDerivative

theorem material_phase_closure_bounds (body : Set Space) (up : Bool) (axis : Fin 3)
    (g : ConicalSmoothJunction.Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (T : Set Space) (hT : IsOpen T) (x : Space) (hx : physicalFlatMap up axis g x ∈ T)
    (hside : ∀ y ∈ T, inverseOriented up axis (graphMap (liftedHeight g) y) ∈ body ↔ 0 < y 2)
    (E : Field) (lower upper : Fin 3 → Space → ℂ)
    (hl : ∀ j, Continuous (lower j)) (hu : ∀ j, Continuous (upper j))
    (hle : ∀ j, (fun y => E y j) =ᵐ[volume.restrict
      (physicalFlatMap up axis g ⁻¹' (T ∩ {y | y 2 < 0}))] lower j)
    (hue : ∀ j, (fun y => E y j) =ᵐ[volume.restrict
      (physicalFlatMap up axis g ⁻¹' (T ∩ {y | 0 < y 2}))] upper j)
    (B : ℝ) (hlb : ∀ j y, y ∈ physicalFlatMap up axis g ⁻¹' (T ∩ {y | y 2 < 0}) → ‖lower j y‖ ≤ B)
    (hub : ∀ j y, y ∈ physicalFlatMap up axis g ⁻¹' (T ∩ {y | 0 < y 2}) → ‖upper j y‖ ≤ B)
    (Uin Uout : Set Space) (hin : Uin ⊆ body) (hout : Uout ⊆ bodyᶜ) :
    ∃ V : Set Space, IsOpen V ∧ x ∈ V ∧
      (∀ j, Continuous (upper j)) ∧ (∀ j, Continuous (lower j)) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict (V ∩ body)] upper j) ∧
      (∀ j, (fun y => E y j) =ᵐ[volume.restrict (V ∩ bodyᶜ)] lower j) ∧
      (∀ j y, y ∈ V ∩ body → ‖upper j y‖ ≤ B) ∧
      (∀ j y, y ∈ V ∩ bodyᶜ → ‖lower j y‖ ≤ B) ∧
      (∀ j y, y ∈ closure Uin ∩ V → ‖upper j y‖ ≤ B) ∧
      (∀ j y, y ∈ closure Uout ∩ V → ‖lower j y‖ ≤ B) := by
  obtain ⟨V,hV,hxV,hu',hl',hAEin,hAEout,hBin,hBout⟩ :=
    Packet05QuantitativeMaterialPhases.quantitative_material_phases body up axis g hg T hT x hx hside
      E lower upper hl hu hle hue B hlb hub
  refine ⟨V,hV,hxV,hu',hl',hAEin,hAEout,hBin,hBout,?_,?_⟩
  · intro j
    apply Packet05PhaseCoverLocalBound.local_phase_bound Uin V hV (upper j) (hu j) B
    intro y hy
    exact hBin j y ⟨hy.2,hin hy.1⟩
  · intro j
    apply Packet05PhaseCoverLocalBound.local_phase_bound Uout V hV (lower j) (hl j) B
    intro y hy
    exact hBout j y ⟨hy.2,hout hy.1⟩

end OQ14.Packet05QuantitativeMaterialClosures
#print axioms OQ14.Packet05QuantitativeMaterialClosures.material_phase_closure_bounds
