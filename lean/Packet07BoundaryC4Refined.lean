import Packet07BoundaryNormalActual

/-! Shrinking the genuine chart gives C⁴ graph and defining function on open neighborhoods. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryC4Refined
open Filter Set Packet07BoundaryCoordinates
open scoped Topology

theorem chart_of_regular_boundary (B : Set Space) (x : Space)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ B ↔ 0 < F y)) :
    ∃ (F : Space → ℝ) (i : Fin 3) (g : Plane → ℝ) (V : Set Plane) (W : Set Space),
      fderiv ℝ F x (EuclideanSpace.single i 1) ≠ 0 ∧
      IsOpen V ∧ (chart i x).1 ∈ V ∧ ContDiffOn ℝ 4 g V ∧
      IsOpen W ∧ x ∈ W ∧ ContDiffOn ℝ 4 F W ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      (∀ y ∈ W, (y ∈ B ↔ 0 < F y) ∧
        (F y = 0 ↔ (chart i y).2 = g (chart i y).1)) := by
  obtain ⟨F,i,g,V,hF,h0,hD,hi,hV,hxV,hg,hgs,hlocal⟩ :=
    Packet07BoundaryNormalActual.chart_of_regular_boundary B x hcert
  obtain ⟨V',hV',hgs'⟩ := hgs.contDiffOn (m := 4) (by change ((4 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top) (by norm_num)
  obtain ⟨V'',hV''sub,hV''open,hxV''⟩ := mem_nhds_iff.mp hV'
  obtain ⟨W',hW',hFs⟩ := hF.contDiffOn (m := 4) (by change ((4 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞); exact WithTop.coe_le_coe.mpr le_top) (by norm_num)
  have hloc : {y | (y ∈ B ↔ 0 < F y) ∧
      (F y = 0 ↔ (chart i y).2 = g (chart i y).1)} ∈ 𝓝 x := hlocal
  obtain ⟨W'',hW''sub,hW''open,hxW''⟩ := mem_nhds_iff.mp (inter_mem hW' hloc)
  refine ⟨F,i,g,V ∩ V'',W'',hi,hV.inter hV''open,⟨hxV,hxV''⟩,?_,hW''open,hxW'',?_,h0,hD,?_⟩
  · exact hgs'.mono (fun y hy => hV''sub hy.2)
  · exact hFs.mono (fun y hy => (hW''sub hy).1)
  · intro y hy
    exact (hW''sub hy).2

end OQ14.Packet07BoundaryC4Refined
#print axioms OQ14.Packet07BoundaryC4Refined.chart_of_regular_boundary
