import Packet07BoundaryNormalChart

/-! Genuine local graph charts for the actual affine binary material boundary. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07BoundaryNormalActual
open Filter Set Packet07BoundaryCoordinates
open scoped Topology

theorem chart_of_regular_boundary (B : Set Space) (x : Space)
    (hcert : ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧
      fderiv ℝ F x ≠ 0 ∧ ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, (y ∈ B ↔ 0 < F y)) :
    ∃ (F : Space → ℝ) (i : Fin 3) (g : Plane → ℝ) (V : Set Plane),
      ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      fderiv ℝ F x (EuclideanSpace.single i 1) ≠ 0 ∧ IsOpen V ∧ (chart i x).1 ∈ V ∧ ContinuousOn g V ∧
      ContDiffAt ℝ (⊤ : ℕ∞) g (chart i x).1 ∧
      (∀ᶠ y in 𝓝 x, (y ∈ B ↔ 0 < F y) ∧
        (F y = 0 ↔ (chart i y).2 = g (chart i y).1)) := by
  obtain ⟨F,hF,h0,hD,U,hU,hx,hB⟩ := hcert
  obtain ⟨i,g,V,hi,hV,hxV,hg,hgs,hgraph⟩ :=
    Packet07BoundaryNormalChart.regular_level_cartesian_normal_graph F x hF h0 hD
  refine ⟨F,i,g,V,hF,h0,hD,hi,hV,hxV,hg,hgs,?_⟩
  filter_upwards [hU.mem_nhds hx,hgraph] with y hy hgraf
  exact ⟨hB y hy,hgraf⟩

theorem actual_affine_body_charts {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ) (center : ι → Space)
    (ha0 : ∀ i, 0 < a i) (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j)) (s : ℝ) (hs : s ≠ 0) (shift : Space) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ frontier (Packet07AffineGeometry.map s shift ⁻¹'
        CommonBinaryInterface.body p a center n),
      ∃ (F : Space → ℝ) (i : Fin 3) (g : Plane → ℝ) (V : Set Plane),
        ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
        fderiv ℝ F x (EuclideanSpace.single i 1) ≠ 0 ∧ IsOpen V ∧ (chart i x).1 ∈ V ∧ ContinuousOn g V ∧
        ContDiffAt ℝ (⊤ : ℕ∞) g (chart i x).1 ∧
        (∀ᶠ y in 𝓝 x, (y ∈ Packet07AffineGeometry.map s shift ⁻¹'
            CommonBinaryInterface.body p a center n ↔ 0 < F y) ∧
          (F y = 0 ↔ (chart i y).2 = g (chart i y).1)) := by
  filter_upwards [CommonBinaryInterface.eventually_body_smooth p a center ha0 ha hsep] with n hn x hx
  exact chart_of_regular_boundary _ x
    (Packet07AffineSmooth.smooth_boundary_preimage s hs shift _ hn x hx)

end OQ14.Packet07BoundaryNormalActual
#print axioms OQ14.Packet07BoundaryNormalActual.chart_of_regular_boundary
#print axioms OQ14.Packet07BoundaryNormalActual.actual_affine_body_charts
