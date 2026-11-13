import Packet06CompactLeft
import Packet06MaterialStatic
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06MaterialCompact
open Filter Set OQ14.StaticCoefficient OQ14.Packet06MaterialStatic
open scoped Topology InnerProduct InnerProductSpace ComplexConjugate
abbrev V := VectorFourier.VectorL2

theorem material_selfAdjoint (c : Coefficient) : IsSelfAdjoint (materialMultiplier c) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change ⟪sqrtMultiplier c (sqrtMultiplier c f), g⟫_ℂ =
    ⟪f, sqrtMultiplier c (sqrtMultiplier c g)⟫_ℂ
  rw [sqrtMultiplier_symmetric c (sqrtMultiplier c f) g, sqrtMultiplier_symmetric c f (sqrtMultiplier c g)]

theorem compact_material_family_uniform {X : Type*} [TopologicalSpace X]
    (c : ℕ → Coefficient) (c₀ : Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : c₀.bound ≤ D)
    (ha : ∀ᵐ x : Space, Tendsto (fun n => (c n).value x) atTop (𝓝 (c₀.value x)))
    (K : X → V →L[ℂ] V) (A : Set X) (hA : IsCompact A)
    (hcont : ContinuousOn K A) (hK : ∀ z ∈ A, IsCompactOperator (K z)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ A,
      ‖(K z).comp (materialMultiplier (c n) - materialMultiplier c₀)‖ < ε := by
  have hD : 0 ≤ D := (bound_nonnegative c₀).trans hb₀
  let T : ℕ → V →L[ℂ] V := fun n => materialMultiplier (c n) - materialMultiplier c₀
  have hadj (n : ℕ) : (T n)† = T n := by
    simp only [T, map_sub, (material_selfAdjoint _).adjoint_eq]
  have hbound (n : ℕ) : ‖T n‖ ≤ 2*D := by
    exact (norm_sub_le _ _).trans (by
      have h1 := (materialMultiplier_norm_le (c n)).trans (hb n)
      have h2 := (materialMultiplier_norm_le c₀).trans hb₀
      linarith)
  have hstrong (f : V) : Tendsto (fun n => ((T n)†) f) atTop (𝓝 0) := by
    simp only [hadj, T, ContinuousLinearMap.sub_apply]
    simpa using (materialMultiplier_strong c c₀ D hb hb₀ ha f).sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => materialMultiplier c₀ f) atTop (𝓝 (materialMultiplier c₀ f)))
  exact Packet06CompactAdjoint.compact_left_family_uniform T (2*D) (by positivity)
    hbound hstrong K A hA hcont hK
#print axioms OQ14.Packet06MaterialCompact.material_selfAdjoint
#print axioms OQ14.Packet06MaterialCompact.compact_material_family_uniform
end OQ14.Packet06MaterialCompact
