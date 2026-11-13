import Packet06CompactAdjoint
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06CompactAdjoint
open Filter Set
open scoped Topology InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Strong convergence of the adjoints gives uniform compact-left convergence. -/
theorem compact_left_family_uniform {X : Type*} [TopologicalSpace X]
    (T : ℕ → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ n, ‖T n‖ ≤ C)
    (hstrong : ∀ x, Tendsto (fun n => ((T n)†) x) atTop (𝓝 0))
    (K : X → E →L[ℂ] E) (D : Set X) (hD : IsCompact D)
    (hcont : ContinuousOn K D) (hK : ∀ z ∈ D, IsCompactOperator (K z)) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ z ∈ D, ‖(K z).comp (T n)‖ < ε := by
  have hcont' : ContinuousOn (fun z => (K z)†) D :=
    Continuous.comp_continuousOn ContinuousLinearMap.adjoint.continuous hcont
  have h := Packet06StrongCompact.compact_family_uniform (fun n => (T n)†) C hC
    (fun n => by simpa only [ContinuousLinearMap.adjoint.norm_map] using hb n)
    hstrong (fun z => (K z)†) D hD hcont' (fun z hz => compact_adjoint (K z) (hK z hz))
  intro ε hε
  filter_upwards [h ε hε] with n hn z hz
  have hn' := hn z hz
  rw [← ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint.norm_map] at hn'
  exact hn'
#print axioms OQ14.Packet06CompactAdjoint.compact_left_family_uniform
end OQ14.Packet06CompactAdjoint
