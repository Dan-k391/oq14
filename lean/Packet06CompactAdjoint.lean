import Packet06StrongCompact
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06CompactAdjoint
open Metric Filter Set
open scoped Topology InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Compactness of the Hilbert adjoint, derived by finite-dimensional
orthogonal approximation. -/
theorem compact_adjoint (K : E →L[ℂ] E) (hK : IsCompactOperator K) : IsCompactOperator (K†) := by
  change K† ∈ {f : E →L[ℂ] E | IsCompactOperator f}
  rw [← isClosed_setOf_isCompactOperator.closure_eq]
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨V,hV,B,hB⟩ := HilbertFiniteRank.factor_approx K hK ε hε
  letI : FiniteDimensional ℂ V := hV
  letI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let F : E →L[ℂ] E := V.subtypeL.comp B
  have hBcompact : IsCompactOperator (B†) := by
    change IsCompactOperator ((B†).toLinearMap)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall _ zero_lt_one]
    have hc : IsCompact (B† '' closedBall (0 : V) 1) :=
      (isCompact_closedBall (0 : V) 1).image (B†).continuous
    convert hc using 1
    exact hc.isClosed.closure_eq
  have hFa : IsCompactOperator (F†) := by
    change IsCompactOperator ((V.subtypeL.comp B)†)
    rw [ContinuousLinearMap.adjoint_comp]
    exact hBcompact.comp_clm _
  refine ⟨F†,hFa,?_⟩
  rw [dist_eq_norm, ← map_sub]
  simpa only [ContinuousLinearMap.adjoint.norm_map, norm_sub_rev] using hB

#print axioms OQ14.Packet06CompactAdjoint.compact_adjoint
end OQ14.Packet06CompactAdjoint
