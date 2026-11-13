import Packet05LocalPartialProduct
import Packet05ScalarLocalTangentialH2

/-! Local tangential H² information yields full H¹ regularity of each
localized tangential component of the scalar gradient. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TangentialGradientH1
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05RegionalPartial OQ14.Packet05LocalPartialProduct

theorem localized_tangential_gradient_h1 (V : Set Space) (hV : IsOpen V)
    (u : L2Scalar) (C : L2Vector) (hC : ∀ j, HasWeakPartial u (C j) j)
    (τ χ : Test) (hτ : ∀ x ∈ V, τ.function x = 1) (hχ : tsupport χ.function ⊆ V)
    (i : Fin 3) (hDer : ∀ j, ∃ v : L2Scalar,
      HasWeakPartial (scaleL2 τ.function τ.regular.continuous τ.compact (C j)) v i) :
    ∃ D : Fin 3 → L2Scalar, ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (C i)) (D j) j := by
  have hx (j : Fin 3) : ∃ D : L2Scalar, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (C i)) D j := by
    obtain ⟨v,hv⟩ := hDer j
    have hlocal : HasPartialOn V (C j) v i := cutoff_partial_on V τ (C j) v i hτ hv
    have hmix : HasPartialOn V (C i) v j :=
      mixed_partial_on_commute V hV u (C j) (C i) v j i
        (global_partial_on V u (C j) j (hC j))
        (global_partial_on V u (C i) i (hC i)) hlocal
    exact ⟨_, local_cutoff_weak_partial V χ hχ (C i) v j hmix⟩
  choose D hD using hx
  exact ⟨D,hD⟩

end OQ14.Packet05TangentialGradientH1
#print axioms OQ14.Packet05TangentialGradientH1.localized_tangential_gradient_h1
