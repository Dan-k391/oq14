import Packet05DivergenceCommutation
import Packet05WeakFourier
import WeakPoynting.DivCurlRegularity

/-! Compact H² div–curl regularity with actual weak derivatives: if field,
curl and divergence already have L² first derivatives, apply the established
div–curl estimate to each differentiated field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05DivCurlH2
open OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.DivCurlCompact
  OQ14.DivCurlRegularity OQ14.Packet05WeakFourier OQ14.Packet05CurlCommutation
  OQ14.Packet05DivergenceCommutation

theorem compact_divcurl_h2 (E C : L2Vector) (D : L2Scalar)
    (G J : Fin 3 → L2Vector) (K : Fin 3 → L2Scalar)
    (hcompact : ∀ j, CompactRepresentative (E j))
    (hcurl : HasWeakCurl E C) (hdiv : HasWeakDivergence E D)
    (hG : ∀ i j, HasWeakPartial (E j) (G i j) i)
    (hJ : ∀ i j, HasWeakPartial (C j) (J i j) i)
    (hK : ∀ i, HasWeakPartial D (K i) i) :
    ∃ H : Fin 3 → DerivativeIndex → L2Scalar,
      (∀ i p, HasWeakPartial (G i p.2) (H i p) p.1) ∧
      ∀ i, (∑ p, ‖H i p‖^2) = (∑ j, ‖J i j‖^2) + ‖K i‖^2 := by
  have hex (i : Fin 3) : ∃ H : DerivativeIndex → L2Scalar,
      (∀ p, HasWeakPartial (G i p.2) (H p) p.1) ∧
      (∑ p, ‖H p‖^2) = (∑ j, ‖J i j‖^2) + ‖K i‖^2 := by
    apply compact_weak_derivatives_energy
    · intro j
      exact weak_partial_compact (hcompact j) i (hG i j)
    · exact partial_commutes_weakCurl E C (G i) (J i) i hcurl (hG i) (hJ i)
    · exact partial_commutes_weakDivergence E (G i) D (K i) i hdiv (hG i) (hK i)
  choose H hH using hex
  exact ⟨H, fun i => (hH i).1, fun i => (hH i).2⟩

end OQ14.Packet05DivCurlH2
#print axioms OQ14.Packet05DivCurlH2.compact_divcurl_h2
