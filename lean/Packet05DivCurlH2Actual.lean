import Packet05DivCurlH2

/-! The field H¹ premise is derived from the div–curl equations before the
second-order estimate is applied. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05DivCurlH2Actual
open OQ14.WeakCurl OQ14.DivCurlCompact OQ14.DivCurlRegularity OQ14.Packet05DivCurlH2

theorem compact_divcurl_h2_from_h1_sources (E C : L2Vector) (D : L2Scalar)
    (J : Fin 3 → L2Vector) (K : Fin 3 → L2Scalar)
    (hcompact : ∀ j, CompactRepresentative (E j))
    (hcurl : HasWeakCurl E C) (hdiv : HasWeakDivergence E D)
    (hJ : ∀ i j, HasWeakPartial (C j) (J i j) i)
    (hK : ∀ i, HasWeakPartial D (K i) i) :
    ∃ G : Fin 3 → L2Vector, ∃ H : Fin 3 → DerivativeIndex → L2Scalar,
      (∀ i j, HasWeakPartial (E j) (G i j) i) ∧
      (∀ i p, HasWeakPartial (G i p.2) (H i p) p.1) ∧
      (∑ i : Fin 3, ∑ j : Fin 3, ‖G i j‖^2) = (∑ j, ‖C j‖^2) + ‖D‖^2 ∧
      ∀ i, (∑ p, ‖H i p‖^2) = (∑ j, ‖J i j‖^2) + ‖K i‖^2 := by
  obtain ⟨G,hG,henergy⟩ := compact_weak_derivatives_energy hcompact hcurl hdiv
  obtain ⟨H,hH,hHenergy⟩ := compact_divcurl_h2 E C D (fun i j => G (i,j)) J K
    hcompact hcurl hdiv (fun i j => hG (i,j)) hJ hK
  refine ⟨fun i j => G (i,j),H,fun i j => hG (i,j),hH,?_,hHenergy⟩
  simpa only [Fintype.sum_prod_type] using henergy

end OQ14.Packet05DivCurlH2Actual
#print axioms OQ14.Packet05DivCurlH2Actual.compact_divcurl_h2_from_h1_sources
