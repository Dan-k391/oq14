import Packet05NormalFluxDataBounds

/-! First normal-flux array bound in terms of the original data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05FirstNormalFluxDataBound
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05NormalFluxArrays Packet05NormalFluxNorms Packet05NormalFluxDataBounds

theorem first_flux_original_bound (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (η : Test) (i : Fin 3) (a b r s : ℝ)
    (ha : ∀ p q x, ‖(A p q).function x‖ ≤ a)
    (hb : ∀ p q t x, ‖dcoord (A p q).function x t‖ ≤ b)
    (hr : ∀ x, ‖η.function x‖ ≤ r) (hs : ∀ t x, ‖dcoord η.function x t‖ ≤ s) :
    let B0 := (1+d)*(a*size (C1 0)+b*size C) + size (F1 0)
    let B1 := (1+d)*(a*size (C1 1)+b*size C) + size (F1 1)
    let B := (1+d)*a*size C+‖F 2‖
    ‖firstFluxArray A hA2 C F C1 F1 d hd η i‖ ≤ r*(B0+B1)+s*B := by
  dsimp only
  have hsum (Q : L2Vector) (q : Fin 3) : ‖Q q‖ ≤ size Q := by
    fin_cases q <;> simp [size] <;> linarith [norm_nonneg (Q 0), norm_nonneg (Q 1), norm_nonneg (Q 2)]
  apply first_flux_array_norm A hA2 C F C1 F1 d hd η r s _ _ _ hr hs
  · intro q
    have h := tangent_flux_norm A hA2 C F (C1 0) (F1 0) d hd 0 q a b ha (fun p q x => hb p q 0 x)
    have hs0 := hsum (F1 0) q
    dsimp [size] at *
    linarith
  · intro q
    have h := tangent_flux_norm A hA2 C F (C1 1) (F1 1) d hd 1 q a b ha (fun p q x => hb p q 1 x)
    have hs1 := hsum (F1 1) q
    dsimp [size] at *
    linarith
  · exact flux_norm A C F d hd 2 a ha

end OQ14.Packet05FirstNormalFluxDataBound
#print axioms OQ14.Packet05FirstNormalFluxDataBound.first_flux_original_bound
