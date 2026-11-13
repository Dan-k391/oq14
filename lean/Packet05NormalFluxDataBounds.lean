import Packet05DifferentiatedFluxNorm

/-! Direct bounds of the explicit normal-flux arrays by original data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet05NormalFluxDataBounds
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05NormalFluxArrays Packet05NormalFluxNorms Packet05DifferentiatedFluxNorm
  Packet05TensorCommutator Packet05ScalarVectorBounds Packet05ScalarResidualBound
  Packet05MatrixWeakDerivative Packet05DifferentiatedScalarEquation

def size (C : L2Vector) : ℝ := ‖C 0‖+‖C 1‖+‖C 2‖

theorem second_flux_original_bound (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (C F : L2Vector) (C1 F1 : Fin 3 → L2Vector) (C2 F2 : Fin 3 → Fin 3 → L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (χ : Test) (i j : Fin 3) (a b c r s : ℝ)
    (ha : ∀ p q x, ‖(A p q).function x‖ ≤ a)
    (hb : ∀ p q t x, ‖dcoord (A p q).function x t‖ ≤ b)
    (hc : ∀ p q t x, ‖dcoord (derivativeMatrix A hA2 i p q).function x t‖ ≤ c)
    (hr : ∀ x, ‖χ.function x‖ ≤ r) (hs : ∀ t x, ‖dcoord χ.function x t‖ ≤ s) :
    let B0 := (1+d)*(a*size (C2 i 0)+b*size (C1 i)) +
      (‖F2 i 0 0‖+‖F2 i 0 1‖+‖F2 i 0 2‖)+(1+d)*(b*size (C1 0)+c*size C)
    let B1 := (1+d)*(a*size (C2 i 1)+b*size (C1 i)) +
      (‖F2 i 1 0‖+‖F2 i 1 1‖+‖F2 i 1 2‖)+(1+d)*(b*size (C1 1)+c*size C)
    let B := (1+d)*a*size (C1 i) + ‖F1 i 2‖+(1+d)*b*size C
    ‖secondFluxArray A hA2 hA3 C F C1 F1 C2 F2 d hd χ i j‖ ≤ r*(B0+B1)+s*B := by
  dsimp only
  have hsum (Q : L2Vector) (q : Fin 3) : ‖Q q‖ ≤ size Q := by
    fin_cases q <;> simp [size] <;> linarith [norm_nonneg (Q 0), norm_nonneg (Q 1), norm_nonneg (Q 2)]
  let R := differentiatedSource A hA2 C (F1 i) d hd i
  let R0 := sourceDerivative A hA2 hA3 C (C1 0) (F2 i 0) d hd i 0
  let R1 := sourceDerivative A hA2 hA3 C (C1 1) (F2 i 1) d hd i 1
  have hR (q : Fin 3) : ‖R q‖ ≤ ‖F1 i q‖+(1+d)*b*size C :=
    differentiated_source_norm A hA2 C (F1 i) d hd i q b (fun p q x => hb p q i x)
  have hR0 (q : Fin 3) : ‖R0 q‖ ≤ size (F2 i 0)+(1+d)*(b*size (C1 0)+c*size C) := by
    have h := source_derivative_norm A hA2 hA3 C (C1 0) (F2 i 0) d hd i 0 q b c
      (fun p q x => hb p q i x) (fun p q x => hc p q 0 x)
    exact h.trans (add_le_add_right (hsum (F2 i 0) q) _)
  have hR1 (q : Fin 3) : ‖R1 q‖ ≤ size (F2 i 1)+(1+d)*(b*size (C1 1)+c*size C) := by
    have h := source_derivative_norm A hA2 hA3 C (C1 1) (F2 i 1) d hd i 1 q b c
      (fun p q x => hb p q i x) (fun p q x => hc p q 1 x)
    exact h.trans (add_le_add_right (hsum (F2 i 1) q) _)
  apply second_flux_array_norm A hA2 hA3 C F C1 F1 C2 F2 d hd χ i j r s _ _ _ hr hs
  · intro q
    have h := tangent_flux_norm A hA2 (C1 i) R (C2 i 0) R0 d hd 0 q a b ha (fun p q x => hb p q 0 x)
    have h0 := hR0 q
    dsimp [size] at *
    linarith
  · intro q
    have h := tangent_flux_norm A hA2 (C1 i) R (C2 i 1) R1 d hd 1 q a b ha (fun p q x => hb p q 1 x)
    have h1 := hR1 q
    dsimp [size] at *
    linarith
  · have h := flux_norm A (C1 i) R d hd 2 a ha
    exact h.trans (by have h' := hR 2; dsimp [size] at *; linarith)

end OQ14.Packet05NormalFluxDataBounds
#print axioms OQ14.Packet05NormalFluxDataBounds.second_flux_original_bound
