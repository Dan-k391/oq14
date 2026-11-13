import Packet05RegionalNormalRecovery
import Packet05WeightedMatrixDerivative
import Packet05ScalarDielectricFlux
import Packet05GraphFluxExtension
import Packet05CurlSourceH1

/-! Recover the normal-normal scalar derivative on a constant phase from the
actual variable-matrix divergence equation and tangential derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05ScalarNormalH2
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05FlatWeight OQ14.Packet05TensorCommutator
  OQ14.Packet05MatrixWeakDerivative OQ14.Packet05WeightedMatrixDerivative
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05GraphFluxExtension OQ14.Packet05PartialProduct
  OQ14.Packet05CurlSourceH1 OQ14.Packet05RegionalPartial OQ14.Packet05RegionalDivergence
  OQ14.Packet05RegionalNormalFlux OQ14.Packet05RegionalNormalRecovery

theorem scalar_phase_normal_normal (V W : Set Space) (A : Fin 3 → Fin 3 → Test)
    (hA : ∀ j k, ContDiff ℝ 2 (A j k).function) (C F C0 C1 : L2Vector)
    (F0 F1 F2n C0n C1n : L2Scalar) (d : ℝ) (hd : 0 ≤ d) (ε : ℂ) (hε : ε ≠ 0)
    (hphase : ∀ x ∈ V, weight d x = ε)
    (hdiv : HasDivergenceOn V (fun j => flux A C d hd j-F j) 0)
    (hC0 : ∀ j, HasWeakPartial (C j) (C0 j) 0)
    (hC1 : ∀ j, HasWeakPartial (C j) (C1 j) 1)
    (hF0 : HasWeakPartial (F 0) F0 0) (hF1 : HasWeakPartial (F 1) F1 1)
    (hF2n : HasWeakPartial (F 2) F2n 2)
    (hC0n : HasWeakPartial (C 0) C0n 2) (hC1n : HasWeakPartial (C 1) C1n 2)
    (r χ : Test) (hrV : tsupport r.function ⊆ V) (hχW : tsupport χ.function ⊆ W)
    (hrecip : ∀ x ∈ W, r.function x * (A 2 2).function x = 1) :
    ∃ N : L2Scalar, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (C 2)) N 2 := by
  let P : L2Vector := fun j => flux A C d hd j-F j
  let S : L2Scalar := scaleL2 (A 2 0).function (A 2 0).regular.continuous (A 2 0).compact (C 0) +
    scaleL2 (A 2 1).function (A 2 1).regular.continuous (A 2 1).compact (C 1)
  let DS : L2Scalar := cutoffProductDerivative (A 2 0) (C 0) C0n 2 +
    cutoffProductDerivative (A 2 1) (C 1) C1n 2
  let DP0 : L2Scalar := mulWeight d hd (matrixField A C0 0 + matrixField (derivativeMatrix A hA 0) C 0)-F0
  let DP1 : L2Scalar := mulWeight d hd (matrixField A C1 1 + matrixField (derivativeMatrix A hA 1) C 1)-F1
  have hp0 : HasWeakPartial (P 0) DP0 0 := by
    have hw := weighted_matrix_tangential_partial A hA C C0 d hd 0 0 (by decide) hC0
    intro φ
    have hw := hw φ; have hf := hF0 φ
    simp only [P, DP0, flux, map_sub]
    linear_combination hw-hf
  have hp1 : HasWeakPartial (P 1) DP1 1 := by
    have hw := weighted_matrix_tangential_partial A hA C C1 d hd 1 1 (by decide) hC1
    intro φ
    have hw := hw φ; have hf := hF1 φ
    simp only [P, DP1, flux, map_sub]
    linear_combination hw-hf
  have hpn : HasPartialOn V (P 2) (0-DP0-DP1) 2 :=
    regional_normal_flux_partial V P 0 DP0 DP1 hdiv
      (global_partial_on V _ _ 0 hp0) (global_partial_on V _ _ 1 hp1)
  have hS : HasWeakPartial S DS 2 := by
    have h0 := cutoff_weak_partial (A 2 0) (C 0) C0n 2 hC0n
    have h1 := cutoff_weak_partial (A 2 1) (C 1) C1n 2 hC1n
    intro φ
    have h0 := h0 φ; have h1 := h1 φ
    simp only [S, DS, cutoffProductDerivative, map_add] at h0 h1 ⊢
    linear_combination h0+h1
  have hrel : ∀ᵐ x ∂volume, x ∈ V → P 2 x + F 2 x - ε*S x =
      ε*scaleL2 (A 2 2).function (A 2 2).regular.continuous (A 2 2).compact (C 2) x := by
    filter_upwards [Lp.coeFn_sub (flux A C d hd 2) (F 2), mulWeight_ae d hd (matrixField A C 2),
      matrixField_ae A C 2, Lp.coeFn_add
        (scaleL2 (A 2 0).function (A 2 0).regular.continuous (A 2 0).compact (C 0))
        (scaleL2 (A 2 1).function (A 2 1).regular.continuous (A 2 1).compact (C 1)),
      scaleL2_ae (A 2 0).function (A 2 0).regular.continuous (A 2 0).compact (C 0),
      scaleL2_ae (A 2 1).function (A 2 1).regular.continuous (A 2 1).compact (C 1),
      scaleL2_ae (A 2 2).function (A 2 2).regular.continuous (A 2 2).compact (C 2)] with x hp hw hm hs h0 h1 h2 hx
    change (flux A C d hd 2-F 2 : L2Scalar) x + F 2 x - ε*S x = _
    rw [hp]
    simp only [Pi.sub_apply]
    change (mulWeight d hd (matrixField A C 2)) x - F 2 x + F 2 x - ε*S x = _
    rw [hw,hm]
    change _ - ε*(scaleL2 (A 2 0).function _ _ (C 0) + scaleL2 (A 2 1).function _ _ (C 1) : L2Scalar) x = _
    rw [hs]
    simp only [Pi.add_apply]
    rw [h0,h1,h2,hphase x hx]
    simp only [Fin.sum_univ_three]
    ring
  exact regional_recover_diagonal_normal V W (A 2 2) r χ hrV hχW hrecip
    (C 2) (P 2) (F 2) S (0-DP0-DP1) F2n DS ε hε hpn
    (global_partial_on V _ _ 2 hF2n) (global_partial_on V _ _ 2 hS) hrel

end OQ14.Packet05ScalarNormalH2
#print axioms OQ14.Packet05ScalarNormalH2.scalar_phase_normal_normal
