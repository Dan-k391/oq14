import Packet05QuantitativeAnisotropic

/-! Exact L² norms of the Fourier factors entering the anisotropic supremum
estimate, in terms of the genuine weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05FourierDerivativeNorm
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05WeakFourier

def fourierConstant : ℂ := -(2 * Real.pi * Complex.I)

theorem fourierConstant_ne_zero : fourierConstant ≠ 0 := by
  unfold fourierConstant
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (by norm_num)
    (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)

theorem coordinate_factor_l2 (u D : L2Scalar) (hu : CompactRepresentative u)
    (i : Fin 3) (hD : HasWeakPartial u D i) :
    let hp := frequency_coordinate_memLp hu i hD
    hp.toLp (fun ξ : Space => (ξ i : ℂ) * FourierL2.fourierEquiv.symm u ξ) =
      fourierConstant⁻¹ • FourierL2.fourierEquiv.symm D := by
  dsimp only
  apply Lp.ext
  filter_upwards [(frequency_coordinate_memLp hu i hD).coeFn_toLp,
    Lp.coeFn_smul fourierConstant⁻¹ (FourierL2.fourierEquiv.symm D),
    inverse_fourier_weak_partial hu i hD] with x hp hs hfour
  rw [hp,hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  change _ = fourierConstant⁻¹ * FourierL2.fourierEquiv.symm D x
  rw [hfour]
  change _ = fourierConstant⁻¹ * (fourierConstant * (x i : ℂ) * FourierL2.fourierEquiv.symm u x)
  field_simp [fourierConstant_ne_zero]
  ring

theorem coordinate_factor_norm (u D : L2Scalar) (hu : CompactRepresentative u)
    (i : Fin 3) (hD : HasWeakPartial u D i) :
    let hp := frequency_coordinate_memLp hu i hD
    ‖hp.toLp (fun ξ : Space => (ξ i : ℂ) * FourierL2.fourierEquiv.symm u ξ)‖ =
      ‖fourierConstant⁻¹‖ * ‖D‖ := by
  dsimp only
  rw [coordinate_factor_l2 u D hu i hD, norm_smul, FourierL2.fourierEquiv.symm.norm_map]

theorem mixed_factor_l2 (u D H : L2Scalar) (hu : CompactRepresentative u)
    (i j : Fin 3) (hD : HasWeakPartial u D i) (hH : HasWeakPartial D H j) :
    let hm := frequency_mixed_memLp hu i j hD hH
    hm.toLp (fun ξ : Space => (ξ i : ℂ) * (ξ j : ℂ) * FourierL2.fourierEquiv.symm u ξ) =
      (fourierConstant⁻¹)^2 • FourierL2.fourierEquiv.symm H := by
  dsimp only
  apply Lp.ext
  have hDc := weak_partial_compact hu i hD
  filter_upwards [(frequency_mixed_memLp hu i j hD hH).coeFn_toLp,
    Lp.coeFn_smul ((fourierConstant⁻¹)^2) (FourierL2.fourierEquiv.symm H),
    inverse_fourier_weak_partial hu i hD, inverse_fourier_weak_partial hDc j hH] with x hp hs h0 h1
  rw [hp,hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h1,h0]
  change _ = (fourierConstant⁻¹)^2 * (fourierConstant * (x j : ℂ) *
    (fourierConstant * (x i : ℂ) * FourierL2.fourierEquiv.symm u x))
  field_simp [fourierConstant_ne_zero]
  ring

theorem mixed_factor_norm (u D H : L2Scalar) (hu : CompactRepresentative u)
    (i j : Fin 3) (hD : HasWeakPartial u D i) (hH : HasWeakPartial D H j) :
    let hm := frequency_mixed_memLp hu i j hD hH
    ‖hm.toLp (fun ξ : Space => (ξ i : ℂ) * (ξ j : ℂ) * FourierL2.fourierEquiv.symm u ξ)‖ =
      ‖fourierConstant⁻¹‖^2 * ‖H‖ := by
  dsimp only
  rw [mixed_factor_l2 u D H hu i j hD hH, norm_smul, norm_pow,
    FourierL2.fourierEquiv.symm.norm_map]

end OQ14.Packet05FourierDerivativeNorm
#print axioms OQ14.Packet05FourierDerivativeNorm.fourierConstant_ne_zero
#print axioms OQ14.Packet05FourierDerivativeNorm.coordinate_factor_l2
#print axioms OQ14.Packet05FourierDerivativeNorm.coordinate_factor_norm
#print axioms OQ14.Packet05FourierDerivativeNorm.mixed_factor_l2
#print axioms OQ14.Packet05FourierDerivativeNorm.mixed_factor_norm
