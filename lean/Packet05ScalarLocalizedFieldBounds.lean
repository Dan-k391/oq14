import Packet05ScalarPreAbsorption
import Packet05ScalarResidualBound

/-! Explicit L² bounds on the three non-principal fields in the localized
scalar difference-quotient energy estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarLocalizedFieldBounds
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05FlatWeight
  OQ14.MaxwellDifferenceQuotient OQ14.Packet05TensorCommutator
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05ScalarSquareCutoff OQ14.Packet05ScalarResidualBound
  OQ14.Packet05ScalarVectorBounds OQ14.Packet05ScalarLocalizedEnergy

theorem localized_field_bounds (ζ : RealTest Set.univ) (A : Fin 3 → Fin 3 → Test)
    (u : L2Scalar) (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (i : Fin 3) (h : ℝ) (hh : h ≠ 0) (b : ℝ)
    (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (a ηa ηb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hηa : ∀ x, ‖ζ.complexTest.function x‖ ≤ ηa)
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb) :
    let Q : L2Vector := fun j => quotient (C j) i h
    let Z := cutVector ζ Q
    let L := localizedMatrixFlux ζ A Q d hd
    let R := localizedResidual ζ A C F d hd i h hh b hb
    let T := localizedCutoffGradient ζ (quotient u i h)
    (∑ j : Fin 3, ‖L j‖) ≤ 3*(1+d)*a*(∑ j : Fin 3, ‖Z j‖) ∧
    (∑ j : Fin 3, ‖R j‖) ≤ ηa*(9*(1+d)*b*(‖C 0‖+‖C 1‖+‖C 2‖) + ∑ j : Fin 3, ‖quotient (F j) i h‖) ∧
    (∑ j : Fin 3, ‖T j‖) ≤ 3*ηb*‖quotient u i h‖ := by
  dsimp only
  let Q : L2Vector := fun j => quotient (C j) i h
  let Z := cutVector ζ Q
  let R := localizedResidual ζ A C F d hd i h hh b hb
  have hηa0 : 0 ≤ ηa := (norm_nonneg _).trans (hηa 0)
  have hL (j : Fin 3) : ‖localizedMatrixFlux ζ A Q d hd j‖ ≤
      (1+d)*a*(‖Z 0‖+‖Z 1‖+‖Z 2‖) := by
    have hw := weight_norm_bound d hd (matrixField A Z j)
    have hm := matrixField_norm A Z j a (ha j)
    exact hw.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm (by linarith : 0 ≤ 1+d))
  have hR (j : Fin 3) : ‖R j‖ ≤ ηa*((1+d)*(3*b*(‖C 0‖+‖C 1‖+‖C 2‖)) + ‖quotient (F j) i h‖) := by
    have hc := InteriorTestDensity.scaleL2_norm_le ζ.complexTest.function ζ.complexTest.regular.continuous
      ζ.complexTest.compact (mulWeight d hd (Packet05ScalarTransmissionCommutator.matrixResidual A C i j h hh b hb) - quotient (F j) i h) hηa
    have hr := dielectric_matrix_residual_bound A C F d hd i j h hh b hb
    exact hc.trans (mul_le_mul_of_nonneg_left hr hηa0)
  have hT (j : Fin 3) : ‖localizedCutoffGradient ζ (quotient u i h) j‖ ≤ ηb*‖quotient u i h‖ := by
    exact InteriorTestDensity.scaleL2_norm_le (fun x => dcoord ζ.complexTest.function x j)
      (partial_continuous ζ.complexTest.regular j) (ζ.complexTest.compact.fderiv_apply ℝ (basis j))
      (quotient u i h) (hηb j)
  simp only [Fin.sum_univ_three]
  constructor
  · have h0 := hL 0; have h1 := hL 1; have h2 := hL 2
    nlinarith
  constructor
  · have h0 := hR 0; have h1 := hR 1; have h2 := hR 2
    nlinarith
  · have h0 := hT 0; have h1 := hT 1; have h2 := hT 2
    nlinarith

end OQ14.Packet05ScalarLocalizedFieldBounds
#print axioms OQ14.Packet05ScalarLocalizedFieldBounds.localized_field_bounds
