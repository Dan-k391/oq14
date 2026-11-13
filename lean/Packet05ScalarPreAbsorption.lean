import Packet05ScalarLocalizedEnergy

/-! The actual localized quotient energy inequality before Young absorption.
Each term is an L² norm of a field constructed from the weak equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05ScalarPreAbsorption
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.WeakPower
  OQ14.DivCurlCompact OQ14.WeakConservation OQ14.WeakEnergy OQ14.Packet05FlatWeight
  OQ14.MaxwellDifferenceQuotient OQ14.Packet05TensorCommutator
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05ScalarPrincipalLocalization
  OQ14.Packet05ScalarLocalizedCoercivity OQ14.Packet05ScalarVectorBounds
  OQ14.Packet05ScalarDielectricFlux OQ14.Packet05ScalarLocalizedEnergy
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem localized_difference_preabsorption
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (u : L2Scalar) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) 0)
    (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (hA : ∀ x ∈ tsupport ζ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ)) :
    let Q : L2Vector := fun j => quotient (C j) i h
    let L := localizedMatrixFlux ζ A Q d hd
    let Z := cutVector ζ Q
    let R := localizedResidual ζ A C F d hd i h hh b hb
    let T := localizedCutoffGradient ζ (quotient u i h)
    (∑ j : Fin 3, ‖Z j‖^2) ≤ (2+4*M^2) *
      (2*(∑ j : Fin 3, ‖L j‖)*(∑ j : Fin 3, ‖T j‖) +
       (∑ j : Fin 3, ‖R j‖)*(∑ j : Fin 3, ‖Z j‖) +
       2*(∑ j : Fin 3, ‖R j‖)*(∑ j : Fin 3, ‖T j‖)) := by
  dsimp only
  let Q : L2Vector := fun j => quotient (C j) i h
  let L := localizedMatrixFlux ζ A Q d hd
  let Z := cutVector ζ Q
  let R := localizedResidual ζ A C F d hd i h hh b hb
  let T := localizedCutoffGradient ζ (quotient u i h)
  let p : ℂ := ∑ j : Fin 3, scalarProduct (L j) (conjScalar (Z j))
  let c : ℂ := ∑ j : Fin 3, scalarProduct (L j) (conjScalar (T j))
  let r : ℂ := ∑ j : Fin 3, scalarProduct (R j) (conjScalar (Z j))
  let t : ℂ := ∑ j : Fin 3, scalarProduct (R j) (conjScalar (T j))
  have hid : p + 2*c + r + 2*t = 0 := localized_difference_energy_identity A u C F d hd hC hdiv ζ i hi h hh b hb
  have hco := localized_principal_coercivity g hg ζ A Q M hM B hB hA d hd
  have he : (∑ j : Fin 3, scalarProduct (mulWeight d hd (matrixField A Q j))
      (conjScalar (scaleL2 (squareTest ζ).complexTest.function (squareTest ζ).complexTest.regular.continuous
        (squareTest ζ).complexTest.compact (Q j)))) = p := by
    apply Finset.sum_congr rfl
    intro j _
    rw [square_cutoff_principal_pairing ζ A Q d hd j]
    rfl
  rw [he] at hco
  have hp : p = -(2*c+r+2*t) := by linear_combination hid
  have hnorm : ‖p‖ ≤ 2*‖c‖ + ‖r‖ + 2*‖t‖ := by
    rw [hp, norm_neg]
    have hh1 := norm_add_le (2*c+r) (2*t)
    have hh2 := norm_add_le (2*c) r
    simp only [norm_mul, Complex.norm_ofNat] at hh1 hh2
    linarith
  have hc := vector_pairing_norm L T
  have hr := vector_pairing_norm R Z
  have ht := vector_pairing_norm R T
  have hpre : p.re ≤ 2*(∑ j : Fin 3, ‖L j‖)*(∑ j : Fin 3, ‖T j‖) +
      (∑ j : Fin 3, ‖R j‖)*(∑ j : Fin 3, ‖Z j‖) +
      2*(∑ j : Fin 3, ‖R j‖)*(∑ j : Fin 3, ‖T j‖) := by
    have h := Complex.re_le_norm p
    change ‖c‖ ≤ _ at hc
    change ‖r‖ ≤ _ at hr
    change ‖t‖ ≤ _ at ht
    linarith
  have hK : 0 ≤ 2+4*M^2 := by positivity
  have hbound := mul_le_mul_of_nonneg_left hpre hK
  have hfinal := hco.trans hbound
  simpa only [Fin.sum_univ_three] using hfinal

end OQ14.Packet05ScalarPreAbsorption
#print axioms OQ14.Packet05ScalarPreAbsorption.localized_difference_preabsorption
