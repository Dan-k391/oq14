import Packet05ScalarAbsorption
import Packet05RegionalScalarPreAbsorption

/-! Absorbed localized scalar difference-quotient estimate derived from the
actual weak equation, with source and cutoff norms explicit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RegionalScalarQuotientEstimate
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.MaxwellDifferenceQuotient OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarLocalizedEnergy OQ14.Packet05ScalarPreAbsorption
  OQ14.Packet05ScalarLocalizedFieldBounds OQ14.Packet05ScalarAbsorption
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_difference_quotient_estimate
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (u : L2Scalar) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (V : Set Space) (hdiv : OQ14.Packet05RegionalDivergence.HasDivergenceOn V (fun j => flux A C d hd j - F j) 0)
    (S₀ : Set Space) (θ : Test) (hθV : tsupport θ.function ⊆ V)
    (hθS : ∀ x ∈ S₀, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ))) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (hζS : ∀ x ∈ tsupport ζ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ i x, ‖slopeC g i.castSucc x‖ ≤ B i)
    (hA : ∀ x ∈ tsupport ζ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a ηa ηb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hηa : ∀ x, ‖ζ.complexTest.function x‖ ≤ ηa)
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb) :
    let Z := cutVector ζ (fun j => quotient (C j) i h)
    let K := 2+4*M^2
    let Ac := 3*(1+d)*a
    let Bc := 3*ηb
    let Dc := ηa*(9*(1+d)*b*(‖C 0‖+‖C 1‖+‖C 2‖) + ∑ j : Fin 3, ‖quotient (F j) i h‖)
    (∑ j : Fin 3, ‖Z j‖^2) ≤
      3*K^2*(2*Ac*Bc*‖quotient u i h‖+Dc)^2 +
        2*K*(Dc^2+(Bc*‖quotient u i h‖)^2) := by
  dsimp only
  let Q : L2Vector := fun j => quotient (C j) i h
  let Z := cutVector ζ Q
  let L := localizedMatrixFlux ζ A Q d hd
  let R := localizedResidual ζ A C F d hd i h hh b hb
  let T := localizedCutoffGradient ζ (quotient u i h)
  let S : ℝ := ∑ j : Fin 3, ‖Z j‖^2
  let X : ℝ := ∑ j : Fin 3, ‖Z j‖
  let Y : ℝ := ‖quotient u i h‖
  let K : ℝ := 2+4*M^2
  let Ac : ℝ := 3*(1+d)*a
  let Bc : ℝ := 3*ηb
  let Dc : ℝ := ηa*(9*(1+d)*b*(‖C 0‖+‖C 1‖+‖C 2‖) + ∑ j : Fin 3, ‖quotient (F j) i h‖)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hAc : 0 ≤ Ac := by
    have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
    dsimp [Ac]; positivity
  have hBc : 0 ≤ Bc := by
    have hb0 : 0 ≤ ηb := (norm_nonneg _).trans (hηb 0 0)
    dsimp [Bc]; positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hL0 : 0 ≤ ∑ j : Fin 3, ‖L j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hR0 : 0 ≤ ∑ j : Fin 3, ‖R j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hT0 : 0 ≤ ∑ j : Fin 3, ‖T j‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hbds := localized_field_bounds ζ A u C F d hd i h hh b hb a ηa ηb ha hηa hηb
  have hL : (∑ j : Fin 3, ‖L j‖) ≤ Ac*X := hbds.1
  have hR : (∑ j : Fin 3, ‖R j‖) ≤ Dc := hbds.2.1
  have hT : (∑ j : Fin 3, ‖T j‖) ≤ Bc*Y := hbds.2.2
  have hDc : 0 ≤ Dc := hR0.trans hR
  have hpre := OQ14.Packet05RegionalScalarPreAbsorption.regional_difference_preabsorption g hg ζ A u C F d hd hC V hdiv S₀ θ hθV hθS i hi h hh hζS b hb M hM B hB hA
  change S ≤ K*(2*(∑ j : Fin 3, ‖L j‖)*(∑ j : Fin 3, ‖T j‖) +
    (∑ j : Fin 3, ‖R j‖)*X + 2*(∑ j : Fin 3, ‖R j‖)*(∑ j : Fin 3, ‖T j‖)) at hpre
  have hLT := mul_le_mul hL hT hT0 (mul_nonneg hAc hX0)
  have hRX := mul_le_mul_of_nonneg_right hR hX0
  have hRT := mul_le_mul hR hT hT0 hDc
  have hraw : S ≤ K*(2*Ac*X*(Bc*Y) + Dc*X + 2*Dc*(Bc*Y)) := by
    apply hpre.trans
    apply mul_le_mul_of_nonneg_left _ hK
    nlinarith
  have hX : X^2 ≤ 3*S := by
    have hs := three_sum_square_le ‖Z 0‖ ‖Z 1‖ ‖Z 2‖
    simpa [X,S,Fin.sum_univ_three] using hs
  exact absorb_localized_scalar S X Y K Ac Bc Dc hK hX hraw

end OQ14.Packet05RegionalScalarQuotientEstimate
#print axioms OQ14.Packet05RegionalScalarQuotientEstimate.regional_difference_quotient_estimate
