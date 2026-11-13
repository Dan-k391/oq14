import Packet05DirectionalQuotient
import Packet05ScalarQuotientEstimate
import Packet05ScalarLocalQuotientEstimate

/-! Uniform localized tangential gradient-quotient bound from actual H¹
scalar and source data, with the cutoff and coefficient constants explicit. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.Packet05ScalarDirectionalUniformQuotients
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.MaxwellDifferenceQuotient OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarQuotientEstimate
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def uniformEnergyBound (C : L2Vector) (JF : L2Vector)
    (d b M a ηa ηb : ℝ) : ℝ :=
  let P := ‖C 0‖+‖C 1‖+‖C 2‖
  let K := 2+4*M^2
  let Ac := 3*(1+d)*a
  let Bc := 3*ηb
  let Dc := ηa*(9*(1+d)*b*P + ∑ j : Fin 3, ‖JF j‖)
  3*K^2*(2*Ac*Bc*P+Dc)^2 + 2*K*(Dc^2+(Bc*P)^2)

theorem directional_uniform_gradient_quotient
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (u D : L2Scalar) (C F : L2Vector) (JF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (S₀ : Set Space) (i : Fin 3) (hi : i ≠ 2)
    (hJF : ∀ j, HasWeakPartial (F j) (JF j) i) (h : ℝ) (hh : h ≠ 0)
    (hD : ∀ᵐ x ∂MeasureTheory.volume, x ∈ S₀ → D x = 0)
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
    (∑ j : Fin 3, ‖cutVector ζ (fun k => quotient (C k) i h) j‖^2) ≤
      uniformEnergyBound C JF d b M a ηa ηb := by
  let P : ℝ := ‖C 0‖+‖C 1‖+‖C 2‖
  let K : ℝ := 2+4*M^2
  let Ac : ℝ := 3*(1+d)*a
  let Bc : ℝ := 3*ηb
  let D0 : ℝ := ηa*(9*(1+d)*b*P + ∑ j : Fin 3, ‖JF j‖)
  let Dh : ℝ := ηa*(9*(1+d)*b*P + ∑ j : Fin 3, ‖quotient (F j) i h‖)
  let Y : ℝ := ‖quotient u i h‖
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
  have hηa0 : 0 ≤ ηa := (norm_nonneg _).trans (hηa 0)
  have hηb0 : 0 ≤ ηb := (norm_nonneg _).trans (hηb 0 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0 0)
  have hAc : 0 ≤ Ac := by dsimp [Ac]; positivity
  have hBc : 0 ≤ Bc := by dsimp [Bc]; positivity
  have hD0 : 0 ≤ D0 := by dsimp [D0]; positivity
  have hDh : 0 ≤ Dh := by dsimp [Dh]; positivity
  have hY : 0 ≤ Y := norm_nonneg _
  have hYle : Y ≤ P := by
    have hhU := quotient_bound hu hC i h hh
    simpa [Y,P,Fin.sum_univ_three] using hhU
  have hFle : (∑ j : Fin 3, ‖quotient (F j) i h‖) ≤ ∑ j : Fin 3, ‖JF j‖ := by
    apply Finset.sum_le_sum
    intro j hj
    exact OQ14.Packet05DirectionalQuotient.directional_quotient_bound (F j) (JF j) (hF j) i (hJF j) h hh
  have hDle : Dh ≤ D0 := by
    dsimp [Dh,D0]
    exact mul_le_mul_of_nonneg_left (add_le_add_left hFle _) hηa0
  have hAcBc : 0 ≤ 2*Ac*Bc := mul_nonneg (mul_nonneg (by norm_num) hAc) hBc
  have hmain0 : 0 ≤ 2*Ac*Bc*Y+Dh := add_nonneg (mul_nonneg hAcBc hY) hDh
  have hmain : 2*Ac*Bc*Y+Dh ≤ 2*Ac*Bc*P+D0 := by
    exact add_le_add (mul_le_mul_of_nonneg_left hYle hAcBc) hDle
  have hby0 : 0 ≤ Bc*Y := mul_nonneg hBc hY
  have hby : Bc*Y ≤ Bc*P := mul_le_mul_of_nonneg_left hYle hBc
  have hs1 : (2*Ac*Bc*Y+Dh)^2 ≤ (2*Ac*Bc*P+D0)^2 := (sq_le_sq₀ hmain0 (hmain0.trans hmain)).2 hmain
  have hs2 : Dh^2 ≤ D0^2 := (sq_le_sq₀ hDh hD0).2 hDle
  have hs3 : (Bc*Y)^2 ≤ (Bc*P)^2 := (sq_le_sq₀ hby0 (hby0.trans hby)).2 hby
  have he := OQ14.Packet05ScalarLocalQuotientEstimate.local_difference_quotient_estimate g hg ζ A u D C F d hd hC hdiv S₀ i hi h hh hD hζS b hb M hM B hB hA a ηa ηb ha hηa hηb
  change (∑ j : Fin 3, ‖cutVector ζ (fun k => quotient (C k) i h) j‖^2) ≤
    3*K^2*(2*Ac*Bc*Y+Dh)^2 + 2*K*(Dh^2+(Bc*Y)^2) at he
  have hmul1 := mul_le_mul_of_nonneg_left hs1 (show 0 ≤ 3*K^2 by positivity)
  have hmul2 := mul_le_mul_of_nonneg_left (add_le_add hs2 hs3) (show 0 ≤ 2*K by positivity)
  change _ ≤ 3*K^2*(2*Ac*Bc*P+D0)^2 + 2*K*(D0^2+(Bc*P)^2)
  linarith

end OQ14.Packet05ScalarDirectionalUniformQuotients
#print axioms OQ14.Packet05ScalarDirectionalUniformQuotients.directional_uniform_gradient_quotient
