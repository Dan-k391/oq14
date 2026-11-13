import Packet05RegionalDirectionalUniform
import Packet05DifferenceConverse
import MaxwellCutoffCommutator

/-! Actual localized tangential second derivatives of scalar transmission
solutions, extracted from the uniform quotient estimate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05RegionalDirectionalTangentialH2
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakConservation
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.MaxwellDifferenceQuotient OQ14.MaxwellCutoffCommutator
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarPrincipalLocalization OQ14.Packet05ScalarCutoffTransfer
  OQ14.Packet05RegionalDirectionalUniform OQ14.Packet05DifferenceConverse
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem regional_tangential_gradient_derivative
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (ζ : RealTest Set.univ)
    (A : Fin 3 → Fin 3 → Test) (u : L2Scalar) (C F : L2Vector) (JF : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (hC : ∀ j, HasWeakPartial u (C j) j)
    (V : Set Space) (hdiv : OQ14.Packet05RegionalDivergence.HasDivergenceOn V (fun j => flux A C d hd j - F j) 0)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (S₀ : Set Space) (θ : Test) (hθV : tsupport θ.function ⊆ V)
    (hθS : ∀ x ∈ S₀, θ.function =ᶠ[nhds x] (fun _ => (1 : ℂ))) (δ : ℝ) (hδ : 0 < δ) (i j : Fin 3) (hi : i ≠ 2)
    (hJF : ∀ j, HasWeakPartial (F j) (JF j) i)
    (hζS : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
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
    ∃ v : L2Scalar, HasWeakPartial (cutScalar ζ (C j)) v i ∧
      ‖v‖ ≤ Real.sqrt (uniformEnergyBound C JF d b M a ηa ηb) + 3*ηb*‖C j‖ := by
  let K : ℝ := uniformEnergyBound C JF d b M a ηa ηb
  let N : ℝ := Real.sqrt K + 3*ηb*‖C j‖
  have hηb0 : 0 ≤ ηb := (norm_nonneg _).trans (hηb 0 0)
  have hN : 0 ≤ N := add_nonneg (Real.sqrt_nonneg K) (by positivity)
  have hq : ∀ h : ℝ, h ≠ 0 → |h| < δ → ‖quotient (cutScalar ζ (C j)) i h‖ ≤ N := by
    intro h hh hsmall
    have hs := regional_uniform_gradient_quotient g hg ζ A u C F JF d hd hC V hdiv hu hF S₀ θ hθV hθS i hi hJF h hh (hζS h hsmall) b hb M hM B hB hA a ηa ηb ha hηa hηb
    change (∑ k : Fin 3, ‖cutVector ζ (fun l => quotient (C l) i h) k‖^2) ≤ K at hs
    have hK : 0 ≤ K := le_trans (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) hs
    have hsingle : ‖cutVector ζ (fun l => quotient (C l) i h) j‖^2 ≤
        ∑ k : Fin 3, ‖cutVector ζ (fun l => quotient (C l) i h) k‖^2 :=
      Finset.single_le_sum (f := fun k : Fin 3 => ‖cutVector ζ (fun l => quotient (C l) i h) k‖^2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hlocal : ‖cutScalar ζ (quotient (C j) i h)‖ ≤ Real.sqrt K := by
      apply (Real.le_sqrt (norm_nonneg _) hK).2
      exact hsingle.trans hs
    have hc := cutoffSource_norm ζ.complexTest.toTest (C j) i h hh ηb hηb
    change ‖quotient (scaleL2 ζ.complexTest.function ζ.complexTest.regular.continuous ζ.complexTest.compact (C j)) i h‖ ≤ N
    rw [cutoff_quotient_decomposition ζ.complexTest.toTest (C j) i h hh ηb hηb]
    exact (norm_add_le _ _).trans (add_le_add hlocal hc)
  exact weakPartial_of_bounded_quotients (cutScalar ζ (C j)) i N δ hN hδ hq

end OQ14.Packet05RegionalDirectionalTangentialH2
#print axioms OQ14.Packet05RegionalDirectionalTangentialH2.regional_tangential_gradient_derivative
