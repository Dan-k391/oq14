import Packet05ScalarTangentialContinuity
import Packet05ScalarActualSecondTangential

/-! Continuity of an actual tangential scalar-gradient component, derived by
both tangential iterations of the variable-metric transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ActualScalarTangentialContinuity
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05LocalPartialProduct OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ScalarActualSecondTangential OQ14.Packet05ScalarTangentialContinuity
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05LocalDerivative
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_tangential_gradient_continuous
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F Fi F0 F1 Fi0 Fi1 : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (i : Fin 3) (hi : i ≠ 2)
    (hFi : ∀ j, HasWeakPartial (F j) (Fi j) i)
    (hF0 : ∀ j, HasWeakPartial (F j) (F0 j) 0)
    (hF1 : ∀ j, HasWeakPartial (F j) (F1 j) 1)
    (hFi0 : ∀ j, HasWeakPartial (Fi j) (Fi0 j) 0)
    (hFi1 : ∀ j, HasWeakPartial (Fi j) (Fi1 j) 1)
    (S₀ V S W : Set Space) (hV : IsOpen V) (hW : IsOpen W) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτSi : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (hτS0 : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 0 ∈ S₀)
    (hτS1 : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 1 ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS0 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis 0 ∈ S)
    (hζS1 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis 1 ∈ S)
    (hζW : ∀ x ∈ W, ζ.function x = 1) (χ : Test) (hχW : tsupport χ.function ⊆ W)
    (hχ2 : ContDiff ℝ 2 χ.function)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b)
    (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B : Fin 2 → ℝ) (hB : ∀ l x, ‖slopeC g l.castSucc x‖ ≤ B l)
    (hmetricτ : ∀ x ∈ tsupport τ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (hmetricζ : ∀ x ∈ tsupport ζ.function, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (a τa τb ηa ηb : ℝ) (ha : ∀ j k x, ‖(A j k).function x‖ ≤ a)
    (hτa : ∀ x, ‖τ.complexTest.function x‖ ≤ τa)
    (hτb : ∀ j x, ‖dcoord τ.complexTest.function x j‖ ≤ τb)
    (hηa : ∀ x, ‖ζ.complexTest.function x‖ ≤ ηa)
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact (cutScalar κ (C i)) x) =ᵐ[volume] f := by
  obtain ⟨DC0,hDC0,hH0⟩ := actual_second_tangential_derivatives g hg A hA2 hA3 u D C F Fi F0 Fi0 d hd
    hC hdiv hu hF i 0 hi (by decide) hFi hF0 hFi0 S₀ V S hV hVS₀ hD τ hτ2 hτ δ₀ hδ₀ hτSi hτS0
    κ hκ2 hκV hκS ζ δ hδ hζS0 b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
  obtain ⟨DC1,hDC1,hH1⟩ := actual_second_tangential_derivatives g hg A hA2 hA3 u D C F Fi F1 Fi1 d hd
    hC hdiv hu hF i 1 hi (by decide) hFi hF1 hFi1 S₀ V S hV hVS₀ hD τ hτ2 hτ δ₀ hδ₀ hτSi hτS1
    κ hκ2 hκV hκS ζ δ hδ hζS1 b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
  have hDC : DC1 = DC0 := by
    funext j
    exact weak_partial_unique (cutScalar τ (C j)) (DC1 j) (DC0 j) i (hDC1 j) (hDC0 j)
  subst DC1
  have hτc : ∀ x ∈ V, τ.complexTest.function x = 1 := by
    intro x hx; simp [RealTest.complexTest,hτ x hx]
  have hκV' : tsupport κ.complexTest.function ⊆ V := by
    simpa only [RealTest.complexTest, tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero] using hκV
  have hgrad (j : Fin 3) : HasPartialOn V (C i) (DC0 j) j := by
    have hl := cutoff_partial_on V τ.complexTest.toTest (C j) (DC0 j) i hτc (hDC0 j)
    exact mixed_partial_on_commute V hV u (C j) (C i) (DC0 j) j i
      (global_partial_on V u (C j) j (hC j)) (global_partial_on V u (C i) i (hC i)) hl
  have hgradκ (j : Fin 3) : HasWeakPartial (cutScalar κ (C i))
      (localizedGradient κ (C i) DC0 j) j :=
    local_cutoff_weak_partial V κ.complexTest.toTest hκV' (C i) (DC0 j) j (hgrad j)
  have hζc : ∀ x ∈ W, ζ.complexTest.function x = 1 := by
    intro x hx; simp [RealTest.complexTest,hζW x hx]
  apply scalar_tangential_continuity W hW (cutScalar κ (C i)) (localizedGradient κ (C i) DC0)
    hgradκ ζ.complexTest.toTest χ hζc hχW hχ2
  intro t ht j
  fin_cases t
  · exact hH0 j
  · exact hH1 j
  · exact (ht rfl).elim

end OQ14.Packet05ActualScalarTangentialContinuity
#print axioms OQ14.Packet05ActualScalarTangentialContinuity.actual_tangential_gradient_continuous
