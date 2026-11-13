import Packet05ActualLocalSecondDerivatives


/-! Continuity of an actual tangential scalar-gradient component, derived by
both tangential iterations of the variable-metric transmission equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ActualAllTangential
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05RegionalPartial
  OQ14.Packet05LocalPartialProduct OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ActualLocalSecondDerivatives OQ14.Packet05ScalarActualSecondTangential OQ14.Packet05LocalSecondTangential
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05LocalDerivative
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem actual_all_tangential
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function) (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F F0 F1 F00 F01 F10 F11 : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (hF0 : ∀ j, HasWeakPartial (F j) (F0 j) 0)
    (hF1 : ∀ j, HasWeakPartial (F j) (F1 j) 1)
    (hF00 : ∀ j, HasWeakPartial (F0 j) (F00 j) 0)
    (hF01 : ∀ j, HasWeakPartial (F0 j) (F01 j) 1)
    (hF10 : ∀ j, HasWeakPartial (F1 j) (F10 j) 0)
    (hF11 : ∀ j, HasWeakPartial (F1 j) (F11 j) 1)
    (S₀ V S W : Set Space) (hV : IsOpen V) (hW : IsOpen W) (hWV : W ⊆ V) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτS0 : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 0 ∈ S₀)
    (hτS1 : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis 1 ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS0 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis 0 ∈ S)
    (hζS1 : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis 1 ∈ S)
    (hκW : ∀ x ∈ W, κ.function x = 1) (hζW : ∀ x ∈ W, ζ.function x = 1)
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
    ∃ DC : Fin 3 → L2Vector, ∃ HC : Fin 3 → Fin 3 → L2Vector,
      (∀ i, i ≠ 2 → ∀ j, HasPartialOn W (C j) (DC i j) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasPartialOn W (DC i j) (HC i t j) t) := by
  obtain ⟨D0,H00,H01,hD0,hH00,hH01⟩ :=
    Packet05ActualLocalSecondDerivatives.actual_local_second_derivatives g hg A hA2 hA3 u D C F F0 F0 F1 F00 F01 d hd
      hC hdiv hu hF 0 (by decide) hF0 hF0 hF1 hF00 hF01 S₀ V S W hV hW hWV hVS₀ hD τ hτ2 hτ
      δ₀ hδ₀ hτS0 hτS0 hτS1 κ hκ2 hκV hκS ζ δ hδ hζS0 hζS1 hκW hζW
      b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
  obtain ⟨D1,H10,H11,hD1,hH10,hH11⟩ :=
    Packet05ActualLocalSecondDerivatives.actual_local_second_derivatives g hg A hA2 hA3 u D C F F1 F0 F1 F10 F11 d hd
      hC hdiv hu hF 1 (by decide) hF1 hF0 hF1 hF10 hF11 S₀ V S W hV hW hWV hVS₀ hD τ hτ2 hτ
      δ₀ hδ₀ hτS1 hτS0 hτS1 κ hκ2 hκV hκS ζ δ hδ hζS0 hζS1 hκW hζW
      b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
  let DC : Fin 3 → L2Vector := ![D0,D1,0]
  let HC : Fin 3 → Fin 3 → L2Vector := ![![H00,H01,0],![H10,H11,0],![0,0,0]]
  refine ⟨DC,HC,?_,?_⟩
  · intro i hi j
    fin_cases i
    · exact hD0 j
    · exact hD1 j
    · exact (hi rfl).elim
  · intro i hi t ht j
    fin_cases i <;> fin_cases t
    · exact hH00 j
    · exact hH01 j
    · exact (ht rfl).elim
    · exact hH10 j
    · exact hH11 j
    · exact (ht rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim
    · exact (hi rfl).elim

end OQ14.Packet05ActualAllTangential
#print axioms OQ14.Packet05ActualAllTangential.actual_all_tangential
