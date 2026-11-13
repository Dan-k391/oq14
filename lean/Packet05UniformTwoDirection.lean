import Packet05UniformScalarIteration
import Packet05QuantitativeNestedAlignment

/-! Both tangential directions with one family-uniform first and mixed ceiling. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet05UniformTwoDirection
open MeasureTheory Set Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05RegionalPartial Packet05RegionalDivergence Packet05ScalarDielectricFlux
  Packet05ScalarCutoffTransfer Packet05RegionalScalarLocalization Packet05GraphSlopeMultiplier
open scoped Topology
abbrev Plane := ConicalSmoothJunction.Plane

theorem uniform_two_direction_iteration
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F : L2Vector) (F1 : Fin 3 → L2Vector) (F2 : Fin 3 → Fin 3 → L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (hF1 : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (F j) (F1 i j) i)
    (hF2 : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (F1 i j) (F2 i t j) t)
    (S₀ V S : Set Space) (hV : IsOpen V) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτS : ∀ i, i ≠ 2 → ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS : ∀ t, t ≠ 2 → ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis t ∈ S)
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
    (hηb : ∀ j x, ‖dcoord ζ.complexTest.function x j‖ ≤ ηb)  (c τc κa κb κc : ℝ)
    (hc : ∀ i t j k x, ‖dcoord (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hτc : ∀ i t x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff τ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hτ2) i).function x t‖ ≤ τc)
    (hκa : ∀ x, ‖κ.complexTest.function x‖ ≤ κa)
    (hκb : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ κb)
    (hκc : ∀ j t x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff κ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hκ2) j).function x t‖ ≤ κc)  (K : ℝ)
    (hCnorm : ∀ j, ‖C j‖ ≤ K) (hFnorm : ∀ j, ‖F j‖ ≤ K)
    (hF1norm : ∀ i, i ≠ 2 → ∀ j, ‖F1 i j‖ ≤ K)
    (hF2norm : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, ‖F2 i t j‖ ≤ K)
    (W : Set Space) (hW : IsOpen W) (hWV : W ⊆ V)
    (hκW : ∀ x ∈ W, κ.function x = 1) (hζW : ∀ x ∈ W, ζ.function x = 1) :
    let P := 3 * Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope (3*K) (3*K) d b M a τa τb) + 9*τb*K
    let Q := Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope
      (OQ14.Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
      (OQ14.Packet05SecondEnvelope.forcing (3*K) (3*K) (3*K) (3*K) (3*K) d b a c τa τb τc κa κb κc M)
      d b M a ηa ηb) + 3*ηb*(OQ14.Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
    ∃ D0 D1 H00 H01 H10 H11 : L2Vector,
      (∀ j, HasPartialOn W (C j) (D0 j) 0) ∧ (∀ j, HasPartialOn W (C j) (D1 j) 1) ∧
      (∀ j, HasPartialOn W (D0 j) (H00 j) 0) ∧ (∀ j, HasPartialOn W (D0 j) (H01 j) 1) ∧
      (∀ j, HasPartialOn W (D1 j) (H10 j) 0) ∧ (∀ j, HasPartialOn W (D1 j) (H11 j) 1) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C 0) D0 j)) (H00 j) 0) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C 0) D0 j)) (H01 j) 1) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C 1) D1 j)) (H10 j) 0) ∧
      (∀ j, HasWeakPartial (cutScalar ζ (localizedGradient κ (C 1) D1 j)) (H11 j) 1) ∧
      (∑ j : Fin 3, ‖D0 j‖) ≤ P ∧ (∑ j : Fin 3, ‖D1 j‖) ≤ P ∧
      (∀ j, ‖H00 j‖ ≤ Q ∧ ‖H01 j‖ ≤ Q ∧ ‖H10 j‖ ≤ Q ∧ ‖H11 j‖ ≤ Q) := by
  dsimp only
  let P := 3 * Real.sqrt (Packet05EnergyEnvelope.envelope (3*K) (3*K) d b M a τa τb) + 9*τb*K
  let Q := Real.sqrt (Packet05EnergyEnvelope.envelope
      (Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
      (Packet05SecondEnvelope.forcing (3*K) (3*K) (3*K) (3*K) (3*K) d b a c τa τb τc κa κb κc M)
      d b M a ηa ηb) + 3*ηb*(Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
  have step (i t : Fin 3) (hi : i ≠ 2) (ht : t ≠ 2) :
      ∃ DC : L2Vector, (∀ j, HasWeakPartial (cutScalar τ (C j)) (DC j) i) ∧
        (∑ j : Fin 3, ‖DC j‖) ≤ P ∧
        ∀ j, ∃ H : L2Scalar, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) DC j)) H t ∧ ‖H‖ ≤ Q :=
    Packet05UniformScalarIteration.uniform_scalar_iteration g hg A hA2 hA3 u D C F (F1 i) (F1 t) (F2 i t) d hd
      hC hdiv hu hF i t hi ht (hF1 i hi) (hF1 t ht) (hF2 i hi t ht)
      S₀ V S hV hVS₀ hD τ hτ2 hτ δ₀ hδ₀ (hτS i hi) (hτS t ht) κ hκ2 hκV hκS ζ δ hδ (hζS t ht)
      b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
      c τc κa κb κc (hc i t) (hτc i t) hκa hκb (fun j x => hκc j t x) K
      hCnorm hFnorm (hF1norm i hi) (hF1norm t ht) (hF2norm i hi t ht)
  obtain ⟨D00,hD00,hP00,h00⟩ := step 0 0 (by decide) (by decide)
  obtain ⟨D01,hD01,hP01,h01⟩ := step 0 1 (by decide) (by decide)
  obtain ⟨D10,hD10,hP10,h10⟩ := step 1 0 (by decide) (by decide)
  obtain ⟨D11,hD11,hP11,h11⟩ := step 1 1 (by decide) (by decide)
  have heq0 : D01=D00 := by
    funext j
    exact Packet05LocalDerivative.weak_partial_unique _ _ _ 0 (hD01 j) (hD00 j)
  have heq1 : D11=D10 := by
    funext j
    exact Packet05LocalDerivative.weak_partial_unique _ _ _ 1 (hD11 j) (hD10 j)
  subst D01
  subst D11
  choose H00 hH00 hQ00 using h00
  choose H01 hH01 hQ01 using h01
  choose H10 hH10 hQ10 using h10
  choose H11 hH11 hQ11 using h11
  have hlocal0 := Packet05QuantitativeNestedAlignment.align_nested_derivatives V W hW hWV τ κ ζ hτ hκW hζW
    C 0 D00 D00 H00 H01 hD00 hD00 hH00 hH01 P Q Q hP00 hQ00 hQ01
  have hlocal1 := Packet05QuantitativeNestedAlignment.align_nested_derivatives V W hW hWV τ κ ζ hτ hκW hζW
    C 1 D10 D10 H10 H11 hD10 hD10 hH10 hH11 P Q Q hP10 hQ10 hQ11
  exact ⟨D00,D10,H00,H01,H10,H11,hlocal0.1,hlocal1.1,hlocal0.2.1,hlocal0.2.2.1,
    hlocal1.2.1,hlocal1.2.2.1,hH00,hH01,hH10,hH11,hP00,hP10,
    fun j => ⟨hQ00 j,hQ01 j,hQ10 j,hQ11 j⟩⟩

end OQ14.Packet05UniformTwoDirection
#print axioms OQ14.Packet05UniformTwoDirection.uniform_two_direction_iteration
