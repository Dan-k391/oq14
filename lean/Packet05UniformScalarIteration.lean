import Packet05ActualSecondUniformBound
import Packet05ActualFirstSecondBounds
import Packet05ActualSecondOriginalBound
import Packet05SecondEnvelopeOriginal
import Packet05ScalarSecondTangential
import Packet05SecondForcingOriginalBound
import Packet05LocalizedForcingNorm
import Packet05EnergyEnvelope
import Packet05SecondTangentialExplicit
import Packet05FirstTangentialArrayBound
import Packet05LocalDerivative

/-! Direct two-tangential derivative construction from the original scalar
transmission equation, using two nested localization stages. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet05UniformScalarIteration
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakConservation
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarCutoffTransfer OQ14.Packet05RegionalScalarLocalization
  OQ14.Packet05ScalarDirectionalTangentialH2 OQ14.Packet05ScalarSecondTangential
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05ScalarPrincipalLocalization
open scoped Topology
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem uniform_scalar_iteration
    (g : Plane → ℝ) (hg : ContDiff ℝ 2 g) (A : Fin 3 → Fin 3 → Test)
    (hA2 : ∀ j k, ContDiff ℝ 2 (A j k).function)
    (hA3 : ∀ j k, ContDiff ℝ 3 (A j k).function)
    (u D : L2Scalar) (C F Fi Ft Fit : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j-F j) D)
    (hu : CompactRepresentative u) (hF : ∀ j, CompactRepresentative (F j))
    (i t : Fin 3) (hi : i ≠ 2) (ht : t ≠ 2)
    (hFi : ∀ j, HasWeakPartial (F j) (Fi j) i)
    (hFt : ∀ j, HasWeakPartial (F j) (Ft j) t)
    (hFit : ∀ j, HasWeakPartial (Fi j) (Fit j) t)
    (S₀ V S : Set Space) (hV : IsOpen V) (hVS₀ : V ⊆ S₀)
    (hD : ∀ᵐ x ∂volume, x ∈ S₀ → D x = 0)
    (τ : RealTest Set.univ) (hτ2 : ContDiff ℝ 2 τ.function) (hτ : ∀ x ∈ V, τ.function x = 1)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hτSi : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis i ∈ S₀)
    (hτSt : ∀ h : ℝ, |h| < δ₀ → ∀ x ∈ tsupport τ.function, x ∈ S₀ ∧ x + h • basis t ∈ S₀)
    (κ : RealTest Set.univ) (hκ2 : ContDiff ℝ 2 κ.function) (hκV : tsupport κ.function ⊆ V)
    (hκS : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℝ)))
    (ζ : RealTest Set.univ) (δ : ℝ) (hδ : 0 < δ)
    (hζS : ∀ h : ℝ, |h| < δ → ∀ x ∈ tsupport ζ.function, x ∈ S ∧ x + h • basis t ∈ S)
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
    (hc : ∀ j k x, ‖dcoord (OQ14.Packet05MatrixWeakDerivative.derivativeMatrix A hA2 i j k).function x t‖ ≤ c)
    (hτc : ∀ x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff τ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hτ2) i).function x t‖ ≤ τc)
    (hκa : ∀ x, ‖κ.complexTest.function x‖ ≤ κa)
    (hκb : ∀ j x, ‖dcoord κ.complexTest.function x j‖ ≤ κb)
    (hκc : ∀ j x, ‖dcoord (OQ14.MaxwellCutoffCommutator.derivativeCutoff κ.complexTest.toTest
      (Complex.ofRealCLM.contDiff.comp hκ2) j).function x t‖ ≤ κc)  (K : ℝ)
    (hCnorm : ∀ j, ‖C j‖ ≤ K) (hFnorm : ∀ j, ‖F j‖ ≤ K)
    (hFinorm : ∀ j, ‖Fi j‖ ≤ K) (hFtnorm : ∀ j, ‖Ft j‖ ≤ K) (hFitnorm : ∀ j, ‖Fit j‖ ≤ K) :
    ∃ DC : L2Vector, (∀ j, HasWeakPartial (cutScalar τ (C j)) (DC j) i) ∧
      (∑ j : Fin 3, ‖DC j‖) ≤ 3 * Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope (3*K) (3*K) d b M a τa τb) + 9*τb*K ∧
      ∀ j, ∃ H : L2Scalar, HasWeakPartial (cutScalar ζ (localizedGradient κ (C i) DC j)) H t ∧
        ‖H‖ ≤ Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope
          (OQ14.Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb)
          (OQ14.Packet05SecondEnvelope.forcing (3*K) (3*K) (3*K) (3*K) (3*K) d b a c τa τb τc κa κb κc M)
          d b M a ηa ηb) + 3*ηb*(OQ14.Packet05SecondEnvelope.gradient (3*K) (3*K) d b M a τa τb κa κb) := by
  have hsum (V : L2Vector) (h : ∀ j, ‖V j‖ ≤ K) : (∑ j : Fin 3, ‖V j‖) ≤ 3*K := by
    simp only [Fin.sum_univ_three]
    linarith [h 0,h 1,h 2]
  have hP := hsum C hCnorm
  have hF0 := hsum F hFnorm
  have hF1 := hsum Fi hFinorm
  have hF2 := hsum Ft hFtnorm
  have hF12 := hsum Fit hFitnorm
  obtain ⟨DC,hDC,hH⟩ := OQ14.Packet05ActualSecondUniformBound.actual_second_uniform_bound
    g hg A hA2 hA3 u D C F Fi Ft Fit d hd hC hdiv hu hF i t hi ht hFi hFt hFit
    S₀ V S hV hVS₀ hD τ hτ2 hτ δ₀ hδ₀ hτSi hτSt κ hκ2 hκV hκS ζ δ hδ hζS
    b hb M hM B hB hmetricτ hmetricζ a τa τb ηa ηb ha hτa hτb hηa hηb
    c τc κa κb κc hc hτc hκa hκb hκc (3*K) (3*K) (3*K) (3*K) (3*K) hP hF0 hF1 hF2 hF12
  obtain ⟨DC',hDC',hnorm⟩ := OQ14.Packet05FirstTangentialArrayBound.first_tangential_array_bound
    g hg τ A u D C F Fi d hd hC hdiv hu hF S₀ δ₀ hδ₀ i hi hFi hD hτSi
    b hb M hM B hB hmetricτ a τa τb ha hτa hτb
  have heq : DC=DC' := by
    funext j
    exact OQ14.Packet05LocalDerivative.weak_partial_unique _ _ _ i (hDC j) (hDC' j)
  have hsumDC : (∑ j : Fin 3, ‖DC j‖) ≤ 3 * Real.sqrt (OQ14.Packet05EnergyEnvelope.envelope (3*K) (3*K) d b M a τa τb) + 9*τb*K := by
    rw [heq]
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0 0 0)
    have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 0 0)
    have hτa0 : 0 ≤ τa := (norm_nonneg _).trans (hτa 0)
    have ht0 : 0 ≤ τb := (norm_nonneg _).trans (hτb 0 0)
    have hP' : ‖C 0‖+‖C 1‖+‖C 2‖ ≤ 3*K := by simpa only [Fin.sum_univ_three] using hP
    have hen := OQ14.Packet05EnergyEnvelope.directional_energy_le_envelope C Fi (3*K) (3*K) d b M a τa τb hd hb0 ha0 hτa0 ht0 hP' hF1
    have hsqrt := Real.sqrt_le_sqrt hen
    have hmul := mul_le_mul_of_nonneg_left hP ht0
    nlinarith [hnorm]
  exact ⟨DC,hDC,hsumDC,hH⟩

end OQ14.Packet05UniformScalarIteration
#print axioms OQ14.Packet05UniformScalarIteration.uniform_scalar_iteration
