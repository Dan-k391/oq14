import Packet06MaxwellScalarEquation
import MaterialMaxwell

/-! The actual driven volume solution supplies the scalar transmission equation,
with its smooth incident electric field added to the Green correction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet07DrivenScalarEquation
open MeasureTheory Metric Set Maxwell WeakCurl DivCurlCompact
  ConicalGradientGraph Packet05RegionalDivergence Packet06ScalarGaussLocalization
open scoped SchwartzMap
abbrev V := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

theorem complex_electric_real (k : ℝ) (F : V) (ρ : Fin 3 → Space → ℂ) :
    Packet06ComplexElectric.electric (k : ℂ) F ρ = FieldResponse.electric k F ρ := by
  funext x i
  simp only [Packet06ComplexElectric.electric,FieldResponse.electric,
    ComplexDynamicKernel.remainder_ofReal]

theorem test_maxwell_gauss (k : ℝ) (hk : k ≠ 0) (ε : Space → ℝ) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H) (f : DynamicSource.Test) :
    (∑ i : Fin 3, ∫ x, (ε x : ℂ)*E x i*(DynamicSource.testPartial i f).val x)=0 := by
  have h := ComplexSphereWeak.div_curl (MaterialMaxwell.fieldPair H) f
  simp_rw [fun i => (hM i (DynamicSource.testPartial i f)).2] at h
  rw [← Finset.mul_sum] at h
  exact (mul_eq_zero.mp h).resolve_left
    (neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hk)))

theorem actual_driven_scalar_equation (c : StaticCoefficient.Coefficient)
    (k S : ℝ) (hk : k ≠ 0) (u f : V) (Einc Hinc : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x)=0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*Einc x i)
    (hsol : DynamicVolume.volumeBlock c k S u=f)
    (hEi : ∀ i, Continuous (fun x => Einc x i))
    (hHi : ∀ i, LocallyIntegrable (fun x => Hinc x i))
    (hvac : MaterialMaxwell.TestMaxwell k (fun _ => 1) Einc Hinc)
    (χ : ContDiffBump (0 : Space)) :
    let U := Packet06ComplexConePotential.potentialData (k : ℂ) S (StaticCoefficient.sqrtMultiplier c u)
      (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
    let W : Field := fun x i => Einc x i+Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x i
    ∃ hW : ∀ i, Continuous (fun x => W x i),
      CompactRepresentative (value χ U) ∧
      (∀ i, HasWeakPartial (value χ U) (gradient χ U i) i) ∧
      (∀ i, CompactRepresentative (correction χ W hW i)) ∧
      (∀ i, ∀ᵐ x ∂volume, x ∈ ball (0 : Space) χ.rIn →
        gradient χ U i x+correction χ W hW i x=MaterialField.total c k u Einc x i) ∧
      HasDivergenceOn (ball (0 : Space) χ.rIn)
        (flux χ U W hW (Packet06MaxwellScalarEquation.epsilon c)
          (Packet06MaxwellScalarEquation.epsilon_memLp c)) 0 := by
  dsimp only
  let U := Packet06ComplexConePotential.potentialData (k : ℂ) S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  let W : Field := fun x i => Einc x i+Packet06ComplexPotential.correction (k : ℂ) (DynamicVolume.source c u) x i
  have hWg := Packet06ComplexPotential.correction_continuous (k : ℂ) S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u)
  have hW : ∀ i, Continuous (fun x => W x i) := fun i => (hEi i).add (hWg i)
  have htotal := MaterialMaxwell.volume_solution_testMaxwell c k S u f Einc Hinc hc hincident hsol
    (fun i => (hEi i).locallyIntegrable) hHi hvac
  have he (i : Fin 3) (x : Space) : U.derivative i x+W x i=MaterialField.total c k u Einc x i := by
    dsimp only [U,W,Packet06ComplexConePotential.potentialData,MaterialField.total,MaterialField.scattered]
    rw [complex_electric_real]
    ring
  have hGauss (φ : 𝓢(Space,ℂ)) (hφ : tsupport (φ : Space → ℂ) ⊆ ball (0 : Space) χ.rIn) :
      (∑ i : Fin 3, ∫ x, Packet06MaxwellScalarEquation.epsilon c x*
        (U.derivative i x+W x i)*dcoord φ x i)=0 := by
    have hcompact : HasCompactSupport (φ : Space → ℂ) :=
      (isCompact_closedBall (0 : Space) χ.rIn).of_isClosed_subset (isClosed_tsupport _)
        (hφ.trans ball_subset_closedBall)
    have hh := test_maxwell_gauss k hk (MaterialMaxwell.dielectric c)
      (MaterialField.total c k u Einc) (MaterialMaxwell.totalMagnetic c k u Hinc) htotal ⟨φ,hcompact⟩
    simpa only [he,Packet06MaxwellScalarEquation.epsilon,MaterialMaxwell.dielectric,
      Complex.ofReal_add,Complex.ofReal_one,DynamicSource.testPartial,GradientProjection.pderivative_apply] using hh
  obtain ⟨hU,hG,hC,hE,hD⟩ := compact_scalar_equation χ U W hW
    (Packet06MaxwellScalarEquation.epsilon c) (Packet06MaxwellScalarEquation.epsilon_memLp c) hGauss
  refine ⟨hW,hU,hG,hC,?_,hD⟩
  intro i
  simpa only [he] using hE i

end OQ14.Packet07DrivenScalarEquation
#print axioms OQ14.Packet07DrivenScalarEquation.complex_electric_real
#print axioms OQ14.Packet07DrivenScalarEquation.test_maxwell_gauss
#print axioms OQ14.Packet07DrivenScalarEquation.actual_driven_scalar_equation
