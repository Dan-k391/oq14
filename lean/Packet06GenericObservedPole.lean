import Packet06PlacedPole

/-! A simple analytic sector pencil has an actual nonzero physical
observation after any explicit injective sector embedding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 300000
set_option maxRecDepth 10000
namespace OQ14.Packet06GenericObservedPole
open Filter Metric Maxwell Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open scoped Topology

def observation (c : StaticCoefficient.Coefficient) (R T : ℝ) (J : Sector →L[ℂ] VectorL2)
    (z : ℂ) : Sector →L[ℂ] VectorL2 := (Packet06LocalPencil.response c z R T).comp J

def SimpleObservedPole (c : StaticCoefficient.Coefficient) (R : ℝ) (J : Sector →L[ℂ] VectorL2)
    (A : ℂ → Sector →L[ℂ] Sector) (z : ℂ) (u : Sector) : Prop :=
  ∃ φ : Sector →L[ℂ] ℂ, φ (deriv A z u) ≠ 0 ∧
    ∀ T : ℝ, R ≤ T →
    ∃ (Q : Sector →L[ℂ] VectorL2) (B : ℂ → Sector →L[ℂ] VectorL2),
      Q ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, Q x = (φ x / φ (deriv A z u)) • Packet06LocalPencil.response c z R T (J u)) ∧
      Tendsto (fun v => (v-z) • (observation c R T J v).comp (Ring.inverse (A v))) (𝓝[≠] z) (𝓝 Q) ∧
      (∀ᶠ v in 𝓝[≠] z, (observation c R T J v).comp (Ring.inverse (A v)) = (v-z)⁻¹ • Q + B v)

theorem observed_of_simple (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (J : Sector →L[ℂ] VectorL2) (A : ℂ → Sector →L[ℂ] Sector) (z : ℂ) (u w : Sector)
    (ψ : Sector →L[ℂ] ℂ) (hA : AnalyticAt ℂ A z)
    (hC : IsUnit (repair (A z) w ψ)) (hk : A z u=0) (hψ : ψ u=1)
    (hds : deriv (fun v => scalar (A v) w ψ) z ≠ 0)
    (hker : ComplexConvolutionAnalytic.volumeBlock c z R (J u)=0) (hne : J u ≠ 0) :
    SimpleObservedPole c R J A z u := by
  have hi : Ring.inverse (repair (A z) w ψ) w=u := repaired_inverse_vector _ u w ψ hC hk hψ
  have hzero : scalar (A z) w ψ=0 := scalar_zero _ u w ψ hC hk hψ
  have hder := Packet06SchurAnalytic.scalar_hasDerivAt A (deriv A z) w ψ z
    hA.differentiableAt.hasDerivAt hC
  let φ := ψ.comp (Ring.inverse (repair (A z) w ψ))
  have hcross : φ (deriv A z u) ≠ 0 := by
    rw [hder.deriv,hi] at hds
    exact hds
  obtain ⟨Q,B,_,hB,hform,hlim,hexp⟩ := Packet06SchurPole.simple_inverse_expansion A w ψ z hA hC hzero hds
  simp only [hi] at hform
  refine ⟨φ,hcross,?_⟩
  intro T hT
  have hObs : AnalyticAt ℂ (observation c R T J) z := by
    exact (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip J).analyticAt _).comp
      (f := fun v : ℂ => Packet06LocalPencil.response c v R T)
      (Packet06LocalPencil.response_analyticAt _ _ T (by linarith) z)
  obtain ⟨D,hD,he⟩ := Packet06LaurentTransport.observation_expansion
    (fun v => Ring.inverse (A v)) Q B (observation c R T J) z hB hObs hexp
  have hCu : observation c R T J z u ≠ 0 :=
    Packet06Observation.kernel_observation_nonzero c z R T hT (J u) hc hker hne
  refine ⟨(observation c R T J z).comp Q,D,?_,hD,?_,?_,he⟩
  · exact Packet06LaurentTransport.observed_residue_nonzero Q (observation c R T J z)
      u φ _ hcross hform hCu (deriv A z u) hcross
  · exact Packet06LaurentTransport.observed_residue_form Q (observation c R T J z) u φ _ hform
  · exact Packet06LaurentTransport.observation_residue_limit
      (fun v => Ring.inverse (A v)) Q (observation c R T J) z hObs.continuousAt hlim
end OQ14.Packet06GenericObservedPole
#print axioms OQ14.Packet06GenericObservedPole.observed_of_simple
