import Packet06PlacedSchur

/-! Nonzero physical electric observation of the actual transported-sector simple pole. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06PlacedPole
open Filter Metric Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open Packet06PlacedKernel Packet06PlacedEquivalence
open Packet06PlacedSector (pencil)
open scoped Topology

def observation (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s)
    (a : Maxwell.Space) (T : ℝ) (z : ℂ) : Sector →L[ℂ] VectorL2 :=
  (Packet06LocalPencil.response (placedCoefficient s a c) z (R/s+‖a‖) T).comp
    ((placed s hs a).toContinuousLinearMap.comp Sector.subtypeL)

def SimpleObservedPole (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s)
    (a : Maxwell.Space) (z : ℂ) (u : Sector) : Prop :=
  ∃ φ : Sector →L[ℂ] ℂ, φ (deriv (pencil c R s hs a) z u) ≠ 0 ∧
    ∀ T : ℝ, R/s+‖a‖ ≤ T →
    ∃ (Q : Sector →L[ℂ] VectorL2) (B : ℂ → Sector →L[ℂ] VectorL2),
      Q ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, Q x = (φ x / φ (deriv (pencil c R s hs a) z u)) •
        Packet06LocalPencil.response (placedCoefficient s a c) z (R/s+‖a‖) T (placed s hs a u)) ∧
      Tendsto (fun v => (v-z) • (observation c R s hs a T v).comp
        (Ring.inverse (pencil c R s hs a v))) (𝓝[≠] z) (𝓝 Q) ∧
      (∀ᶠ v in 𝓝[≠] z, (observation c R s hs a T v).comp
        (Ring.inverse (pencil c R s hs a v)) = (v-z)⁻¹ • Q + B v)

theorem observation_analyticAt (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s)
    (a : Maxwell.Space) (T : ℝ) (hT : 0 ≤ T+(R/s+‖a‖)) (z : ℂ) :
    AnalyticAt ℂ (observation c R s hs a T) z := by
  exact (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip
    ((placed s hs a).toContinuousLinearMap.comp Sector.subtypeL)).analyticAt _).comp
      (f := fun v : ℂ => Packet06LocalPencil.response (placedCoefficient s a c) v (R/s+‖a‖) T)
      (Packet06LocalPencil.response_analyticAt _ _ T hT z)

theorem coefficient_support (c : StaticCoefficient.Coefficient) (R : ℝ)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) :
    ∀ x : Maxwell.Space, x ∉ closedBall 0 (R/s+‖a‖) →
      (placedCoefficient s a c).value (VectorFourier.coordinateMap x)=0 :=
  Packet06TranslationMaterial.coefficient_support a _ (R/s)
    (ComplexDilationVolume.coefficient_support s R hs _
      (Packet06CyclicDynamic.coefficient_support c R hc))

theorem certified_observed_pole (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u) :
    SimpleObservedPole c R s hs a ((s : ℂ)*z) u := by
  obtain ⟨w,ψ,hC,hk,hψ,hds⟩ :=
    Packet06PlacedSchur.certified_schur c ha hm R hR hc s hs a z u hcert
  let A := pencil c R s hs a
  let zp := (s : ℂ)*z
  have hA : AnalyticAt ℂ A zp := Packet06PlacedSchur.pencil_analyticAt c R hR hc s hs a zp
  have hi : Ring.inverse (repair (A zp) w ψ) w=u := repaired_inverse_vector _ u w ψ hC hk hψ
  have hzero : scalar (A zp) w ψ=0 := scalar_zero _ u w ψ hC hk hψ
  have hder := Packet06SchurAnalytic.scalar_hasDerivAt A (deriv A zp) w ψ zp
    hA.differentiableAt.hasDerivAt hC
  let φ := ψ.comp (Ring.inverse (repair (A zp) w ψ))
  have hcross : φ (deriv A zp u) ≠ 0 := by
    rw [hder.deriv,hi] at hds
    exact hds
  obtain ⟨Q,B,_,hB,hform,hlim,hexp⟩ :=
    Packet06SchurPole.simple_inverse_expansion A w ψ zp hA hC hzero hds
  simp only [hi] at hform
  refine ⟨φ,hcross,?_⟩
  intro T hT
  have hS : 0 ≤ R/s+‖a‖ := add_nonneg (div_nonneg hR hs.le) (norm_nonneg _)
  have hObs := observation_analyticAt c R s hs a T (by linarith) zp
  obtain ⟨D,hD,he⟩ := Packet06LaurentTransport.observation_expansion
    (fun v => Ring.inverse (A v)) Q B (observation c R s hs a T) zp hB hObs hexp
  have hker : ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) zp
      (R/s+‖a‖) (placed s hs a u)=0 := by
    rw [Packet06PlacedConjugacy.volume_intertwines c R hR hc s hs a z u]
    obtain ⟨_,_,_,hku,_,_⟩ := hcert
    rw [hku,map_zero]
  have hne : placed s hs a (u : VectorL2) ≠ 0 := by
    intro heq
    have hu0 : (u : VectorL2)=0 := (placed s hs a).injective (heq.trans (map_zero _).symm)
    have hu' : u=0 := Subtype.ext hu0
    rw [hu',map_zero] at hψ
    exact zero_ne_one hψ
  have hCu : observation c R s hs a T zp u ≠ 0 :=
    Packet06Observation.kernel_observation_nonzero _ zp _ T hT _
      (coefficient_support c R hc s hs a) hker hne
  refine ⟨(observation c R s hs a T zp).comp Q,D,?_,hD,?_,?_,he⟩
  · exact Packet06LaurentTransport.observed_residue_nonzero Q (observation c R s hs a T zp)
      u φ _ hcross hform hCu (deriv A zp u) hcross
  · exact Packet06LaurentTransport.observed_residue_form Q (observation c R s hs a T zp)
      u φ _ hform
  · exact Packet06LaurentTransport.observation_residue_limit
      (fun v => Ring.inverse (A v)) Q (observation c R s hs a T) zp hObs.continuousAt hlim

end OQ14.Packet06PlacedPole
#print axioms OQ14.Packet06PlacedPole.observation_analyticAt
#print axioms OQ14.Packet06PlacedPole.coefficient_support
#print axioms OQ14.Packet06PlacedPole.certified_observed_pole
