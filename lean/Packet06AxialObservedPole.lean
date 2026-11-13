import Packet06GenericSectorConjugate
import Packet06PlacedPole
import Packet06AxialOutgoingTransport

/-! Actual axial-rotated physical observation of the same selected-sector pole. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet06AxialObservedPole
open Filter Metric Maxwell ModalAxialRotation Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
  Packet06PlacedKernel Packet06PlacedEquivalence Packet06GenericSectorConjugate Packet06AxialMaterialTransport
open scoped Topology

def pencil (θ : ℝ) (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) : Sector →L[ℂ] Sector :=
  Packet06SectorFamily.compression (conjugate (placed s hs a) (conjugate (Packet06AxialEquivalence.equivalence θ)
    (ComplexConvolutionAnalytic.pencil (coefficient θ (placedCoefficient s a c)) z (R/s+‖a‖))))

theorem pencil_eq (θ : ℝ) (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) :
    pencil θ c R s hs a z = Packet06PlacedSector.pencil c R s hs a z := by
  unfold pencil
  rw [axial_pencil_conjugate θ (placedCoefficient s a c) (R/s+‖a‖)
    (add_nonneg (div_nonneg hR hs.le) (norm_nonneg a)) (Packet06PlacedPole.coefficient_support c R hc s hs a)]
  rfl

def observation (θ : ℝ) (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s)
    (a : Space) (T : ℝ) (z : ℂ) : Sector →L[ℂ] VectorL2 :=
  (Packet06LocalPencil.response (coefficient θ (placedCoefficient s a c)) z (R/s+‖a‖) T).comp
    ((action θ).comp ((placed s hs a).toContinuousLinearMap.comp Sector.subtypeL))

def SimpleObservedPole (θ : ℝ) (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s)
    (a : Space) (z : ℂ) (u : Sector) : Prop :=
  ∃ φ : Sector →L[ℂ] ℂ, φ (deriv (pencil θ c R s hs a) z u) ≠ 0 ∧
    ∀ T : ℝ, R/s+‖a‖ ≤ T →
    ∃ (Q : Sector →L[ℂ] VectorL2) (B : ℂ → Sector →L[ℂ] VectorL2),
      Q ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, Q x = (φ x / φ (deriv (pencil θ c R s hs a) z u)) •
        Packet06LocalPencil.response (coefficient θ (placedCoefficient s a c)) z (R/s+‖a‖) T (action θ (placed s hs a u))) ∧
      Tendsto (fun v => (v-z) • (observation θ c R s hs a T v).comp
        (Ring.inverse (pencil θ c R s hs a v))) (𝓝[≠] z) (𝓝 Q) ∧
      (∀ᶠ v in 𝓝[≠] z, (observation θ c R s hs a T v).comp
        (Ring.inverse (pencil θ c R s hs a v)) = (v-z)⁻¹ • Q + B v)

theorem observation_analyticAt (θ : ℝ) (c : StaticCoefficient.Coefficient) (R s : ℝ) (hs : 0 < s)
    (a : Space) (T : ℝ) (hT : 0 ≤ T+(R/s+‖a‖)) (z : ℂ) :
    AnalyticAt ℂ (observation θ c R s hs a T) z := by
  exact (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip
    ((action θ).comp ((placed s hs a).toContinuousLinearMap.comp Sector.subtypeL))).analyticAt _).comp
      (f := fun v : ℂ => Packet06LocalPencil.response (coefficient θ (placedCoefficient s a c)) v (R/s+‖a‖) T)
      (Packet06LocalPencil.response_analyticAt _ _ T hT z)

theorem certified_observed_pole (θ : ℝ) (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u) :
    SimpleObservedPole θ c R s hs a ((s : ℂ)*z) u := by
  obtain ⟨w,ψ,hC,hk,hψ,hds⟩ := Packet06PlacedSchur.certified_schur c ha hm R hR hc s hs a z u hcert
  let A := pencil θ c R s hs a
  let zp := (s : ℂ)*z
  have hAeq : A = Packet06PlacedSector.pencil c R s hs a := by
    funext v
    exact pencil_eq θ c R hR hc s hs a v
  rw [← hAeq] at hC hk hds
  have hA : AnalyticAt ℂ A zp := by
    rw [hAeq]
    exact Packet06PlacedSchur.pencil_analyticAt c R hR hc s hs a zp
  have hi : Ring.inverse (repair (A zp) w ψ) w=u := repaired_inverse_vector _ u w ψ hC hk hψ
  have hzero : scalar (A zp) w ψ=0 := scalar_zero _ u w ψ hC hk hψ
  have hder := Packet06SchurAnalytic.scalar_hasDerivAt A (deriv A zp) w ψ zp
    hA.differentiableAt.hasDerivAt hC
  let φ := ψ.comp (Ring.inverse (repair (A zp) w ψ))
  have hcross : φ (deriv A zp u) ≠ 0 := by
    rw [hder.deriv,hi] at hds
    exact hds
  obtain ⟨Q,B,_,hB,hform,hlim,hexp⟩ := Packet06SchurPole.simple_inverse_expansion A w ψ zp hA hC hzero hds
  simp only [hi] at hform
  refine ⟨φ,hcross,?_⟩
  intro T hT
  have hS : 0 ≤ R/s+‖a‖ := add_nonneg (div_nonneg hR hs.le) (norm_nonneg a)
  have hObs := observation_analyticAt θ c R s hs a T (by linarith) zp
  obtain ⟨D,hD,he⟩ := Packet06LaurentTransport.observation_expansion
    (fun v => Ring.inverse (A v)) Q B (observation θ c R s hs a T) zp hB hObs hexp
  have hpc := Packet06PlacedPole.coefficient_support c R hc s hs a
  have hrc : ∀ x : Space, x ∉ closedBall 0 (R/s+‖a‖) →
      (coefficient θ (placedCoefficient s a c)).value (VectorFourier.coordinateMap x)=0 := by
    intro x hx
    rw [Packet06AxialMaterialTransport.coefficient_value]
    apply hpc
    simpa [mem_closedBall,dist_zero_right,(rotation (-θ)).norm_map] using hx
  have hker : ComplexConvolutionAnalytic.volumeBlock (coefficient θ (placedCoefficient s a c)) zp
      (R/s+‖a‖) (action θ (placed s hs a u))=0 := by
    rw [Packet06AxialPencilTransport.volume_intertwines θ (placedCoefficient s a c) _ hS hpc,
      Packet06PlacedConjugacy.volume_intertwines c R hR hc s hs a z u]
    obtain ⟨_,_,_,hku,_,_⟩ := hcert
    rw [hku,map_zero,map_zero]
  have hne : action θ (placed s hs a (u : VectorL2)) ≠ 0 := by
    intro heq
    have heq' := congrArg (Packet06AxialEquivalence.equivalence θ).symm heq
    change action (-θ) (action θ (placed s hs a (u : VectorL2))) = action (-θ) 0 at heq'
    rw [Packet06AxialEquivalence.action_inverse,map_zero] at heq'
    have hu0 : (u : VectorL2)=0 := (placed s hs a).injective (heq'.trans (map_zero _).symm)
    have hu' : u=0 := Subtype.ext hu0
    rw [hu',map_zero] at hψ
    exact zero_ne_one hψ
  have hCu : observation θ c R s hs a T zp u ≠ 0 :=
    Packet06Observation.kernel_observation_nonzero _ zp _ T hT _ hrc hker hne
  refine ⟨(observation θ c R s hs a T zp).comp Q,D,?_,hD,?_,?_,he⟩
  · exact Packet06LaurentTransport.observed_residue_nonzero Q (observation θ c R s hs a T zp)
      u φ _ hcross hform hCu (deriv A zp u) hcross
  · exact Packet06LaurentTransport.observed_residue_form Q (observation θ c R s hs a T zp) u φ _ hform
  · exact Packet06LaurentTransport.observation_residue_limit
      (fun v => Ring.inverse (A v)) Q (observation θ c R s hs a T) zp hObs.continuousAt hlim

end OQ14.Packet06AxialObservedPole
#print axioms OQ14.Packet06AxialObservedPole.pencil_eq
#print axioms OQ14.Packet06AxialObservedPole.observation_analyticAt
#print axioms OQ14.Packet06AxialObservedPole.certified_observed_pole
