import Packet06SpherePole
import ModalWeightedResidue
import ModalBoundedContrastIsolation
import Packet06PhysicalPairing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06NormalizedMode
open Complex OQ14.Packet06SectorOperator OQ14.Packet06SectorCrossing
  OQ14.ModalMatching OQ14.ModalWeightedMode
open scoped Topology

def normalizedMode (n : ℝ) (hn : 1 < n) (k : ModalShell.Frequency)
    (f : Amplitudes) (a : ℂ) : Sector := by
  refine ⟨a • weightedMode n hn k f, ?_⟩
  rw [ModalWeightedResidue.residue_eq_numerator, smul_smul]
  exact ModalMeridionalReflection.electricSector.smul_mem _
    (ModalMeridionalReflection.numerator_in_electricSector n hn k.val)

def pairing (U : Sector) : Sector →L[ℂ] ℂ :=
  (ComplexVolumeReciprocity.pairFunctional (U : VectorFourier.VectorL2)).comp Sector.subtypeL

theorem pairing_crossing_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (U : Sector) :
    pairing U (blockDerivative n hn z U) =
      ComplexVolumeReciprocity.pairFunctional (U : VectorFourier.VectorL2)
        (deriv (fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) w 1) z U) := by
  change ComplexVolumeReciprocity.pairFunctional (U : VectorFourier.VectorL2)
      ((blockDerivative n hn z U : Sector) : VectorFourier.VectorL2) = _
  rw [block_derivative_actual]

theorem pairing_left_annihilates (n : ℝ) (hn : 1 < n) (z : ℂ) (U : Sector)
    (hU : block n hn z U = 0) (v : Sector) : pairing U (block n hn z v) = 0 := by
  exact ModalVolumeNormalization.kernel_left_functional n hn z U
    (congrArg Subtype.val hU) v

theorem kernel_generator (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (z : ℂ) (hz : z ≠ 0) (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (U : Sector) (hU : block n hn z U = 0) (hU0 : U ≠ 0)
    (v : Sector) (hv : block n hn z v = 0) : ∃ c : ℂ, v = c • U := by
  obtain ⟨s,hs,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd U).mp hU
  have hs0 : s ≠ 0 := by
    intro h
    apply hU0
    simpa [h] using hs
  obtain ⟨c,hc,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd v).mp hv
  refine ⟨c/s, ?_⟩
  rw [hs, smul_smul, div_mul_cancel₀ c hs0]
  exact hc

/-- The same selected normalized mode has the unit rank-one restricted residue. -/
theorem normalized_residue (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (z : ℂ) (hz : z ≠ 0) (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (U : Sector) (hU : block n hn z U = 0) (hU0 : U ≠ 0)
    (hunit : pairing U (blockDerivative n hn z U) = 1) :
    ∃ (R : Sector →L[ℂ] Sector) (B : ℂ → Sector →L[ℂ] Sector),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧ (∀ v, R v = pairing U v • U) ∧
      Filter.Tendsto (fun w => (w-z) • Ring.inverse (block n hn w)) (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ w in 𝓝[≠] z, Ring.inverse (block n hn w) = (w-z)⁻¹ • R + B w) := by
  obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := Packet06Laurent.simple_inverse_expansion
    (block n hn) (blockDerivative n hn z) z (block_hasDerivAt n hn z) U (pairing U)
    (kernel_generator n hn hna z hz hd U hU hU0)
    (pairing_left_annihilates n hn z U hU) (by rw [hunit]; exact one_ne_zero)
    (inverse_meromorphicAt n hn z) (block_punctured_isUnit n hn z)
    (block_not_isUnit n hn z hz hd)
  refine ⟨R,B,hR,hB,?_,hlim,hexp⟩
  intro v
  simpa only [hunit, div_one] using hform v

/-- The high-Q witness supplied by the established normalization theorem is
unchanged, and its physical pairing gives the actual unit residue. -/
theorem selected_highQ_normalized_residue (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (L Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ (k : ModalShell.Frequency) (f : Amplitudes) (a : ℂ),
      L < k.val.re ∧ k.val.im < 0 ∧ Q < k.val.re / (-2*k.val.im) ∧
      (∀ j : ℕ, ModalAlgebra.tmDet j (n : ℂ) k.val = 0 ↔ j = 1) ∧
      normalizedMode n hn k f a ≠ 0 ∧
      block n hn k.val (normalizedMode n hn k f a) = 0 ∧
      pairing (normalizedMode n hn k f a)
        (blockDerivative n hn k.val (normalizedMode n hn k f a)) = 1 ∧
      (∀ v : Sector, block n hn k.val v = 0 ↔ ∃! c : ℂ,
        v = c • normalizedMode n hn k f a) ∧
      ∃ (R : Sector →L[ℂ] Sector) (B : ℂ → Sector →L[ℂ] Sector),
        R ≠ 0 ∧ AnalyticAt ℂ B k.val ∧
        (∀ v : Sector, R v =
          (∫ x : Maxwell.Space, ∑ i : Fin 3,
            (v : VectorFourier.VectorL2) (VectorFourier.coordinateMap x) i *
              (normalizedMode n hn k f a : VectorFourier.VectorL2)
                (VectorFourier.coordinateMap x) i) • normalizedMode n hn k f a) ∧
        Filter.Tendsto (fun w => (w-k.val) • Ring.inverse (block n hn w))
          (𝓝[≠] k.val) (𝓝 R) ∧
        (∀ᶠ w in 𝓝[≠] k.val, Ring.inverse (block n hn w) = (w-k.val)⁻¹ • R + B w) := by
  obtain ⟨k,f,a,hL,him,hQk,hiso,hs,hU0,hUk,hunit,hmer⟩ :=
    ModalBoundedContrastIsolation.normalized_isolated_poles n hn hna L Q hQ
  let U := normalizedMode n hn k f a
  have hz : k.val ≠ 0 := k.property
  have hd : ModalAlgebra.tmDet 1 (n : ℂ) k.val = 0 := (hiso 1).mpr rfl
  have hU0' : U ≠ 0 := fun h => hU0 (congrArg Subtype.val h)
  have hUk' : block n hn k.val U = 0 := Subtype.ext hUk
  have hunit' : pairing U (blockDerivative n hn k.val U) = 1 := by
    rw [pairing_crossing_actual]
    exact hunit
  obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := normalized_residue n hn hna k.val hz hd U hUk' hU0' hunit'
  refine ⟨k,f,a,hL,him,hQk,hiso,hU0',hUk',hunit',?_,R,B,hR,hB,?_,hlim,hexp⟩
  · intro v
    constructor
    · intro hv
      obtain ⟨c,hc⟩ := kernel_generator n hn hna k.val hz hd U hUk' hU0' v hv
      refine ⟨c,hc,?_⟩
      intro d hd'
      exact (smul_left_injective ℂ hU0') (hd'.symm.trans hc)
    · rintro ⟨c,hc,_⟩
      rw [hc,map_smul,hUk',smul_zero]
  · intro v
    rw [hform]
    change OQ14.KernelReciprocity.vectorPair (v : VectorFourier.VectorL2)
      (U : VectorFourier.VectorL2) • U = _
    rw [Packet06PhysicalPairing.vectorPair_physical]

#print axioms OQ14.Packet06NormalizedMode.pairing_crossing_actual
#print axioms OQ14.Packet06NormalizedMode.pairing_left_annihilates
#print axioms OQ14.Packet06NormalizedMode.kernel_generator
#print axioms OQ14.Packet06NormalizedMode.normalized_residue
#print axioms OQ14.Packet06NormalizedMode.selected_highQ_normalized_residue
end OQ14.Packet06NormalizedMode
