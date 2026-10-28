import ConicalCommonNonzero
import ConicalAngularCoefficient

/-! Actual entire incident fields and local projection systems for one common material. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonEntire
open MeasureTheory Set Metric OQ14.NewtonL2
open scoped Topology SchwartzMap
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def solution (R k : ℝ) (I : ConicalEntireGauge.Incident k) : VectorL2 :=
  ConicalMaterialRunge.solutionOperator (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
    (ConicalEntireGauge.restricted R I)

def source (R k : ℝ) (I : ConicalEntireGauge.Incident k) : Fin 3 → Space → ℂ :=
  DynamicVolume.source (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
    (solution p a center B hB hcontrast ha hsep R k I)

def polarization (R k : ℝ) (I : ConicalEntireGauge.Incident k) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
    (solution p a center B hB hcontrast ha hsep R k I)

def electric (R k : ℝ) (I : ConicalEntireGauge.Incident k) : Maxwell.Field :=
  MaterialField.total (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k
    (solution p a center B hB hcontrast ha hsep R k I) I.E

def magnetic (R k : ℝ) (I : ConicalEntireGauge.Incident k) : Maxwell.Field :=
  MaterialMaxwell.totalMagnetic (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k
    (solution p a center B hB hcontrast ha hsep R k I) I.H

omit [DecidableEq ι] in
theorem source_ae (R k : ℝ) (I : ConicalEntireGauge.Incident k) (j : Fin 3) :
    physicalCoordinate (polarization p a center B hB hcontrast ha hsep R k I) j =ᵐ[volume]
      source p a center B hB hcontrast ha hsep R k I j := StaticNewton.material_source_ae _ _ j

omit [DecidableEq ι] in
theorem source_zero (R k : ℝ) (I : ConicalEntireGauge.Incident k)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R) :
    ∀ j x, x ∉ closedBall (0 : Space) R → source p a center B hB hcontrast ha hsep R k I j x = 0 :=
  DynamicVolume.source_zero _ _ R (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR)

omit [DecidableEq ι] in
theorem maxwell (R k : ℝ) (hR0 : 0 ≤ R)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) :
    MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep))
      (electric p a center B hB hcontrast ha hsep R k I) (magnetic p a center B hB hcontrast ha hsep R k I) := by
  have hc := ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR
  exact MaterialMaxwell.volume_solution_testMaxwell _ k R _ _ I.E I.H hc
    (ConicalMaterialRunge.weighted_actual _ R _ _ hc (ConicalEntireGauge.restricted_ae R I))
    (ConicalMaterialRunge.solution_equation _ k R hR0 hfreq _)
    (fun j => (I.smoothE j).continuous.locallyIntegrable)
    (fun j => (I.smoothH j).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H
      (fun j => (I.smoothE j).of_le (by simp)) (fun j => (I.smoothH j).of_le (by simp)) I.maxwell)

def potential (R k : ℝ) (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) :=
  ConicalCompactPotential.potentialData k R (polarization p a center B hB hcontrast ha hsep R k I)
    (source p a center B hB hcontrast ha hsep R k I) (source_zero p a center B hB hcontrast ha hsep R k I hR)
    (source_ae p a center B hB hcontrast ha hsep R k I)

def centeredPotential (l : ι) (R k : ℝ) (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) :=
  ConicalTranslatedPotential.translated (center l) (potential p a center B hB hcontrast ha hsep R k hR I)

def correction (l : ι) (R k : ℝ) (I : ConicalEntireGauge.Incident k) (x : Space) (j : Fin 3) : ℂ :=
  I.E (x + center l) j + ElectricPotentialDecomposition.correction k (source p a center B hB hcontrast ha hsep R k I) (x + center l) j

omit [DecidableEq ι] in
theorem correction_continuous (l : ι) (R k : ℝ) (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) (j : Fin 3) : Continuous (fun x => correction p a center B hB hcontrast ha hsep l R k I x j) :=
  ((I.smoothE j).continuous.add (ElectricPotentialDecomposition.correction_continuous k R _ _
    (source_zero p a center B hB hcontrast ha hsep R k I hR) (source_ae p a center B hB hcontrast ha hsep R k I) j)).comp
      (continuous_id.add continuous_const)

omit [DecidableEq ι] in
theorem potential_gauss (l : ι) (R k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b ≤ a l)
    (hai : a l < (p l).cutoff.rIn)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) (f : 𝓢(Space, ℂ)) (hf : tsupport (f : Space → ℂ) ⊆ ball (0 : Space) b) :
    (∑ j : Fin 3, ∫ x, (ConicalLocalGauss.epsilon (p l) x : ℂ) *
      ((centeredPotential p a center B hB hcontrast ha hsep l R k hR I).derivative j x +
        correction p a center B hB hcontrast ha hsep l R k I x j) * Maxwell.dcoord f x j) = 0 := by
  have h := ConicalCommonLocal.local_gauss p a center B hB hcontrast ha hsep l b k hb hai hk _ _
    (maxwell p a center B hB hcontrast ha hsep R k hR0 hfreq hR I) f hf
  have he (j : Fin 3) : (∫ x, (ConicalLocalGauss.epsilon (p l) x : ℂ) *
      ((centeredPotential p a center B hB hcontrast ha hsep l R k hR I).derivative j x +
        correction p a center B hB hcontrast ha hsep l R k I x j) * Maxwell.dcoord f x j) =
      ∫ x, (ConicalLocalGauss.epsilon (p l) x : ℂ) *
        electric p a center B hB hcontrast ha hsep R k I (center l+x) j * Maxwell.dcoord f x j := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp [centeredPotential, ConicalTranslatedPotential.translated, potential, ConicalCompactPotential.potentialData,
      correction, electric, MaterialField.total, MaterialField.scattered, polarization, source]
    rw [add_comm x (center l)]
    ring
  simpa only [he] using h

def system (l : ι) (R k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b ≤ a l)
    (hai : a l < (p l).cutoff.rIn)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) : ConicalProjectionData.System (p l) b :=
  ConicalProjectionLocalization.ofPotential (p l) b (hb.trans_lt hai)
    (centeredPotential p a center B hB hcontrast ha hsep l R k hR I)
    (correction p a center B hB hcontrast ha hsep l R k I)
    (correction_continuous p a center B hB hcontrast ha hsep l R k hR I)
    (potential_gauss p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR I)

omit [DecidableEq ι] in
theorem system_actual (l : ι) (R k b : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b ≤ a l)
    (hai : a l < (p l).cutoff.rIn)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) (j : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) b →
      ConicalProjectionData.totalCoordinate (system p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR I) j x =
        electric p a center B hB hcontrast ha hsep R k I (center l+x) j := by
  have h := ConicalProjectionLocalization.total_inner (p l) b (hb.trans_lt hai)
    (centeredPotential p a center B hB hcontrast ha hsep l R k hR I)
    (correction p a center B hB hcontrast ha hsep l R k I)
    (correction_continuous p a center B hB hcontrast ha hsep l R k hR I)
    (potential_gauss p a center B hB hcontrast ha hsep l R k b hR0 hk hb hai hfreq hR I) j
  filter_upwards [h] with x hx hxb
  dsimp only [system]
  rw [hx hxb]
  dsimp [centeredPotential, ConicalTranslatedPotential.translated, potential, ConicalCompactPotential.potentialData,
    correction, electric, MaterialField.total, MaterialField.scattered, polarization, source]
  rw [add_comm x (center l)]
  ring

end OQ14.ConicalCommonEntire
#print axioms OQ14.ConicalCommonEntire.source_ae
#print axioms OQ14.ConicalCommonEntire.source_zero
#print axioms OQ14.ConicalCommonEntire.maxwell
#print axioms OQ14.ConicalCommonEntire.correction_continuous
#print axioms OQ14.ConicalCommonEntire.potential_gauss
#print axioms OQ14.ConicalCommonEntire.system
#print axioms OQ14.ConicalCommonEntire.system_actual
