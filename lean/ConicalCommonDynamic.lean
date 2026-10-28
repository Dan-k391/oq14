import ConicalCommonBaseline
import ConicalSeparatedDynamic

/-! The common material's actual separated-source responses converge to the translated static fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonDynamic
open MeasureTheory Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def incident (i : ι) (R T k : ℝ) : VectorL2 :=
  -(newtonOperator + DynamicConvolution.operator k (R + T)) (ConicalCommonBaseline.forcing p a center i)

def weightedForcing (i : ι) (R T k : ℝ) : VectorL2 :=
  StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
    (incident p a center i R T k)

def solution (i : ι) (R T k : ℝ) : VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R)
    (weightedForcing p a center B hB hcontrast ha hsep i R T k)

def field (i : ι) (R T k : ℝ) : VectorL2 :=
  MaterialVolumeLimit.volumeField (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) k R
    (incident p a center i R T k)

omit [Fintype ι] [DecidableEq ι] in
theorem incident_tendsto (i : ι) (R T : ℝ) (hRT : 0 ≤ R + T) :
    Tendsto (incident p a center i R T) (𝓝 0)
      (𝓝 (-newtonOperator (ConicalCommonBaseline.forcing p a center i))) := by
  have ho := ConicalSeparatedDynamic.remainder_tendsto (R + T) hRT
  have hresp : Tendsto (fun k : ℝ => newtonOperator + DynamicConvolution.operator k (R + T))
      (𝓝 0) (𝓝 newtonOperator) := by simpa only [add_zero] using tendsto_const_nhds.add ho
  have h := isBoundedBilinearMap_apply.continuous.tendsto
    (newtonOperator, ConicalCommonBaseline.forcing p a center i) |>.comp
      (hresp.prodMk_nhds tendsto_const_nhds)
  simpa only [incident] using h.neg

omit [DecidableEq ι] in
theorem solution_tendsto (i : ι) (R T : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    Tendsto (solution p a center B hB hcontrast ha hsep i R T) (𝓝 0)
      (𝓝 (ConicalCommonBaseline.weighted p a center B hB hcontrast ha hsep i)) := by
  have hf := ((StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)).continuous.tendsto _).comp
    (incident_tendsto p a center i R T hRT)
  have h := isBoundedBilinearMap_apply.continuous.tendsto
    (Ring.inverse (StaticNewton.volumeBlock (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)),
      StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
        (-newtonOperator (ConicalCommonBaseline.forcing p a center i))) |>.comp
      ((DynamicStaticLimit.inverse_tendsto (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R hR).prodMk_nhds hf)
  simpa only [solution, weightedForcing, ConicalCommonBaseline.static_inverse] using h

omit [DecidableEq ι] in
theorem field_weighted (i : ι) (R T k : ℝ) (hR : 0 ≤ R)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R) :
    StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)
      (field p a center B hB hcontrast ha hsep i R T k) = solution p a center B hB hcontrast ha hsep i R T k :=
  MaterialVolumeLimit.volumeField_weighted _ k R hR hk _

omit [DecidableEq ι] in
theorem field_tendsto (i : ι) (R T : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    Tendsto (field p a center B hB hcontrast ha hsep i R T) (𝓝 0)
      (𝓝 (ConicalCommonBaseline.electric p center i)) := by
  have hresp : Tendsto (fun k : ℝ => newtonOperator + DynamicConvolution.operator k (2*R))
      (𝓝 0) (𝓝 newtonOperator) := by
    simpa only [add_zero] using tendsto_const_nhds.add (ConicalSeparatedDynamic.remainder_tendsto (2*R) (by linarith))
  have hsource := ((StaticCoefficient.sqrtMultiplier (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep)).continuous.tendsto _).comp
    (solution_tendsto p a center B hB hcontrast ha hsep i R T hR hRT)
  have hscatter := isBoundedBilinearMap_apply.continuous.tendsto
    (newtonOperator, ConicalCommonBaseline.materialSource p a center B hB hcontrast ha hsep i) |>.comp
      (hresp.prodMk_nhds hsource)
  have ht := (incident_tendsto p a center i R T hRT).add hscatter
  have he : -newtonOperator (ConicalCommonBaseline.forcing p a center i) +
      newtonOperator (ConicalCommonBaseline.materialSource p a center B hB hcontrast ha hsep i) =
      ConicalCommonBaseline.electric p center i := by
    have h := ConicalCommonBaseline.static_field_equation p a center B hB hcontrast ha hsep i
    rw [← h]
    abel
  simpa only [field, MaterialVolumeLimit.volumeField, MaterialVolumeLimit.weightedSolution,
    solution, weightedForcing, he] using ht

omit [Fintype ι] [DecidableEq ι] in
theorem incident_ae (i : ι) (R T k : ℝ)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : a i ≤ (p i).cutoff.rOut) (j : Fin 3) :
    physicalCoordinate (incident p a center i R T k) j =ᵐ[volume.restrict (closedBall (0 : Space) R)]
      fun x => -FieldResponse.electric k (ConicalCommonBaseline.forcing p a center i)
        (ConicalCommonMaterial.source p a center i) x j := by
  have he := LocalVolumeResponse.electric_ae_on_ball k R T (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (fun t => ConicalCommonBaseline.source_integrable p a center i t T hT hai)
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · hai)
    (ConicalCommonBaseline.source_ae p a center i) j
  simp only [incident, physicalCoordinate_neg]
  filter_upwards [he, ae_restrict_of_ae (Lp.coeFn_neg
    (physicalCoordinate ((newtonOperator + DynamicConvolution.operator k (R+T))
      (ConicalCommonBaseline.forcing p a center i)) j))] with x he hn
  rw [hn]
  simp only [Pi.neg_apply]
  congr 1

omit [DecidableEq ι] in
theorem field_restricted_tendsto (i : ι) (R T S : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    Tendsto (fun k => ConicalBallRestriction.vector S (field p a center B hB hcontrast ha hsep i R T k))
      (𝓝 0) (𝓝 (ConicalBallRestriction.vector S (ConicalCommonBaseline.electric p center i))) :=
  ((ConicalBallRestriction.vector S).continuous.tendsto _).comp
    (field_tendsto p a center B hB hcontrast ha hsep i R T hR hRT)

omit [DecidableEq ι] in
theorem tip_component_tendsto (i : ι) (j : Fin 3) (R T S : ℝ) (hR : 0 ≤ R) (hRT : 0 ≤ R + T) :
    Tendsto (fun k => ConicalBallRestriction.scalar S
      (StaticBallTranslation.scalar (-center i) (physicalCoordinate (field p a center B hB hcontrast ha hsep i R T k) j)))
      (𝓝 0) (𝓝 (ConicalBallRestriction.scalar S (StaticBallTranslation.scalar (-center i)
        (physicalCoordinate (ConicalCommonBaseline.electric p center i) j)))) := by
  exact ((ConicalBallRestriction.scalar S).continuous.tendsto _).comp
    (((StaticBallTranslation.scalar (-center i)).continuous.tendsto _).comp
      (((DynamicConvolution.component j).continuous.tendsto _).comp
        (field_tendsto p a center B hB hcontrast ha hsep i R T hR hRT)))

end OQ14.ConicalCommonDynamic

#print axioms OQ14.ConicalCommonDynamic.incident_tendsto
#print axioms OQ14.ConicalCommonDynamic.solution_tendsto
#print axioms OQ14.ConicalCommonDynamic.field_weighted
#print axioms OQ14.ConicalCommonDynamic.field_tendsto
#print axioms OQ14.ConicalCommonDynamic.incident_ae
#print axioms OQ14.ConicalCommonDynamic.field_restricted_tendsto
#print axioms OQ14.ConicalCommonDynamic.tip_component_tendsto
