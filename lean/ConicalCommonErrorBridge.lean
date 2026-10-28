import ConicalCommonIncidentError
import CommonUnionTarget
import SourceFreeOpenResponse

/-! Exact tip-centered identification of the actual common-material witness incident field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalCommonErrorBridge
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

omit [Fintype ι] in
include ha hsep in
theorem incident_centered_ae (i : ι) (R T k : ℝ)
    (hR : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hT : ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) T)
    (hai : ∀ j, a j < (p j).cutoff.rIn) (j : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (0 : Space) (a i) →
      physicalCoordinate (ConicalCommonDynamic.incident p a center i R T k) j (x+center i) =
        -ExteriorContinuity.electric k (ConicalSeparatedSource.physicalSource (p i) (a i)) x j := by
  have hsource : ∀ j y, y ∈ ball (center i) (a i) → ConicalCommonMaterial.source p a center i j y = 0 := by
    intro j y hy
    exact ConicalCommonMaterial.source_zero_material p a center ha hsep hai i i j y (ball_subset_closedBall hy)
  have he := SourceFreeOpenResponse.electric_ae k (ConicalCommonBaseline.forcing p a center i)
    (ConicalCommonMaterial.source p a center i)
    (fun j => ConicalCommonBaseline.source_integrable p a center i j T hT (ha i))
    (ConicalCommonBaseline.source_ae p a center i) T
    (ConicalCommonMaterial.source_zero_global_outer p a center i · T hT · · (ha i))
    (ball (center i) (a i)) isOpen_ball hsource
  have hi := (ae_restrict_iff' measurableSet_closedBall).mp
    (ConicalCommonDynamic.incident_ae p a center i R T k hT (ha i) j)
  have hshift := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae (he.and hi)
  filter_upwards [hshift] with x hx hxball
  have hm : x+center i ∈ ball (center i) (a i) := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hxball
  have hmem := hR (ConicalCommonMaterial.material_subset_outer p a center ha i (ball_subset_closedBall hm))
  rw [hx.2 hmem, congrFun (hx.1 hm) j]
  change -ExteriorContinuity.electric k (fun t y => ConicalSeparatedSource.physicalSource (p i) (a i) t (y-center i)) (x+center i) j = _
  rw [ConicalCommonExteriorTranslation.electric_translate]

end OQ14.ConicalCommonErrorBridge
#print axioms OQ14.ConicalCommonErrorBridge.incident_centered_ae
