import MaterialMaxwell
import IncidentLocalization
import MagneticLocal
import DynamicVolumeConstants

/-! # Actual small-volume dielectric fields from incident Maxwell fields

The incident datum is constructed from local L2 regularity. The inverse,
polarization, locally L2 spatial fields and their two compact-smooth-test
Maxwell equations are all derived. An outgoing radiation theorem and the
extension to arbitrary support sizes are not asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.SmallVolumeMaxwell

open MeasureTheory Metric OQ14.Maxwell OQ14.MaterialMaxwell

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

theorem continuous_memLp_ball (f : Space → ℂ) (hf : Continuous f) (R : ℝ) :
    MemLp f 2 (volume.restrict (closedBall 0 R)) := by
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Space) R).exists_bound_of_continuousOn hf.continuousOn
  apply MemLp.of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_closedBall] with x hx
  exact hC x hx

theorem locallyIntegrable_of_memLp_ball (f : Space → ℂ)
    (hf : ∀ R : ℝ, MemLp f 2 (volume.restrict (closedBall 0 R))) : LocallyIntegrable f := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Space)
  letI : IsFiniteMeasure (volume.restrict (closedBall (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall 0 R).measure_ne_top
  exact IntegrableOn.mono_set
    ((hf R).integrable (by norm_num : (1 : ENNReal) ≤ 2)) hR

theorem total_electric_memLp_ball (c : Coefficient) (k R T : ℝ) (u : VectorL2)
    (Einc : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hE : ∀ i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (i : Fin 3) :
    MemLp (fun x => MaterialField.total c k u Einc x i) 2 (volume.restrict (closedBall 0 T)) :=
  (hE i).add (MaterialField.scattered_memLp_ball c k R T u hc i)

theorem total_magnetic_memLp_ball (c : Coefficient) (k R T : ℝ) (u : VectorL2)
    (Hinc : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hH : ∀ i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (i : Fin 3) :
    MemLp (fun x => totalMagnetic c k u Hinc x i) 2 (volume.restrict (closedBall 0 T)) :=
  (hH i).add (MagneticLocal.magnetic_memLp_ball k T R (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (DynamicVolume.source_zero c u R hc) (StaticNewton.material_source_ae c u) i)

/-- A concrete inverse and actual local spatial fields, from local incoming
regularity alone. The numerical smallness condition is the proved kernel mass
bound. No global L2 incident field or material field equation is assumed. -/
theorem exists_small_volume_fields (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : 252 * c.bound * k^2 * R^2 < 1)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    ∃ u : VectorL2,
      DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R) ∧
      ‖u‖ ≤ (1 - 252 * c.bound * k^2 * R^2)⁻¹ *
        ‖IncidentLocalization.datum c R Einc hc (hE R)‖ ∧
      TestMaxwell k (dielectric c) (MaterialField.total c k u Einc) (totalMagnetic c k u Hinc) ∧
      (∀ T i, MemLp (fun x => MaterialField.total c k u Einc x i) 2
        (volume.restrict (closedBall 0 T))) ∧
      (∀ T i, MemLp (fun x => totalMagnetic c k u Hinc x i) 2
        (volume.restrict (closedBall 0 T))) := by
  have hs : DynamicVolume.errorBound c k R < 1 := by
    rwa [DynamicVolume.errorBound_explicit]
  let f := IncidentLocalization.datum c R Einc hc (hE R)
  let u := MaterialField.solution c k R f
  have hu := MaterialField.solution_equation c k R hR hs f
  have hn := DynamicVolume.solution_norm_bound c k R hR hs u f hu
  rw [DynamicVolume.errorBound_explicit] at hn
  refine ⟨u, hu, hn, ?_, ?_, ?_⟩
  · exact small_volume_testMaxwell c k R hR hs f Einc Hinc hc
      (IncidentLocalization.datum_actual c R Einc hc (hE R))
      (fun i => locallyIntegrable_of_memLp_ball _ (fun T => hE T i))
      (fun i => locallyIntegrable_of_memLp_ball _ (fun T => hH T i)) hMax
  · exact fun T i => total_electric_memLp_ball c k R T u Einc hc (hE T) i
  · exact fun T i => total_magnetic_memLp_ball c k R T u Hinc hc (hH T) i

theorem classical_incident_exists (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : 252 * c.bound * k^2 * R^2 < 1)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ i, ContDiff ℝ 1 (fun x => Einc x i))
    (hH : ∀ i, ContDiff ℝ 1 (fun x => Hinc x i))
    (hMax : ∀ x, MaxwellAt k 1 1 Einc Hinc x) :
    ∃ u : VectorL2,
      TestMaxwell k (dielectric c) (MaterialField.total c k u Einc) (totalMagnetic c k u Hinc) ∧
      (∀ T i, MemLp (fun x => MaterialField.total c k u Einc x i) 2
        (volume.restrict (closedBall 0 T))) ∧
      (∀ T i, MemLp (fun x => totalMagnetic c k u Hinc x i) 2
        (volume.restrict (closedBall 0 T))) := by
  obtain ⟨u, _, _, hM, hE', hH'⟩ := exists_small_volume_fields c k R hR hsmall hc Einc Hinc
    (fun T i => continuous_memLp_ball _ (hE i).continuous T)
    (fun T i => continuous_memLp_ball _ (hH i).continuous T)
    (classical_vacuum_testMaxwell k Einc Hinc hE hH hMax)
  exact ⟨u, hM, hE', hH'⟩

end OQ14.SmallVolumeMaxwell

#print axioms OQ14.SmallVolumeMaxwell.continuous_memLp_ball
#print axioms OQ14.SmallVolumeMaxwell.locallyIntegrable_of_memLp_ball
#print axioms OQ14.SmallVolumeMaxwell.total_electric_memLp_ball
#print axioms OQ14.SmallVolumeMaxwell.total_magnetic_memLp_ball
#print axioms OQ14.SmallVolumeMaxwell.exists_small_volume_fields
#print axioms OQ14.SmallVolumeMaxwell.classical_incident_exists
