import ConicalDynamicHotspot
import MaterialVolumeLimit
import L2PeakPreservation

/-! Physical coordinate peaks of actual conical volume solutions under material convergence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalVolumePeaks
open MeasureTheory Set Metric Filter OQ14.ConicalStaticVolume
open scoped Topology
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def physicalCoordinateCLM (i : Fin 3) : VectorL2 →L[ℂ] FourierL2.ScalarL2 :=
  VectorFourier.scalarCoordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (VectorFourier.coordinate i)

theorem volumeField_eq (p : Data) (k : ℝ) :
    MaterialVolumeLimit.volumeField (coefficient p) k p.cutoff.rOut
      (ConicalDynamicVolume.incident p k)=ConicalDynamicVolume.field p k := by
  simp only [MaterialVolumeLimit.volumeField,MaterialVolumeLimit.weightedSolution,
    ConicalDynamicVolume.incident,ConicalDynamicVolume.field,ConicalDynamicVolume.totalSource,
    ConicalDynamicVolume.solution,ConicalDynamicVolume.forcing,ConicalDynamicVolume.response,map_sub]
  abel

theorem coordinate_unbounded (F : Space → Maxwell.Vector) (S : Set Space)
    (hu : ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict S, ‖F x‖ ≤ M) :
    ∃ i : Fin 3, ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict S, ‖F x i‖ ≤ M := by
  classical
  by_contra hn
  push_neg at hn
  choose M hM using hn
  apply hu
  refine ⟨∑ i : Fin 3, |M i|,?_⟩
  filter_upwards [ae_all_iff.mpr hM] with x hx
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (M i)))).mpr
  intro i
  exact (hx i).trans ((le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (M j)) (Finset.mem_univ i)))

theorem coordinate_limit_unbounded (p : Data) (k R : ℝ) (hRR : R ≤ p.cutoff.rIn)
    (hu : ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalSpatialMaxwell.electric p k x‖ ≤ M) :
    ∃ i : Fin 3, ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖NewtonL2.physicalCoordinate (ConicalDynamicVolume.field p k) i x‖ ≤ M := by
  obtain ⟨i,hi⟩ := coordinate_unbounded _ _ hu
  refine ⟨i,?_⟩
  rintro ⟨M,hM⟩
  apply hi
  refine ⟨M,?_⟩
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) p.cutoff.rOut :=
    (ball_subset_ball (hRR.trans p.cutoff.rIn_lt_rOut.le)).trans ball_subset_closedBall
  filter_upwards [hM,ae_restrict_of_ae_restrict_of_subset hs (ConicalSpatialMaxwell.field_ae p k i)] with x hx he
  rwa [he] at hx

theorem eventually_positive_physical_peaks (p : Data) (hν : p.exponent < 1)
    (c : ℕ → StaticCoefficient.Coefficient) (D : ℝ)
    (hb : ∀ n, (c n).bound ≤ D) (hb₀ : p.contrast ≤ D)
    (ha : ∀ᵐ x : StaticCoefficient.Space,
      Tendsto (fun n => (c n).value x) atTop (𝓝 ((coefficient p).value x))) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ MaterialVolumeLimit.commonRadius D p.cutoff.rOut ∧
      ∀ k : ℝ, 0 < k → k < δ → ∀ R : ℝ, 0 < R → R ≤ p.cutoff.rIn →
      ∃ i : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
        0 < (volume.restrict (ball (0 : Space) R))
          {x | M < ‖NewtonL2.physicalCoordinate
            (MaterialVolumeLimit.volumeField (c n) k p.cutoff.rOut
              (ConicalDynamicVolume.incident p k)) i x‖} := by
  obtain ⟨δ,hδ,hu⟩ := ConicalEssentialUnbounded.positive_frequency_electric_not_essentially_bounded p hν
  have hD : 0 ≤ D := p.contrast_nonnegative.trans hb₀
  refine ⟨min δ (MaterialVolumeLimit.commonRadius D p.cutoff.rOut),
    lt_min hδ (MaterialVolumeLimit.commonRadius_positive _ _ hD),min_le_right _ _,?_⟩
  intro k hk hkd R hR hRR
  obtain ⟨i,hi⟩ := coordinate_limit_unbounded p k R hRR (hu k hk (hkd.trans_le (min_le_left _ _)) R hR hRR)
  refine ⟨i,?_⟩
  have hfreq : |k| ≤ MaterialVolumeLimit.commonRadius D p.cutoff.rOut := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  have hf := MaterialVolumeLimit.volumeField_tendsto c (coefficient p) D k p.cutoff.rOut
    p.cutoff.rOut_pos.le hb hb₀ ha hfreq (ConicalDynamicVolume.incident p k)
  rw [volumeField_eq] at hf
  have hcoord := (physicalCoordinateCLM i).continuous.tendsto _ |>.comp hf
  exact L2PeakPreservation.eventually_positive_superlevel (ball (0 : Space) R) _ _ hcoord hi

end OQ14.ConicalVolumePeaks

#print axioms OQ14.ConicalVolumePeaks.volumeField_eq
#print axioms OQ14.ConicalVolumePeaks.coordinate_unbounded
#print axioms OQ14.ConicalVolumePeaks.coordinate_limit_unbounded
#print axioms OQ14.ConicalVolumePeaks.eventually_positive_physical_peaks
