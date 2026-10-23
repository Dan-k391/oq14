import ConicalSeparatedIllumination
import ConicalSeparatedHotspot
import ConicalTipRounding

/-! Literal rounded separated materials and their convergent restricted volume responses. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalSeparatedRounding
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalStaticVolume OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space

def material (p : Data) (a : ℝ) (n : ℕ) : StaticCoefficient.Coefficient :=
  ConicalTipRounding.rounded (ConicalSeparatedSource.material p a) n

def permittivity (p : Data) (a : ℝ) (n : ℕ) (x : Space) : ℝ :=
  1+(material p a n).value (VectorFourier.coordinateMap x)

def field (p : Data) (a k : ℝ) (n : ℕ) : VectorFourier.VectorL2 :=
  MaterialVolumeLimit.volumeField (material p a n) k a (ConicalSeparatedDynamic.incident p a k)

def ballField (p : Data) (a k : ℝ) (n : ℕ) : BallL2 a := ConicalBallRestriction.vector a (field p a k n)

theorem material_bound (p : Data) (a : ℝ) (n : ℕ) : (material p a n).bound=p.contrast := rfl

theorem common_support (p : Data) (a : ℝ) (n : ℕ) (x : Space)
    (hx : x ∉ closedBall (0 : Space) a) : (material p a n).value (VectorFourier.coordinateMap x)=0 := by
  rw [material,ConicalTipRounding.rounded_spatial,ConicalSeparatedSource.material_compact p a x hx,mul_zero]

theorem permittivity_bounds (p : Data) (a : ℝ) (n : ℕ) (x : Space) :
    permittivity p a n x ∈ Icc (1 : ℝ) (1+p.contrast) := by
  have h0 := (material p a n).nonnegative (VectorFourier.coordinateMap x)
  have h1 := (material p a n).bounded (VectorFourier.coordinateMap x)
  change (material p a n).value (VectorFourier.coordinateMap x) ≤ p.contrast at h1
  constructor <;> unfold permittivity <;> linarith

theorem permittivity_one_inner (p : Data) (a : ℝ) (n : ℕ) (x : Space)
    (hx : ‖x‖ ≤ ConicalTipRounding.radius n) : permittivity p a n x=1 := by
  simp only [permittivity,material,ConicalTipRounding.rounded_zero_inner _ n x hx,add_zero]

theorem permittivity_smooth_near_tip (p : Data) (a : ℝ) (n : ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (permittivity p a n) (ball (0 : Space) (ConicalTipRounding.radius n)) :=
  contDiffOn_const.add (ConicalTipRounding.rounded_smooth_near_tip (ConicalSeparatedSource.material p a) n)

theorem material_tendsto (p : Data) (a : ℝ) :
    ∀ᵐ ξ : StaticCoefficient.Space, Tendsto (fun n => (material p a n).value ξ) atTop
      (𝓝 ((ConicalSeparatedSource.material p a).value ξ)) :=
  ConicalTipRounding.rounded_ae_tendsto (ConicalSeparatedSource.material p a)

theorem field_tendsto (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) :
    Tendsto (field p a k) atTop (𝓝 (ConicalSeparatedDynamic.field p a k)) :=
  MaterialVolumeLimit.volumeField_tendsto (material p a) (ConicalSeparatedSource.material p a)
    p.contrast k a ha (fun _ => le_rfl) le_rfl (material_tendsto p a) hk (ConicalSeparatedDynamic.incident p a k)

theorem ballField_tendsto (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) :
    Tendsto (ballField p a k) atTop
      (𝓝 (ConicalBallRestriction.vector a (ConicalSeparatedDynamic.field p a k))) :=
  (ConicalBallRestriction.vector a).continuous.tendsto _ |>.comp (field_tendsto p a k ha hk)

def boundedCoordinate (a R M : ℝ) (i : Fin 3) : Set (BallL2 a) :=
  {g | ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R), ‖g i x‖ ≤ M}

theorem boundedCoordinate_isClosed (a R M : ℝ) (i : Fin 3) (hRR : R ≤ a) :
    IsClosed (boundedCoordinate a R M i) := by
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) a :=
    (ball_subset_ball hRR).trans ball_subset_closedBall
  have he : boundedCoordinate a R M i=(fun g : BallL2 a => g i) ⁻¹'
      L2PeakPreservation.boundedOn (μ := volume.restrict (closedBall (0 : Space) a)) (ball (0 : Space) R) M := by
    ext g
    simp only [boundedCoordinate,mem_setOf_eq,mem_preimage,L2PeakPreservation.boundedOn,
      Measure.restrict_restrict_of_subset hs]
  rw [he]
  exact (L2PeakPreservation.isClosed_boundedOn (ball (0 : Space) R) M).preimage
    (PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 3 => ScalarBall a) i).continuous

theorem sharp_coordinate_unbounded (p : Data) (a k R : ℝ) (hai : a < p.cutoff.rIn) (hRR : R ≤ a)
    (hu : ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (0 : Space) R),
      ‖ConicalSeparatedMaxwell.electric p a k x‖ ≤ M) :
    ∃ i : Fin 3, ¬∃ M : ℝ,
      ConicalBallRestriction.vector a (ConicalSeparatedDynamic.field p a k) ∈ boundedCoordinate a R M i := by
  obtain ⟨i,hi⟩ := ConicalVolumePeaks.coordinate_unbounded _ _ hu
  refine ⟨i,?_⟩
  rintro ⟨M,hM⟩
  apply hi
  refine ⟨M,?_⟩
  have hs : ball (0 : Space) R ⊆ closedBall (0 : Space) a :=
    (ball_subset_ball hRR).trans ball_subset_closedBall
  filter_upwards [hM,
    ae_restrict_of_ae_restrict_of_subset hs (ConicalBallRestriction.vector_ae a (ConicalSeparatedDynamic.field p a k) i),
    ae_restrict_of_ae_restrict_of_subset hs (ConicalSeparatedMaxwell.field_ae p a k hai i)] with x hm hr he
  rwa [hr,he] at hm

theorem eventually_avoids_bound (p : Data) (a k R : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius p.contrast a) (hRR : R ≤ a)
    (i : Fin 3) (hi : ¬∃ M : ℝ,
      ConicalBallRestriction.vector a (ConicalSeparatedDynamic.field p a k) ∈ boundedCoordinate a R M i) (M : ℝ) :
    ∀ᶠ n : ℕ in atTop, ballField p a k n ∉ boundedCoordinate a R M i := by
  have hn : ConicalBallRestriction.vector a (ConicalSeparatedDynamic.field p a k) ∉ boundedCoordinate a R M i :=
    fun h => hi ⟨M,h⟩
  exact (ballField_tendsto p a k ha hk).eventually ((boundedCoordinate_isClosed a R M i hRR).isOpen_compl.mem_nhds hn)

end OQ14.ConicalSeparatedRounding

#print axioms OQ14.ConicalSeparatedRounding.material_bound
#print axioms OQ14.ConicalSeparatedRounding.common_support
#print axioms OQ14.ConicalSeparatedRounding.permittivity_bounds
#print axioms OQ14.ConicalSeparatedRounding.permittivity_one_inner
#print axioms OQ14.ConicalSeparatedRounding.permittivity_smooth_near_tip
#print axioms OQ14.ConicalSeparatedRounding.material_tendsto
#print axioms OQ14.ConicalSeparatedRounding.field_tendsto
#print axioms OQ14.ConicalSeparatedRounding.ballField_tendsto
#print axioms OQ14.ConicalSeparatedRounding.boundedCoordinate_isClosed
#print axioms OQ14.ConicalSeparatedRounding.sharp_coordinate_unbounded
#print axioms OQ14.ConicalSeparatedRounding.eventually_avoids_bound
