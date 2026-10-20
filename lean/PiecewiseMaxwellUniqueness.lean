import RegionalMaxwellContinuation
import MaterialCellGraph
import HomogeneousVolumeUniqueness
import MaxwellExteriorRellich
import VolumeAlternative

/-! # Global Maxwell volume uniqueness from actual material-cell geometry

The partition data concerns only the coefficient and actual open subsets of
space. The field propagation step is proved from Maxwell, and exterior zero
for homogeneous volume solutions is supplied by the actual Rellich theorem.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.PiecewiseMaxwellUniqueness

open MeasureTheory Filter Metric Set OQ14.Maxwell
  OQ14.RegionalMaxwellContinuation OQ14.MaterialCellGraph

structure Partition (ι : Type*) (ε : Space → ℝ) where
  cell : ι → Set Space
  region_open : ∀ i, IsOpen (cell i)
  region_preconnected : ∀ i, IsPreconnected (cell i)
  value : ι → ℝ
  positive : ∀ i, 0 < value i
  constant_on : ∀ i, ∀ᵐ x : Space, x ∈ cell i → ε x = value i
  cover : ∀ᵐ x : Space, ∃ i, x ∈ cell i
  reachable : ∀ i j, Relation.ReflTransGen (fun i j => Bridge (cell i) (cell j)) i j

theorem electric_zero_of_partition {ι : Type*} (k : ℝ) (hk : k ≠ 0)
    (ε : Space → ℝ) (p : Partition ι ε) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (i₀ : ι) (c₀ : Space) (hc₀ : c₀ ∈ p.cell i₀)
    (hz : ∃ r : ℝ, 0 < r ∧ E =ᵐ[volume.restrict (ball c₀ r)] 0) :
    E =ᵐ[volume] 0 := by
  have hi := electric_zero_on_weighted_region k (p.value i₀) hk (p.positive i₀)
    ε (p.cell i₀) (p.region_open i₀) (p.region_preconnected i₀) E H hM hE
    (weight_equality_on_constant_region ε (p.value i₀) (p.cell i₀) E
      (p.constant_on i₀)) c₀ hc₀ hz
  apply ae_zero_of_reachable_open_cover p.cell p.region_open E _ i₀ hi
    (p.reachable i₀) p.cover
  intro i j hb hzi
  obtain ⟨B,hB,hBc,hcover,hBi,hBj⟩ := hb
  exact electric_zero_across_interface k (p.value j) hk (p.positive j) ε E H hM hE
    (p.cell i) (p.cell j) B (p.region_open i) (p.region_open j)
    (p.region_preconnected j) hB hBc.isPreconnected hcover hBi hBj (p.constant_on j) hzi

theorem homogeneous_electric_zero {ι : Type*} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (MaterialMaxwell.dielectric c))
    (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖)
    (u : VectorFourier.VectorL2) (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    HomogeneousVolumePower.electric c k R u =ᵐ[volume] 0 := by
  let Ω : Set Space := {x | R < ‖x‖}
  have hΩ : IsOpen Ω := isOpen_lt continuous_const continuous_norm
  have hzero : HomogeneousVolumePower.electric c k R u =ᵐ[volume.restrict Ω] 0 := by
    apply (ae_restrict_iff' hΩ.measurableSet).mpr
    exact Eventually.of_forall (fun x hx =>
      (MaxwellExteriorRellich.homogeneous_exterior_zero c k hk R hR u hc hsol x hx).1)
  exact electric_zero_of_partition k (ne_of_gt hk) (MaterialMaxwell.dielectric c) p
    (HomogeneousVolumePower.electric c k R u) (HomogeneousVolumePower.magnetic c k u)
    (HomogeneousVolumePower.homogeneous_testMaxwell c k R u hc hsol)
    (HomogeneousVolumeUniqueness.electric_locallyIntegrable c k R u hc) i₀ x₀ hx₀
    (zero_germ_of_open _ Ω hΩ hzero x₀ hout)

theorem homogeneous_unknown_zero {ι : Type*} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (MaterialMaxwell.dielectric c))
    (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖)
    (u : VectorFourier.VectorL2) (hsol : DynamicVolume.volumeBlock c k R u = 0) : u = 0 :=
  HomogeneousVolumeUniqueness.unknown_zero_of_electric_zero c k R u hc hsol
    (homogeneous_electric_zero c k hk R hR hc p i₀ x₀ hx₀ hout u hsol)

theorem volumeBlock_isUnit {ι : Type*} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (MaterialMaxwell.dielectric c))
    (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖) :
    IsUnit (DynamicVolume.volumeBlock c k R) :=
  VolumeAlternative.volumeBlock_isUnit c k R hc
    (homogeneous_unknown_zero c k hk R hR hc p i₀ x₀ hx₀ hout)

theorem existsUnique_solution {ι : Type*} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (MaterialMaxwell.dielectric c))
    (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖)
    (f : VectorFourier.VectorL2) :
    ∃! u : VectorFourier.VectorL2, DynamicVolume.volumeBlock c k R u = f :=
  VolumeAlternative.existsUnique_solution c k R hc
    (homogeneous_unknown_zero c k hk R hR hc p i₀ x₀ hx₀ hout) f

end OQ14.PiecewiseMaxwellUniqueness

#print axioms OQ14.PiecewiseMaxwellUniqueness.electric_zero_of_partition
#print axioms OQ14.PiecewiseMaxwellUniqueness.homogeneous_electric_zero
#print axioms OQ14.PiecewiseMaxwellUniqueness.homogeneous_unknown_zero
#print axioms OQ14.PiecewiseMaxwellUniqueness.volumeBlock_isUnit
#print axioms OQ14.PiecewiseMaxwellUniqueness.existsUnique_solution
