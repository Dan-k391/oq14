import FiniteRadialPartition
import PiecewiseScattering
import MaxwellZeroField

/-! # Actual uniqueness and scattering for arbitrary finite concentric layers

All connectivity, interface bridges, coverage and reachability are derived
from the strictly ordered positive radii. No abstract partition certificate
or homogeneous uniqueness premise is required by these conclusions.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RadialMaxwellUniqueness

open MeasureTheory Metric OQ14.Maxwell OQ14.FiniteRadialPartition

theorem homogeneous_electric_zero {n : ℕ} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ i, 0 < r i)
    (v : Fin (n+2) → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → MaterialMaxwell.dielectric c x = v i)
    (u : VectorFourier.VectorL2) (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    HomogeneousVolumePower.electric c k R u =ᵐ[volume] 0 := by
  obtain ⟨x,hx,ho⟩ := exists_exterior_seed r hm hp R
  exact PiecewiseMaxwellUniqueness.homogeneous_electric_zero c k hk R hR hc
    (partition r hm hp (MaterialMaxwell.dielectric c) v hv hε)
    (Fin.last (n+1)) x hx ho u hsol

theorem homogeneous_fields_zero {n : ℕ} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ i, 0 < r i)
    (v : Fin (n+2) → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → MaterialMaxwell.dielectric c x = v i)
    (u : VectorFourier.VectorL2) (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    (HomogeneousVolumePower.electric c k R u =ᵐ[volume] 0) ∧
      (HomogeneousVolumePower.magnetic c k u =ᵐ[volume] 0) := by
  have hE := homogeneous_electric_zero c k hk R hR hc r hm hp v hv hε u hsol
  exact ⟨hE,MaxwellZeroField.magnetic_zero_of_electric_zero k (ne_of_gt hk)
    (MaterialMaxwell.dielectric c) _ _
    (HomogeneousVolumePower.homogeneous_testMaxwell c k R u hc hsol)
    (HomogeneousVolumeUniqueness.magnetic_locallyIntegrable c k R u hc) hE⟩

theorem homogeneous_unknown_zero {n : ℕ} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ i, 0 < r i)
    (v : Fin (n+2) → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → MaterialMaxwell.dielectric c x = v i)
    (u : VectorFourier.VectorL2) (hsol : DynamicVolume.volumeBlock c k R u = 0) : u = 0 :=
  HomogeneousVolumeUniqueness.unknown_zero_of_electric_zero c k R u hc hsol
    (homogeneous_electric_zero c k hk R hR hc r hm hp v hv hε u hsol)

theorem volumeBlock_isUnit {n : ℕ} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ i, 0 < r i)
    (v : Fin (n+2) → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → MaterialMaxwell.dielectric c x = v i) :
    IsUnit (DynamicVolume.volumeBlock c k R) :=
  VolumeAlternative.volumeBlock_isUnit c k R hc
    (homogeneous_unknown_zero c k hk R hR hc r hm hp v hv hε)

theorem existsUnique_solution {n : ℕ} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ i, 0 < r i)
    (v : Fin (n+2) → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → MaterialMaxwell.dielectric c x = v i)
    (f : VectorFourier.VectorL2) :
    ∃! u : VectorFourier.VectorL2, DynamicVolume.volumeBlock c k R u = f :=
  VolumeAlternative.existsUnique_solution c k R hc
    (homogeneous_unknown_zero c k hk R hR hc r hm hp v hv hε) f

theorem classical_incident_exists {n : ℕ} (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (r : Fin (n+1) → ℝ) (hm : StrictMono r) (hp : ∀ i, 0 < r i)
    (v : Fin (n+2) → ℝ) (hv : ∀ i, 0 < v i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ cell r i → MaterialMaxwell.dielectric c x = v i)
    (Einc Hinc : Field) (hE : ∀ i, ContDiff ℝ 1 (fun x => Einc x i))
    (hH : ∀ i, ContDiff ℝ 1 (fun x => Hinc x i))
    (hMax : ∀ x, MaxwellAt k 1 1 Einc Hinc x) :
    ∃ u : VectorFourier.VectorL2, PiecewiseScattering.PhysicalFields c k R Einc Hinc u := by
  obtain ⟨x,hx,ho⟩ := exists_exterior_seed r hm hp R
  exact PiecewiseScattering.classical_incident_exists c k hk R hR hc
    (partition r hm hp (MaterialMaxwell.dielectric c) v hv hε)
    (Fin.last (n+1)) x hx ho Einc Hinc hE hH hMax

end OQ14.RadialMaxwellUniqueness

#print axioms OQ14.RadialMaxwellUniqueness.homogeneous_electric_zero
#print axioms OQ14.RadialMaxwellUniqueness.homogeneous_fields_zero
#print axioms OQ14.RadialMaxwellUniqueness.homogeneous_unknown_zero
#print axioms OQ14.RadialMaxwellUniqueness.volumeBlock_isUnit
#print axioms OQ14.RadialMaxwellUniqueness.existsUnique_solution
#print axioms OQ14.RadialMaxwellUniqueness.classical_incident_exists
