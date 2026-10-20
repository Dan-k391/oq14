import LayeredInclusionCells
import PiecewiseScattering
import PiecewiseRealSpectrum

/-! # Actual Maxwell scattering for layered spherical inclusion devices -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.LayeredInclusionScattering

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialMaxwell
open scoped Topology

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

section Geometry

variable {ι : Type*} [Fintype ι] {n : ℕ}
    (center : ι → Space) (radius : ι → ℝ) (r : Fin (n+1) → ℝ)
    (hm : StrictMono r) (hp : ∀ j, 0 < r j) (hr : ∀ i, 0 < radius i)
    (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (value : ι ⊕ Fin (n+2) → ℝ) (hvalue : ∀ i, 0 < value i)
    (hε : ∀ i, ∀ᵐ x : Space, x ∈ LayeredInclusionCells.cell center radius r i →
      dielectric c x = value i)

include center radius r hm hp hr hcore hsep c R hR hc value hvalue hε

theorem volumeBlock_isUnit (k : ℝ) (hk : 0 < k) :
    IsUnit (DynamicVolume.volumeBlock c k R) := by
  let p := LayeredInclusionCells.partition center radius r hm hp hr hcore hsep
    (dielectric c) value hvalue hε
  obtain ⟨x,hx,hout⟩ := LayeredInclusionCells.exterior_seed center radius r hm hp R
  exact PiecewiseMaxwellUniqueness.volumeBlock_isUnit c k hk R hR hc p
    (.inr (Fin.last (n+1))) x hx hout

theorem solution_equation (k : ℝ) (hk : 0 < k) (f : VectorL2) :
    DynamicVolume.volumeBlock c k R (MaterialField.solution c k R f) = f := by
  have hunit := volumeBlock_isUnit center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c k R) hunit)

theorem solution_unique (k : ℝ) (hk : 0 < k) (f u : VectorL2)
    (hu : DynamicVolume.volumeBlock c k R u = f) : u = MaterialField.solution c k R f := by
  have hunit := volumeBlock_isUnit center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    (hu.trans (solution_equation center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk f).symm)

theorem solution_physicalFields (k : ℝ) (hk : 0 < k) (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    PiecewiseScattering.PhysicalFields c k R Einc Hinc
      (MaterialField.solution c k R (IncidentLocalization.datum c R Einc hc (hE R))) := by
  exact PiecewiseScattering.physical_fields_of_volume_equation c k R hR hc Einc Hinc hE hH hMax _
    (solution_equation center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk _)

theorem classical_incident_exists (k : ℝ) (hk : 0 < k) (Einc Hinc : Field)
    (hE : ∀ i, ContDiff ℝ 1 (fun x => Einc x i))
    (hH : ∀ i, ContDiff ℝ 1 (fun x => Hinc x i))
    (hMax : ∀ x, MaxwellAt k 1 1 Einc Hinc x) :
    ∃ u : VectorL2, PiecewiseScattering.PhysicalFields c k R Einc Hinc u := by
  let p := LayeredInclusionCells.partition center radius r hm hp hr hcore hsep
    (dielectric c) value hvalue hε
  obtain ⟨x,hx,hout⟩ := LayeredInclusionCells.exterior_seed center radius r hm hp R
  exact PiecewiseScattering.classical_incident_exists c k hk R hR hc p
    (.inr (Fin.last (n+1))) x hx hout Einc Hinc hE hH hMax

theorem positive_complex_volumeBlock_isUnit (k : ℝ) (hk : 0 < k) :
    IsUnit (ComplexConvolutionAnalytic.volumeBlock c (k : ℂ) R) := by
  rw [ComplexConvolutionAnalytic.volumeBlock_ofReal]
  exact volumeBlock_isUnit center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk

theorem exceptional_disjoint_positiveAxis :
    Disjoint {z : ℂ | ¬ IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R)}
      (Complex.ofReal '' Ioi (0 : ℝ)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨k,hk,rfl⟩
  exact hz (positive_complex_volumeBlock_isUnit center radius r hm hp hr hcore hsep
    c R hR hc value hvalue hε k hk)

theorem inverse_analyticAt_positive (k : ℝ) (hk : 0 < k) :
    AnalyticAt ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R)) (k : ℂ) :=
  VolumeAnalyticAlternative.inverse_analyticAt_of_isUnit c R hR (k : ℂ)
    (positive_complex_volumeBlock_isUnit center radius r hm hp hr hcore hsep
      c R hR hc value hvalue hε k hk)

theorem inverse_analyticOnNhd_positiveAxis :
    AnalyticOnNhd ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R))
      (Complex.ofReal '' Ioi (0 : ℝ)) := by
  rintro z ⟨k,hk,rfl⟩
  exact inverse_analyticAt_positive center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk

theorem complex_neighborhood_regular (k : ℝ) (hk : 0 < k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (k : ℂ) δ,
      IsUnit (ComplexConvolutionAnalytic.volumeBlock c z R) ∧
      AnalyticAt ℂ (fun w => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c w R)) z := by
  let p := LayeredInclusionCells.partition center radius r hm hp hr hcore hsep
    (dielectric c) value hvalue hε
  obtain ⟨x,hx,hout⟩ := LayeredInclusionCells.exterior_seed center radius r hm hp R
  exact PiecewiseRealSpectrum.complex_neighborhood_regular c R hR hc p
    (.inr (Fin.last (n+1))) x hx hout k hk

theorem inverse_apply_analyticAt_positive (k : ℝ) (hk : 0 < k) (f : VectorL2) :
    AnalyticAt ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R) f) (k : ℂ) :=
  ((ContinuousLinearMap.apply ℂ VectorL2 f).analyticAt
    (Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c (k : ℂ) R))).comp
    (f := fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock c z R))
    (inverse_analyticAt_positive center radius r hm hp hr hcore hsep c R hR hc value hvalue hε k hk)

end Geometry

end OQ14.LayeredInclusionScattering

#print axioms OQ14.LayeredInclusionScattering.volumeBlock_isUnit
#print axioms OQ14.LayeredInclusionScattering.solution_equation
#print axioms OQ14.LayeredInclusionScattering.solution_unique
#print axioms OQ14.LayeredInclusionScattering.solution_physicalFields
#print axioms OQ14.LayeredInclusionScattering.classical_incident_exists
#print axioms OQ14.LayeredInclusionScattering.positive_complex_volumeBlock_isUnit
#print axioms OQ14.LayeredInclusionScattering.exceptional_disjoint_positiveAxis
#print axioms OQ14.LayeredInclusionScattering.inverse_analyticAt_positive
#print axioms OQ14.LayeredInclusionScattering.inverse_analyticOnNhd_positiveAxis
#print axioms OQ14.LayeredInclusionScattering.complex_neighborhood_regular
#print axioms OQ14.LayeredInclusionScattering.inverse_apply_analyticAt_positive
