import LayeredInclusionCoefficient
import LayeredInclusionScattering

/-! # Maxwell scattering for literal finite indicator-sum devices -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.LayeredDeviceScattering

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialMaxwell
open OQ14.LayeredInclusionCoefficient
open scoped Topology

abbrev VectorL2 := VectorFourier.VectorL2

section Geometry

variable {ι : Type*} [Fintype ι] {n : ℕ}
    (center : ι → Space) (radius : ι → ℝ) (r : Fin (n+1) → ℝ)
    (hm : StrictMono r) (hp : ∀ j, 0 < r j) (hr : ∀ i, 0 < radius i)
    (hcore : ∀ i, ‖center i‖+radius i < r 0)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (χ : ι ⊕ Fin (n+2) → ℝ) (hχ : ∀ i, 0 ≤ χ i)
    (M : ℝ) (hM : 0 ≤ M) (hχM : ∀ i, χ i ≤ M)
    (hχext : χ (.inr (Fin.last (n+1))) = 0)

include center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext

local notation "device" => coefficient center radius r hm hcore hsep χ hχ M hM hχM
local notation "outer" => r (Fin.last n)
local notation "supportProof" => coefficient_zero_outside center radius r hm hcore hsep χ hχ M hM hχM hχext

theorem volumeBlock_isUnit (k : ℝ) (hk : 0 < k) :
    IsUnit (DynamicVolume.volumeBlock device k outer) :=
  LayeredInclusionScattering.volumeBlock_isUnit center radius r hm hp hr hcore hsep
    device outer (hp (Fin.last n)).le supportProof (fun i => 1+χ i)
    (dielectric_values_positive χ hχ)
    (dielectric_on_cell_ae center radius r hm hcore hsep χ hχ M hM hχM) k hk

theorem solution_equation (k : ℝ) (hk : 0 < k) (f : VectorL2) :
    DynamicVolume.volumeBlock device k outer (MaterialField.solution device k outer f) = f := by
  have hunit := volumeBlock_isUnit center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock device k outer) hunit)

theorem solution_unique (k : ℝ) (hk : 0 < k) (f u : VectorL2)
    (hu : DynamicVolume.volumeBlock device k outer u = f) : u = MaterialField.solution device k outer f := by
  have hunit := volumeBlock_isUnit center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    (hu.trans (solution_equation center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk f).symm)

theorem solution_physicalFields (k : ℝ) (hk : 0 < k) (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    PiecewiseScattering.PhysicalFields device k outer Einc Hinc
      (MaterialField.solution device k outer
        (IncidentLocalization.datum device outer Einc supportProof (hE outer))) := by
  exact PiecewiseScattering.physical_fields_of_volume_equation device k outer (hp (Fin.last n)).le
    supportProof Einc Hinc hE hH hMax _
    (solution_equation center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk _)

theorem classical_incident_exists (k : ℝ) (hk : 0 < k) (Einc Hinc : Field)
    (hE : ∀ i, ContDiff ℝ 1 (fun x => Einc x i))
    (hH : ∀ i, ContDiff ℝ 1 (fun x => Hinc x i))
    (hMax : ∀ x, MaxwellAt k 1 1 Einc Hinc x) :
    ∃ u : VectorL2, PiecewiseScattering.PhysicalFields device k outer Einc Hinc u :=
  LayeredInclusionScattering.classical_incident_exists center radius r hm hp hr hcore hsep
    device outer (hp (Fin.last n)).le supportProof (fun i => 1+χ i)
    (dielectric_values_positive χ hχ)
    (dielectric_on_cell_ae center radius r hm hcore hsep χ hχ M hM hχM) k hk Einc Hinc hE hH hMax

theorem positive_complex_volumeBlock_isUnit (k : ℝ) (hk : 0 < k) :
    IsUnit (ComplexConvolutionAnalytic.volumeBlock device (k : ℂ) outer) := by
  rw [ComplexConvolutionAnalytic.volumeBlock_ofReal]
  exact volumeBlock_isUnit center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk

theorem exceptional_disjoint_positiveAxis :
    Disjoint {z : ℂ | ¬ IsUnit (ComplexConvolutionAnalytic.volumeBlock device z outer)}
      (Complex.ofReal '' Ioi (0 : ℝ)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨k,hk,rfl⟩
  exact hz (positive_complex_volumeBlock_isUnit center radius r hm hp hr hcore hsep
    χ hχ M hM hχM hχext k hk)

theorem inverse_analyticAt_positive (k : ℝ) (hk : 0 < k) :
    AnalyticAt ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock device z outer)) (k : ℂ) :=
  VolumeAnalyticAlternative.inverse_analyticAt_of_isUnit device outer (hp (Fin.last n)).le (k : ℂ)
    (positive_complex_volumeBlock_isUnit center radius r hm hp hr hcore hsep
      χ hχ M hM hχM hχext k hk)

theorem inverse_analyticOnNhd_positiveAxis :
    AnalyticOnNhd ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock device z outer))
      (Complex.ofReal '' Ioi (0 : ℝ)) := by
  rintro z ⟨k,hk,rfl⟩
  exact inverse_analyticAt_positive center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk

theorem complex_neighborhood_regular (k : ℝ) (hk : 0 < k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball (k : ℂ) δ,
      IsUnit (ComplexConvolutionAnalytic.volumeBlock device z outer) ∧
      AnalyticAt ℂ (fun w => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock device w outer)) z :=
  LayeredInclusionScattering.complex_neighborhood_regular center radius r hm hp hr hcore hsep
    device outer (hp (Fin.last n)).le supportProof (fun i => 1+χ i)
    (dielectric_values_positive χ hχ)
    (dielectric_on_cell_ae center radius r hm hcore hsep χ hχ M hM hχM) k hk

theorem inverse_apply_analyticAt_positive (k : ℝ) (hk : 0 < k) (f : VectorL2) :
    AnalyticAt ℂ (fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock device z outer) f) (k : ℂ) :=
  ((ContinuousLinearMap.apply ℂ VectorL2 f).analyticAt
    (Ring.inverse (ComplexConvolutionAnalytic.volumeBlock device (k : ℂ) outer))).comp
    (f := fun z => Ring.inverse (ComplexConvolutionAnalytic.volumeBlock device z outer))
    (inverse_analyticAt_positive center radius r hm hp hr hcore hsep χ hχ M hM hχM hχext k hk)

end Geometry

end OQ14.LayeredDeviceScattering

#print axioms OQ14.LayeredDeviceScattering.volumeBlock_isUnit
#print axioms OQ14.LayeredDeviceScattering.solution_equation
#print axioms OQ14.LayeredDeviceScattering.solution_unique
#print axioms OQ14.LayeredDeviceScattering.solution_physicalFields
#print axioms OQ14.LayeredDeviceScattering.classical_incident_exists
#print axioms OQ14.LayeredDeviceScattering.positive_complex_volumeBlock_isUnit
#print axioms OQ14.LayeredDeviceScattering.exceptional_disjoint_positiveAxis
#print axioms OQ14.LayeredDeviceScattering.inverse_analyticAt_positive
#print axioms OQ14.LayeredDeviceScattering.inverse_analyticOnNhd_positiveAxis
#print axioms OQ14.LayeredDeviceScattering.complex_neighborhood_regular
#print axioms OQ14.LayeredDeviceScattering.inverse_apply_analyticAt_positive
