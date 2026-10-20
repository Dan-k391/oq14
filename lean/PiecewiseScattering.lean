import PiecewiseMaxwellUniqueness
import ExteriorMaterial
import MaxwellRadiation

/-! # Actual scattering fields for material partitions at arbitrary support size -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.PiecewiseScattering

open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.MaterialMaxwell
  OQ14.PiecewiseMaxwellUniqueness
open scoped Topology

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def scatteredDefect (c : Coefficient) (k R : ℝ) (u : VectorL2) (x : Space) (i : Fin 3) : ℂ :=
  crossProduct (MagneticResponse.magnetic k (DynamicVolume.source c u) x)
    (MaxwellRadiation.direction x) i-ExteriorMaterial.scattered c k R u x i

theorem total_scattered_defect_eq (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (Einc Hinc : Field) (x : Space) (i : Fin 3) :
    crossProduct (fun j => totalMagnetic c k u Hinc x j-Hinc x j) (MaxwellRadiation.direction x) i-
      (ExteriorMaterial.total c k R u Einc x i-Einc x i) = scatteredDefect c k R u x i := by
  simp only [totalMagnetic,ExteriorMaterial.total,add_sub_cancel_left,scatteredDefect]

theorem scattered_defect_exterior (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (x : Space) (hx : R < ‖x‖) (i : Fin 3) :
    scatteredDefect c k R u x i = MaxwellRadiation.radiationDefect k (DynamicVolume.source c u) x i := by
  change crossProduct (MagneticResponse.magnetic k (DynamicVolume.source c u) x)
    (MaxwellRadiation.direction x) i-HomogeneousVolumePower.electric c k R u x i = _
  rw [HomogeneousVolumePower.electric_exterior c k R u x hx]
  rfl

theorem scattered_defect_bound (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (x : Space) (hx : 2*R < ‖x‖) (hx₂ : 2 ≤ ‖x‖) (i : Fin 3) :
    ‖scatteredDefect c k R u x i‖ ≤ MaxwellRadiation.radiationConstant k R *
      MaxwellRadiation.sourceMass (DynamicVolume.source c u)/‖x‖^2 := by
  rw [scattered_defect_exterior c k R u x (by linarith) i]
  exact MaxwellRadiation.silver_mueller_bound k R hR (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc) x hx hx₂ i

theorem scattered_defect_limit {α : Type*} {l : Filter α}
    (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (γ : α → Space) (hγ : Tendsto (fun t => ‖γ t‖) l atTop) (i : Fin 3) :
    Tendsto (fun t => (‖γ t‖ : ℂ)*scatteredDefect c k R u (γ t) i) l (𝓝 0) := by
  have h := MaxwellRadiation.silver_mueller_limit k R hR (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc) γ hγ i
  apply h.congr'
  filter_upwards [hγ.eventually (eventually_gt_atTop R)] with t ht
  rw [scattered_defect_exterior c k R u (γ t) ht i]

structure PhysicalFields (c : Coefficient) (k R : ℝ) (Einc Hinc : Field) (u : VectorL2) : Prop where
  maxwell : TestMaxwell k (dielectric c) (ExteriorMaterial.total c k R u Einc)
    (totalMagnetic c k u Hinc)
  electric_L2 : ∀ T i, MemLp (fun x => ExteriorMaterial.total c k R u Einc x i) 2
    (volume.restrict (closedBall 0 T))
  magnetic_L2 : ∀ T i, MemLp (fun x => totalMagnetic c k u Hinc x i) 2
    (volume.restrict (closedBall 0 T))
  exterior_continuous : ∀ x, R < ‖x‖ → ContinuousAt (ExteriorMaterial.scattered c k R u) x
  polarization : ∀ i, DynamicVolume.source c u i =ᵐ[volume] fun x =>
    (c.value (VectorFourier.coordinateMap x) : ℂ)*ExteriorMaterial.total c k R u Einc x i
  radiation_bound : ∀ x, 2*R < ‖x‖ → 2 ≤ ‖x‖ → ∀ i,
    ‖scatteredDefect c k R u x i‖ ≤ MaxwellRadiation.radiationConstant k R *
      MaxwellRadiation.sourceMass (DynamicVolume.source c u)/‖x‖^2

theorem physical_fields_of_volume_equation (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) (u : VectorL2)
    (hu : DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R)) :
    PhysicalFields c k R Einc Hinc u := by
  have hM := volume_solution_testMaxwell c k R u _ Einc Hinc hc
    (IncidentLocalization.datum_actual c R Einc hc (hE R)) hu
    (fun i => SmallVolumeMaxwell.locallyIntegrable_of_memLp_ball _ (fun T => hE T i))
    (fun i => SmallVolumeMaxwell.locallyIntegrable_of_memLp_ball _ (fun T => hH T i)) hMax
  refine ⟨?_,?_,?_,ExteriorMaterial.scattered_continuousAt c k R u hc,?_,?_⟩
  · exact ExteriorMaterial.testMaxwell_congr k (dielectric c) _ _ _ _
      (ExteriorMaterial.total_ae c k R u Einc hc).symm EventuallyEq.rfl hM
  · exact fun T i => ExteriorMaterial.total_memLp_ball c k R T u Einc hc (hE T) i
  · exact fun T i => SmallVolumeMaxwell.total_magnetic_memLp_ball c k R T u Hinc hc (hH T) i
  · exact ExteriorMaterial.material_relation c k R u _ Einc hc
      (IncidentLocalization.datum_actual c R Einc hc (hE R)) hu
  · exact fun x hx hx₂ i => scattered_defect_bound c k R hR u hc x hx hx₂ i

theorem exists_piecewise_fields {ι : Type*} (c : Coefficient) (k : ℝ) (hk : 0 < k)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (dielectric c)) (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    ∃ u : VectorL2,
      DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R) ∧
      (∀ v : VectorL2, DynamicVolume.volumeBlock c k R v =
        IncidentLocalization.datum c R Einc hc (hE R) → v = u) ∧
      ‖u‖ ≤ ‖Ring.inverse (DynamicVolume.volumeBlock c k R)‖*
        ‖IncidentLocalization.datum c R Einc hc (hE R)‖ ∧ PhysicalFields c k R Einc Hinc u := by
  let f := IncidentLocalization.datum c R Einc hc (hE R)
  let u := MaterialField.solution c k R f
  have hunit := volumeBlock_isUnit c k hk R hR hc p i₀ x₀ hx₀ hout
  have hu : DynamicVolume.volumeBlock c k R u = f :=
    congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
      (Ring.mul_inverse_cancel (DynamicVolume.volumeBlock c k R) hunit)
  refine ⟨u,hu,?_,?_,physical_fields_of_volume_equation c k R hR hc Einc Hinc hE hH hMax u hu⟩
  · intro v hv
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1 (hv.trans hu.symm)
  · exact (Ring.inverse (DynamicVolume.volumeBlock c k R)).le_opNorm f

theorem classical_incident_exists {ι : Type*} (c : Coefficient) (k : ℝ) (hk : 0 < k)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (p : Partition ι (dielectric c)) (i₀ : ι) (x₀ : Space) (hx₀ : x₀ ∈ p.cell i₀) (hout : R < ‖x₀‖)
    (Einc Hinc : Field) (hE : ∀ i, ContDiff ℝ 1 (fun x => Einc x i))
    (hH : ∀ i, ContDiff ℝ 1 (fun x => Hinc x i))
    (hMax : ∀ x, MaxwellAt k 1 1 Einc Hinc x) :
    ∃ u : VectorL2, PhysicalFields c k R Einc Hinc u := by
  obtain ⟨u,_,_,_,hfields⟩ := exists_piecewise_fields c k hk R hR hc p i₀ x₀ hx₀ hout Einc Hinc
    (fun T i => SmallVolumeMaxwell.continuous_memLp_ball _ (hE i).continuous T)
    (fun T i => SmallVolumeMaxwell.continuous_memLp_ball _ (hH i).continuous T)
    (classical_vacuum_testMaxwell k Einc Hinc hE hH hMax)
  exact ⟨u,hfields⟩

end OQ14.PiecewiseScattering

#print axioms OQ14.PiecewiseScattering.total_scattered_defect_eq
#print axioms OQ14.PiecewiseScattering.scattered_defect_exterior
#print axioms OQ14.PiecewiseScattering.scattered_defect_bound
#print axioms OQ14.PiecewiseScattering.scattered_defect_limit
#print axioms OQ14.PiecewiseScattering.physical_fields_of_volume_equation
#print axioms OQ14.PiecewiseScattering.exists_piecewise_fields
#print axioms OQ14.PiecewiseScattering.classical_incident_exists
