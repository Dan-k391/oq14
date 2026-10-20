import ExteriorMaterial
import AngularPowerZero
import RadialFlux

/-!
Homogeneous actual volume solutions at any support size generate genuine
locally L2 dielectric Maxwell fields. Their outgoing power and far-field
amplitudes follow from actual weak conservation and source integrals.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.HomogeneousVolumePower
open MeasureTheory Metric OQ14.Maxwell OQ14.MaterialMaxwell
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def electric (c : Coefficient) (k R : ℝ) (u : VectorL2) : Field :=
  ExteriorMaterial.scattered c k R u

def magnetic (c : Coefficient) (k : ℝ) (u : VectorL2) : Field :=
  MagneticResponse.magnetic k (DynamicVolume.source c u)

theorem zero_datum_coordinate_ae (i : Fin 3) :
    (fun x : Space => (0 : VectorL2) (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun _ => (0 : ℂ) := by
  have hz := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_zero VectorFourier.Vector 2 (volume : Measure VectorFourier.Frequency))
  filter_upwards [hz] with x hx
  exact congrArg (fun v : VectorFourier.Vector => v i) hx

theorem zero_testMaxwell (k : ℝ) :
    TestMaxwell k (fun _ => 1) (fun _ _ => 0) (fun _ _ => 0) := by
  intro i f
  simp [MagneticResponse.curlPair, fieldPair]

theorem dielectric_measurable (c : Coefficient) : Measurable (dielectric c) :=
  measurable_const.add (c.measurable.comp VectorFourier.coordinateMap.measurable)

theorem dielectric_norm_bound (c : Coefficient) (x : Space) :
    ‖dielectric c x‖ ≤ 1+c.bound := by
  have hb := dielectric_bounds c x
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ dielectric c x)]
  exact hb.2

theorem homogeneous_testMaxwell (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    TestMaxwell k (dielectric c) (electric c k R u) (magnetic c k u) := by
  have hI : ∀ i : Fin 3,
      (fun x : Space => (0 : VectorL2) (VectorFourier.coordinateMap x) i) =ᵐ[volume]
        fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * (0 : ℂ) := by
    intro i
    simpa only [mul_zero] using zero_datum_coordinate_ae i
  have hm := volume_solution_testMaxwell c k R u 0 (fun _ _ => 0) (fun _ _ => 0) hc hI hsol
    (fun _ => locallyIntegrable_zero) (fun _ => locallyIntegrable_zero) (zero_testMaxwell k)
  have hm' : TestMaxwell k (dielectric c) (MaterialField.scattered c k u) (magnetic c k u) := by
    have hEt : MaterialField.total c k u (fun _ _ => 0) = MaterialField.scattered c k u := by
      funext x i
      exact zero_add _
    have hHt : totalMagnetic c k u (fun _ _ => 0) = magnetic c k u := by
      funext x i
      exact zero_add _
    rw [hEt, hHt] at hm
    exact hm
  exact ExteriorMaterial.testMaxwell_congr k (dielectric c)
    (MaterialField.scattered c k u) (magnetic c k u) (electric c k R u) (magnetic c k u)
    (ExteriorMaterial.scattered_ae c k R u hc).symm Filter.EventuallyEq.rfl hm'

theorem electric_memLp_ball (c : Coefficient) (k R T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    MemLp (fun x => electric c k R u x i) 2 (volume.restrict (closedBall 0 T)) := by
  apply (MaterialField.scattered_memLp_ball c k R T u hc i).ae_eq
  filter_upwards [ae_restrict_of_ae (ExteriorMaterial.scattered_ae c k R u hc)] with x hx
  exact (congrFun hx i).symm

theorem magnetic_memLp_ball (c : Coefficient) (k R T : ℝ) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    MemLp (fun x => magnetic c k u x i) 2 (volume.restrict (closedBall 0 T)) :=
  MagneticLocal.magnetic_memLp_ball k T R (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (DynamicVolume.source_zero c u R hc) (StaticNewton.material_source_ae c u) i

theorem electric_exterior (c : Coefficient) (k R : ℝ) (u : VectorL2)
    (x : Space) (hx : R < ‖x‖) :
    electric c k R u x = ExteriorContinuity.electric k (DynamicVolume.source c u) x :=
  ExteriorContinuity.representative_exterior k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) R x hx

theorem homogeneous_farPower_zero (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    AngularPower.farPower k (DynamicVolume.source c u) = 0 :=
  RadialFlux.maxwell_farPower_zero k R hR (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc)
    (dielectric c) (dielectric_measurable c) (1+c.bound) (dielectric_norm_bound c)
    (electric c k R u) (magnetic c k u)
    (fun T i => electric_memLp_ball c k R T u hc i)
    (fun T i => magnetic_memLp_ball c k R T u hc i)
    (homogeneous_testMaxwell c k R u hc hsol)
    (electric_exterior c k R u) (fun _ _ => rfl)

theorem homogeneous_amplitudes_zero (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R) (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    ∀ n : Space, ‖n‖ = 1 →
      MaxwellFarField.electricAmplitude k (DynamicVolume.source c u) n = 0 ∧
      MaxwellFarField.magneticAmplitude k (DynamicVolume.source c u) n = 0 := by
  have he := (AngularPowerZero.farPower_zero_iff_unit k (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc)).mp (homogeneous_farPower_zero c k R hR u hc hsol)
  intro n hn
  exact ⟨he n hn, AngularPowerZero.magnetic_zero_of_electric_zero k _ n (he n hn)⟩

theorem homogeneous_spherical_power_limit_zero (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (u : VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    Filter.Tendsto (fun r => AngularPower.sphericalPower k r (DynamicVolume.source c u))
      Filter.atTop (nhds 0) := by
  have hz := homogeneous_farPower_zero c k R hR u hc hsol
  simpa only [hz] using AngularPower.actual_spherical_power_limit k R hR (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc)

end OQ14.HomogeneousVolumePower


#print axioms OQ14.HomogeneousVolumePower.zero_datum_coordinate_ae
#print axioms OQ14.HomogeneousVolumePower.zero_testMaxwell
#print axioms OQ14.HomogeneousVolumePower.dielectric_measurable
#print axioms OQ14.HomogeneousVolumePower.dielectric_norm_bound
#print axioms OQ14.HomogeneousVolumePower.homogeneous_testMaxwell
#print axioms OQ14.HomogeneousVolumePower.electric_memLp_ball
#print axioms OQ14.HomogeneousVolumePower.magnetic_memLp_ball
#print axioms OQ14.HomogeneousVolumePower.electric_exterior
#print axioms OQ14.HomogeneousVolumePower.homogeneous_farPower_zero
#print axioms OQ14.HomogeneousVolumePower.homogeneous_amplitudes_zero
#print axioms OQ14.HomogeneousVolumePower.homogeneous_spherical_power_limit_zero
