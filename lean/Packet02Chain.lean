import Packet02SphereVanishing
import Packet02GoodMeasurable
import Packet02Axis
import Packet02ExteriorGood
import Packet02ExteriorSmooth

/-! Packet 02: the actual magnetic symmetry and radial-vanishing chain.

The only source restriction is membership in the electric symmetry sector.
There is no volume-kernel premise and no restriction on the complex frequency.
The convergence set is the explicit frequency-independent `Packet02GoodSet.good`.
The sphere conclusions are asserted separately at every positive radius.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02Chain
open MeasureTheory OQ14.Maxwell OQ14.AngularPower OQ14.WeakDebyeScalar
open OQ14.ModalAxialRotation OQ14.ModalMeridionalReflection

structure Conclusions (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2) : Prop where
  good_measurable : MeasurableSet {x : Space | Packet02GoodSet.good n hn u x}
  good_volume_ae : ∀ᵐ x ∂(volume : Measure Space), Packet02GoodSet.good n hn u x
  good_rotation : ∀ θ x, Packet02GoodSet.good n hn u (rotation θ x) ↔
    Packet02GoodSet.good n hn u x
  good_reflection : ∀ x, Packet02GoodSet.good n hn u (reflection x) ↔
    Packet02GoodSet.good n hn u x
  good_exterior : ∀ x : Space, 1 < ‖x‖ → Packet02GoodSet.good n hn u x
  rotation_covariance : ∀ (z : ℂ) θ x, Packet02GoodSet.good n hn u x →
    ComplexSphereMaxwell.magnetic n hn z u (rotation θ x) =
      vector θ (ComplexSphereMaxwell.magnetic n hn z u x)
  reflection_covariance : ∀ (z : ℂ) x i,
    ComplexSphereMaxwell.magnetic n hn z u (reflection x) i =
      -(sign i : ℂ) * ComplexSphereMaxwell.magnetic n hn z u x i
  radial_vanishing : ∀ (z : ℂ) x, Packet02GoodSet.good n hn u x →
    radialDot (fun j y => ComplexSphereMaxwell.magnetic n hn z u y j) x = 0
  axis_vanishing : ∀ (z : ℂ) (x : Space), x 0 = 0 → x 1 = 0 →
    ComplexSphereMaxwell.magnetic n hn z u x = 0
  exterior_smooth : ∀ z : ℂ, ContDiffOn ℝ (⊤ : ℕ∞)
    (ComplexSphereMaxwell.magnetic n hn z u) {x : Space | 1 < ‖x‖}
  representative_ae : ∀ z : ℂ, Packet02MagneticVanishing.representative n hn z u =ᵐ[volume]
    ComplexSphereMaxwell.magnetic n hn z u
  representative_rotation : ∀ (z : ℂ) θ x,
    Packet02MagneticVanishing.representative n hn z u (rotation θ x) =
      vector θ (Packet02MagneticVanishing.representative n hn z u x)
  representative_reflection : ∀ (z : ℂ) x i,
    Packet02MagneticVanishing.representative n hn z u (reflection x) i =
      -(sign i : ℂ) * Packet02MagneticVanishing.representative n hn z u x i
  representative_radial : ∀ (z : ℂ) x,
    radialDot (fun j y => Packet02MagneticVanishing.representative n hn z u y j) x = 0
  representative_local_L2 : ∀ (z : ℂ) R i,
    MemLp (fun x => Packet02MagneticVanishing.representative n hn z u x i) 2
      (volume.restrict (Metric.closedBall 0 R))
  good_sphere_ae : ∀ r : ℝ, 0 < r → ∀ᵐ ω : Sphere ∂angularMeasure,
    Packet02GoodSet.good n hn u (r • (ω : Space))
  magnetic_sphere_L1 : ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ i : Fin 3,
    Integrable (fun ω : Sphere => ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) i)
      angularMeasure
  radial_sphere_ae : ∀ (z : ℂ) (r : ℝ), 0 < r → ∀ᵐ ω : Sphere ∂angularMeasure,
    (∑ j : Fin 3, (((ω : Space) j : ℝ) : ℂ) *
      ComplexSphereMaxwell.magnetic n hn z u (r • (ω : Space)) j) = 0
  coefficients_zero : ∀ (z : ℂ) (p : HarmonicPolynomial.Poly) r, 0 < r →
    ComplexMagneticDebye.radialCoefficient n hn z u p r = 0
  datum_zero : ∀ z : ℂ, DebyeScalarL2.datum 1 (ComplexMagneticDebye.coordinates n hn z u) = 0

theorem exterior_radial_zero (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) (z : ℂ) (x : Space) (hx : 1 < ‖x‖) :
    radialDot (fun j y => ComplexSphereMaxwell.magnetic n hn z u y j) x = 0 :=
  Packet02MagneticVanishing.radial_zero_good n hn u hu z x
    (Packet02ExteriorGood.exterior_good n hn u x hx)

theorem exterior_rotation (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) (z : ℂ) (θ : ℝ) (x : Space) (hx : 1 < ‖x‖) :
    ComplexSphereMaxwell.magnetic n hn z u (rotation θ x) =
      vector θ (ComplexSphereMaxwell.magnetic n hn z u x) :=
  Packet02MagneticVanishing.magnetic_rotation n hn u hu z θ x
    (Packet02ExteriorGood.exterior_good n hn u x hx)

theorem complete (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ electricSector) : Conclusions n hn u where
  good_measurable := Packet02GoodMeasurable.good_measurable n hn u
  good_volume_ae := Packet02GoodSet.good_ae n hn u
  good_rotation := Packet02GoodRotation.good_rotation n hn u hu.1
  good_reflection := Packet02GoodRotation.good_reflection n hn u hu
  good_exterior := Packet02ExteriorGood.exterior_good n hn u
  rotation_covariance := fun z θ x hx =>
    Packet02MagneticVanishing.magnetic_rotation n hn u hu z θ x hx
  reflection_covariance := fun z x i =>
    ComplexMagneticReflection.sector_magnetic_axial n hn z u hu x i
  radial_vanishing := fun z x hx =>
    Packet02MagneticVanishing.radial_zero_good n hn u hu z x hx
  axis_vanishing := fun z x hx0 hx1 => Packet02Axis.axis_vector_zero n hn u hu z x hx0 hx1
  exterior_smooth := fun z => Packet02ExteriorSmooth.magnetic_contDiffOn n hn z u
  representative_ae := fun z => Packet02MagneticVanishing.representative_ae n hn z u
  representative_rotation := fun z θ x =>
    Packet02MagneticVanishing.representative_rotation n hn z u hu θ x
  representative_reflection := fun z x i =>
    Packet02MagneticVanishing.representative_reflection n hn z u hu x i
  representative_radial := fun z x =>
    Packet02MagneticVanishing.representative_radial_zero n hn z u hu x
  representative_local_L2 := fun z R i =>
    Packet02DebyeVanishing.representative_memLp_ball n hn z u R i
  good_sphere_ae := Packet02SphereVanishing.good_sphere_ae n hn u
  magnetic_sphere_L1 := fun z r hr i => Packet02SphereVanishing.magnetic_integrable n hn z u r hr i
  radial_sphere_ae := fun z r hr => Packet02SphereVanishing.sphere_radial_zero n hn z u hu r hr
  coefficients_zero := fun z p r hr =>
    Packet02SphereVanishing.radialCoefficient_zero n hn z u hu p r hr
  datum_zero := fun z => Packet02DebyeVanishing.datum_zero n hn z u hu

end OQ14.Packet02Chain
#print axioms OQ14.Packet02Chain.exterior_radial_zero
#print axioms OQ14.Packet02Chain.exterior_rotation
#print axioms OQ14.Packet02Chain.complete
