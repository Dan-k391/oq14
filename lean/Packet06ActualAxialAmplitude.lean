import Packet06AxialAmplitude
import Packet06RoundedPlacement
import Packet05RoundedModeSupport
import Packet05ActualMaximum

/-! Axial symmetry of the actual physical Euclidean amplitude, obtained from
the exact sector kernel equation and the actual electric representative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06ActualAxialAmplitude
open MeasureTheory Metric Set Maxwell ModalAxialRotation Packet05ActualMaximum

theorem amplitude_eq_sqrt_energy (E : Field) (x : Space) :
    physicalAmplitude (fun i y => E y i) x = Real.sqrt (energy (E x)) := by
  simp only [physicalAmplitude,energy,Fin.sum_univ_three,Complex.normSq_eq_norm_sq]

theorem actual_amplitude_ae (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (z : ℂ)
    (u : Packet06SectorOperator.Sector)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hpos : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0) (θ : ℝ) :
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
    ∀ᵐ x ∂volume.restrict (ball (0 : Space) 1),
      physicalAmplitude (fun i y => E y i) (rotation θ x)=physicalAmplitude (fun i y => E y i) x := by
  let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
  have he : ∀ᵐ x : Space, x ∈ closedBall 0 1 → ∀ i,
      Packet06LocalPencil.response c z 1 1 u (VectorFourier.coordinateMap x) i=E x i := by
    apply (ae_restrict_iff' measurableSet_closedBall).mp
    exact ae_all_iff.mpr (fun i => Packet06ComplexElectric.electric_ae_on_ball z 1 1
      (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
      (DynamicVolume.source_integrable c u 1 hc) (DynamicVolume.source_zero c u 1 hc)
      (StaticNewton.material_source_ae c u) i)
  have her := (rotation θ).measurePreserving.quasiMeasurePreserving.ae he
  filter_upwards [ae_restrict_of_ae he,ae_restrict_of_ae her,
    ae_restrict_of_ae (Packet06AxialAmplitude.response_energy_ae c ha z 1 1 le_rfl u hc hu θ),
    ae_restrict_mem measurableSet_ball] with x hx hxr henergy hball
  have hrball : rotation θ x ∈ closedBall (0 : Space) 1 := by
    simpa only [mem_closedBall,dist_zero_right,(rotation θ).norm_map] using
      (ball_subset_closedBall hball : x ∈ closedBall (0 : Space) 1)
  have hxE : (fun i => Packet06LocalPencil.response c z 1 1 u (VectorFourier.coordinateMap x) i)=E x :=
    funext (hx (ball_subset_closedBall hball))
  have hrE : (fun i => Packet06LocalPencil.response c z 1 1 u (VectorFourier.coordinateMap (rotation θ x)) i)=E (rotation θ x) :=
    funext (hxr hrball)
  have hh := henergy (hpos x hball)
  rw [hxE,hrE] at hh
  simpa only [amplitude_eq_sqrt_energy] using congrArg Real.sqrt hh

theorem rounded_amplitude_ae {N : ℕ} (n : ℝ) (hn : 1 < n)
    (g : Packet06ConcreteModalGeometry.Geometry N n) (η : ℝ) (hη : 0 ≤ η) (j : ℕ)
    (z : ℂ) (u : Packet06SectorOperator.Sector)
    (hu : ComplexConvolutionAnalytic.volumeBlock (Packet06ConcreteModalRounding.rounded n hn g η hη j) z 1 u=0)
    (θ : ℝ) :
    let c := Packet06ConcreteModalRounding.rounded n hn g η hη j
    let E := Packet06ComplexElectric.electric z (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u)
    ∀ᵐ x ∂volume.restrict (ball (0 : Space) 1),
      physicalAmplitude (fun i y => E y i) (rotation θ x)=physicalAmplitude (fun i y => E y i) x := by
  have hdata := Packet06RoundedInsertion.admissible
    (fun _ : Fin N => g.datum) (fun _ => g.radius) g.center (n^2) (sq_nonneg n)
    (fun _ => g.contrast.le) (fun _ => g.radius_outer) g.outer_disjoint (fun _ => g.radius_pos)
    (ModalWeightedMode.coefficient n hn) η hη (ModalWeightedMode.coefficient_support n hn)
    (Packet06SphereSymmetry.sphere_axial n hn) (Packet06SphereSymmetry.sphere_meridional n hn)
    g.onAxis (fun i => (g.outer_inside i).trans ball_subset_closedBall)
  apply actual_amplitude_ae _ (hdata.2.2.2.2.2.1 j) z u
    (Packet05RoundedModeSupport.rounded_support n hn g η hη j) _ hu θ
  intro x hx
  exact (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη j x hx).ne'

end OQ14.Packet06ActualAxialAmplitude
#print axioms OQ14.Packet06ActualAxialAmplitude.amplitude_eq_sqrt_energy
#print axioms OQ14.Packet06ActualAxialAmplitude.actual_amplitude_ae
#print axioms OQ14.Packet06ActualAxialAmplitude.rounded_amplitude_ae
