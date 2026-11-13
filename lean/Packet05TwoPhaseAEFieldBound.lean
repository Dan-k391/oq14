import Packet05FixedChartUniformField
import Packet05ChartMaterialPhases

/-! Uniform bounded half-phase representatives give an actual a.e. field
bound on the whole open physical chart, including its null interface. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05TwoPhaseAEFieldBound
open MeasureTheory Set Maxwell Packet05PhysicalChartBranches Packet05LocalDerivative
open scoped Topology
abbrev Plane := ConicalSmoothJunction.Plane

theorem two_phase_ae_bound (up : Bool) (axis : Fin 3) (g : Plane → ℝ) (hg : ContDiff ℝ 1 g)
    (T : Set Space) (hT : IsOpen T) (E : Field) (lower upper : Fin 3 → Space → ℂ) (B : ℝ)
    (hle : ∀ k, (fun y => E y k) =ᵐ[volume.restrict
      (physicalFlatMap up axis g ⁻¹' (T ∩ {y | y 2 < 0}))] lower k)
    (hue : ∀ k, (fun y => E y k) =ᵐ[volume.restrict
      (physicalFlatMap up axis g ⁻¹' (T ∩ {y | 0 < y 2}))] upper k)
    (hlb : ∀ k y, y ∈ physicalFlatMap up axis g ⁻¹' (T ∩ {y | y 2 < 0}) → ‖lower k y‖ ≤ B)
    (hub : ∀ k y, y ∈ physicalFlatMap up axis g ⁻¹' (T ∩ {y | 0 < y 2}) → ‖upper k y‖ ≤ B) :
    ∀ k, ∀ᵐ y ∂volume, y ∈ physicalFlatMap up axis g ⁻¹' T → ‖E y k‖ ≤ B := by
  let p := physicalFlatMap up axis g
  have hp := physicalFlat_continuous up axis g hg
  have hlo : MeasurableSet (p ⁻¹' (T ∩ {y | y 2 < 0})) :=
    (hT.inter (isOpen_lt (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous continuous_const)).measurableSet.preimage hp.measurable
  have hhi : MeasurableSet (p ⁻¹' (T ∩ {y | 0 < y 2})) :=
    (hT.inter (isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous)).measurableSet.preimage hp.measurable
  have hplane : ∀ᵐ y : Space ∂volume, y 2 ≠ 0 := by
    rw [ae_iff]
    simpa using interface_plane_null
  have hpp := (physicalFlat_measure_preserving up axis g hg.continuous).quasiMeasurePreserving.ae hplane
  intro k
  have hl := (ae_restrict_iff' hlo).mp (hle k)
  have hu := (ae_restrict_iff' hhi).mp (hue k)
  filter_upwards [hl,hu,hpp] with y hylo hyhi hnonzero hyT
  by_cases hneg : p y 2 < 0
  · have hy : y ∈ p ⁻¹' (T ∩ {y | y 2 < 0}) := ⟨hyT,hneg⟩
    rw [hylo hy]
    exact hlb k y hy
  · have hpos : 0 < p y 2 := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hnonzero)
    have hy : y ∈ p ⁻¹' (T ∩ {y | 0 < y 2}) := ⟨hyT,hpos⟩
    rw [hyhi hy]
    exact hub k y hy

end OQ14.Packet05TwoPhaseAEFieldBound
#print axioms OQ14.Packet05TwoPhaseAEFieldBound.two_phase_ae_bound
