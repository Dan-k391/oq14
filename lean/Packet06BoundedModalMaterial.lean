import Packet06ConcreteModalRounding
import Packet06PhysicalPlacement

/-! Any prescribed index ceiling above one allows the actual rounded construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06BoundedModalMaterial
open Metric Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
abbrev Space := Maxwell.Space

theorem choose_index (K : ℝ) (hK : 1 < K) :
    ∃ (n ηmax : ℝ), 1 < n ∧ n < K ∧ IsAlgebraic ℚ (n : ℂ) ∧
      0 < ηmax ∧ (1+ηmax)*n^2=K^2 := by
  obtain ⟨q,hq1,hqK⟩ := exists_rat_btwn hK
  let n : ℝ := q
  have hn : 1 < n := hq1
  have hnK : n < K := hqK
  have hn0 : 0 < n := by linarith
  have hsq : n^2 < K^2 := by nlinarith
  refine ⟨n,(K^2-n^2)/n^2,hn,hnK,?_,div_pos (sub_pos.mpr hsq) (sq_pos_of_pos hn0),?_⟩
  · simpa only [n,Complex.ofReal_ratCast] using (isAlgebraic_rat ℚ (A := ℂ) q)
  · field_simp

theorem rounded_bounds {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (K : ℝ) (_hK : 1 < K)
    (hceiling : (1+η)*n^2 ≤ K^2) (j : ℕ) (x : Space) :
    1 ≤ MaterialMaxwell.dielectric (rounded n hn g η hη j) x ∧
      MaterialMaxwell.dielectric (rounded n hn g η hη j) x ≤ K^2 := by
  change 1 ≤ 1+(rounded n hn g η hη j).value (VectorFourier.coordinateMap x) ∧ _
  rw [dielectric_values]
  change 1 ≤ _ ∧ (1+(rounded n hn g η hη j).value (VectorFourier.coordinateMap x)) ≤ K^2
  rw [dielectric_values]
  split_ifs <;> constructor <;> nlinarith [sq_nonneg n,mul_nonneg hη (sq_nonneg n)]

theorem placed_dielectric (c : StaticCoefficient.Coefficient) (s : ℝ) (a x : Space) :
    MaterialMaxwell.dielectric (Packet06PlacedKernel.placedCoefficient s a c) x =
      MaterialMaxwell.dielectric c (Packet06CyclicRotation.unrotate (s • (x-a))) := by
  rw [Packet06PlacedKernel.placedCoefficient,Packet06TranslationMaterial.dielectric_value,
    FrequencyScalingMaxwell.dielectric_scaleCoeff,Packet06CyclicMaterial.dielectric_value]

theorem placed_bounds (c : StaticCoefficient.Coefficient) (K : ℝ)
    (hc : ∀ x : Space, 1 ≤ MaterialMaxwell.dielectric c x ∧ MaterialMaxwell.dielectric c x ≤ K^2)
    (s : ℝ) (a x : Space) :
    1 ≤ MaterialMaxwell.dielectric (Packet06PlacedKernel.placedCoefficient s a c) x ∧
      MaterialMaxwell.dielectric (Packet06PlacedKernel.placedCoefficient s a c) x ≤ K^2 := by
  rw [placed_dielectric]
  exact hc _

end OQ14.Packet06BoundedModalMaterial
#print axioms OQ14.Packet06BoundedModalMaterial.choose_index
#print axioms OQ14.Packet06BoundedModalMaterial.rounded_bounds
#print axioms OQ14.Packet06BoundedModalMaterial.placed_dielectric
#print axioms OQ14.Packet06BoundedModalMaterial.placed_bounds
