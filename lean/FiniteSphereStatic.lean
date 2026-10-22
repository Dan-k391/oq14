import StaticBallInteraction
import StaticSphereMaterial

/-! # Actual finite sphere trial sources and material conversions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.FiniteSphereStatic

open MeasureTheory Metric Set StaticBallNewton
open scoped Topology BigOperators
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coefficient (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ) :
    StaticCoefficient.Coefficient where
  value x := if VectorFourier.coordinateMap.symm x ∈ ⋃ j, ball (p j) (r j) then χ else 0
  bound := χ
  measurable := Measurable.ite
    ((isOpen_iUnion (fun _ => isOpen_ball)).measurableSet.preimage
      VectorFourier.coordinateMap.symm.measurable) measurable_const measurable_const
  nonnegative x := by split_ifs <;> first | exact hχ | exact le_rfl
  bounded x := by split_ifs <;> first | exact le_rfl | exact hχ

omit [Fintype ι] [DecidableEq ι] in
theorem coefficient_value (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ) (x : Space) :
    (coefficient p r χ hχ).value (VectorFourier.coordinateMap x) =
      if x ∈ ⋃ j, ball (p j) (r j) then χ else 0 := by
  simp only [coefficient, MeasurableEquiv.symm_apply_apply]

def sumSource (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) : VectorL2 :=
  ∑ j : ι, StaticBallCentered.source (p j) (r j) (P j)

theorem sumSource_ae (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (m : Fin 3) :
    (fun x => sumSource p r P (VectorFourier.coordinateMap x) m) =ᵐ[volume]
      fun x => ∑ j : ι, (ball (p j) (r j)).indicator (fun _ => P j m) x := by
  have he : NewtonL2.physicalCoordinate (sumSource p r P) m =
      ∑ j : ι, NewtonL2.physicalCoordinate (StaticBallCentered.source (p j) (r j) (P j)) m := by
    simp only [sumSource, NewtonL2.physicalCoordinate, map_sum]
  have hj : ∀ᵐ x : Space, ∀ j : ι,
      NewtonL2.physicalCoordinate (StaticBallCentered.source (p j) (r j) (P j)) m x =
        (ball (p j) (r j)).indicator (fun _ => P j m) x :=
    ae_all_iff.mpr (fun j => (NewtonL2.physicalCoordinate_ae _ m).trans
      (StaticBallCentered.source_ae (p j) (r j) (P j) m))
  filter_upwards [NewtonL2.physicalCoordinate_ae (sumSource p r P) m, hj,
    StaticBallInteraction.finite_sum_ae Finset.univ
      (fun j => NewtonL2.physicalCoordinate (StaticBallCentered.source (p j) (r j) (P j)) m)]
    with x hx hj hs
  rw [← hx, he, hs]
  simp only [hj]

omit [Fintype ι] [DecidableEq ι] in
theorem other_ball_excluded (p : ι → Space) (r : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → r i+r j ≤ dist (p i) (p j))
    (i j : ι) (hji : j ≠ i) (x : Space) (hx : x ∈ ball (p i) (r i)) :
    x ∉ ball (p j) (r j) := by
  intro hj
  have hi' : dist (p i) x < r i := by simpa only [mem_ball, dist_comm] using hx
  have hj' : dist x (p j) < r j := hj
  have ht := dist_triangle (p i) x (p j)
  have hs := hsep i j hji.symm
  linarith

theorem sumSource_on_ball (p : ι → Space) (r : ι → ℝ) (P : ι → Vector)
    (hsep : ∀ i j, i ≠ j → r i+r j ≤ dist (p i) (p j)) (i : ι) (m : Fin 3) :
    ∀ᵐ x : Space, x ∈ ball (p i) (r i) →
      sumSource p r P (VectorFourier.coordinateMap x) m = P i m := by
  filter_upwards [sumSource_ae p r P m] with x hx hm
  rw [hx, Finset.sum_eq_single i]
  · exact indicator_of_mem hm _
  · intro j _ hji
    exact indicator_of_not_mem (other_ball_excluded p r hsep i j hji x hm) _
  · simp

omit [DecidableEq ι] in
theorem sqrt_single (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (j : ι) (P : Vector) :
    StaticCoefficient.sqrtMultiplier (coefficient p r χ hχ) (StaticBallCentered.source (p j) (r j) P) =
      StaticBallCentered.source (p j) (r j) ((Real.sqrt χ : ℂ) • P) := by
  apply StaticSphereMaterial.vector_ext_physical
  intro m
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae (coefficient p r χ hχ) (StaticBallCentered.source (p j) (r j) P))
  filter_upwards [hs, StaticBallCentered.source_ae (p j) (r j) P m,
    StaticBallCentered.source_ae (p j) (r j) ((Real.sqrt χ : ℂ) • P) m] with x hs hp hq
  rw [hs]
  change (Real.sqrt ((coefficient p r χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
    StaticBallCentered.source (p j) (r j) P (VectorFourier.coordinateMap x) m = _
  rw [coefficient_value, hp, hq]
  by_cases hm : x ∈ ball (p j) (r j)
  · have hu : x ∈ ⋃ j, ball (p j) (r j) := mem_iUnion.mpr ⟨j, hm⟩
    simp [hm, hu]
  · simp [hm]

omit [DecidableEq ι] in
theorem sqrt_sumSource (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ) (P : ι → Vector) :
    StaticCoefficient.sqrtMultiplier (coefficient p r χ hχ) (sumSource p r P) =
      sumSource p r (fun j => (Real.sqrt χ : ℂ) • P j) := by
  simp only [sumSource, map_sum, sqrt_single]

def trial (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (E : ι → Vector) : VectorL2 :=
  sumSource p r (fun j => StaticSphereMaterial.trialVector χ (E j))

def forcing (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (E : ι → Vector) : VectorL2 :=
  sumSource p r (fun j => (Real.sqrt χ : ℂ) • E j)

omit [DecidableEq ι] in
theorem physical_trial (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ) (E : ι → Vector) :
    StaticCoefficient.sqrtMultiplier (coefficient p r χ hχ) (trial p r χ E) =
      sumSource p r (fun j => StaticSpherePolarization.polarization χ (E j)) := by
  unfold trial
  rw [sqrt_sumSource]
  congr 1
  funext j
  exact StaticSphereMaterial.trial_physical_vector χ hχ (E j)

theorem sumSource_eq_self_cross (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (i : ι) :
    sumSource p r P = StaticBallCentered.source (p i) (r i) (P i) +
      StaticBallInteraction.crossSource p r P i := by
  have he := Finset.sum_erase_add (Finset.univ : Finset ι)
    (fun j => StaticBallCentered.source (p j) (r j) (P j)) (Finset.mem_univ i)
  simpa only [sumSource, StaticBallInteraction.crossSource, add_comm] using he.symm

def supportData (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0 ≤ χ)
    (R : ℝ) (hinside : ∀ i, ‖p i‖+r i ≤ R) :
    BoundedMaterialKernel.SupportData (coefficient p r χ hχ) :=
  BoundedMaterialKernel.ofFiniteBalls (coefficient p r χ hχ) R p r hinside
    (fun x hx => by rw [coefficient_value, if_neg hx])

end OQ14.FiniteSphereStatic

#print axioms OQ14.FiniteSphereStatic.coefficient_value
#print axioms OQ14.FiniteSphereStatic.sumSource_ae
#print axioms OQ14.FiniteSphereStatic.other_ball_excluded
#print axioms OQ14.FiniteSphereStatic.sumSource_on_ball
#print axioms OQ14.FiniteSphereStatic.sqrt_single
#print axioms OQ14.FiniteSphereStatic.sqrt_sumSource
#print axioms OQ14.FiniteSphereStatic.physical_trial
#print axioms OQ14.FiniteSphereStatic.sumSource_eq_self_cross
#print axioms OQ14.FiniteSphereStatic.supportData
