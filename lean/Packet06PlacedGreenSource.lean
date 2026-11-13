import Packet06PlacedGreenActual
import Packet06PlacedGreenSupport
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedGreenSource
open MeasureTheory Maxwell Packet06PlacedEquivalence Packet06PlacedProjection
open Packet06CyclicRotation Packet06CyclicRotationMaxwell Packet06ProjectedGreen
abbrev V := VectorFourier.VectorL2

/-- The placed orthogonal projection is represented by the transformed base projection. -/
theorem projection_ae (s : ℝ) (hs : 0 < s) (a : Space) (f : V) (i : Fin 3) :
    (fun x : Space => ((placedSector s hs a).orthogonalProjection f : V)
      (VectorFourier.coordinateMap x) i) =ᵐ[volume]
    fun x => ((Real.sqrt s*s : ℝ) : ℂ) * rotateField
      (fun y => project ((placed s hs a).symm f) (VectorFourier.coordinateMap y))
      (s • (x-a)) i := by
  have hp := projected_transport s hs a f
  have he := Packet06PlacedAction.placed_unknown_ae s hs a (project ((placed s hs a).symm f)) i
  have hx : ((placedSector s hs a).orthogonalProjection f : V) =
      Packet06PlacedKernel.placedUnknown s a (project ((placed s hs a).symm f)) := by
    rw [hp]
    rfl
  rw [hx]
  simpa only [rotateField] using he

/-- The placed actual field solves Maxwell with the placed sector projection of f. -/
theorem global_maxwell (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (S J : ℝ) (hS : 0 ≤ S) (hJ : 0 ≤ J)
    (hc : ∀ x : Space, x ∉ Metric.closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (z : ℂ) (hz : z ≠ 0) (hunit : IsUnit (Packet06MaterialSector.pencil c S z)) (f : V)
    (s : ℝ) (hs : 0 < s) (a : Space)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ Metric.closedBall 0 J →
      ((placed s hs a).symm f) (VectorFourier.coordinateMap x) = 0) :
    Packet06PlacedGreenMaxwell.weakSecond ((s : ℂ)*z)
      (fun x => 1+c.value (VectorFourier.coordinateMap (unrotate (s • (x-a)))))
      (fun x => (((s : ℂ)^2)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) • rotateField
        (Packet06ProjectedGlobal.field c S J z ((placed s hs a).symm f)) (s • (x-a)))
      (fun x => ((placedSector s hs a).orthogonalProjection f : V) (VectorFourier.coordinateMap x)) := by
  have h := Packet06PlacedGreenActual.transformed_global_maxwell c ha hm S J hS hJ hc z hz hunit
    ((placed s hs a).symm f) hf s hs a (((s : ℂ)^2)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ))
  intro i φ
  have hh := h i φ
  have hp := projection_ae s hs a f i
  have hi : MaterialMaxwell.fieldPair
      (fun x => (((s : ℂ)^2)⁻¹ * ((Real.sqrt s*s : ℝ) : ℂ)) •
        ((s : ℂ)^2 • rotateField (fun y => project ((placed s hs a).symm f)
          (VectorFourier.coordinateMap y)) (s • (x-a)))) i φ =
      MaterialMaxwell.fieldPair (fun x => ((placedSector s hs a).orthogonalProjection f : V)
        (VectorFourier.coordinateMap x)) i φ := by
    unfold MaterialMaxwell.fieldPair
    apply integral_congr_ae
    filter_upwards [hp] with x hx
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx]
    have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    field_simp
    ring
  rw [hi] at hh
  exact hh

#print axioms OQ14.Packet06PlacedGreenSource.global_maxwell
#print axioms OQ14.Packet06PlacedGreenSource.projection_ae
end OQ14.Packet06PlacedGreenSource
