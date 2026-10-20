import DynamicVolumeCompact
import CompactPerturbation

/-! # Actual static preconditioning and Fredholm kernel/range properties

The compact operator is built from the physical dynamic dyadic convolution.
No support-radius or contrast smallness condition is imposed here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.VolumeFredholm

open Metric OQ14.DynamicConvolution
open OQ14.StaticCoefficient (Coefficient)

def compactPart (c : Coefficient) (k R : ℝ) : VectorL2 →L[ℂ] VectorL2 :=
  (Ring.inverse (StaticNewton.volumeBlock c)).comp (DynamicVolume.weightedRemainder c k R)

theorem compactPart_compact (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsCompactOperator (compactPart c k R) :=
  (DynamicVolumeCompact.weightedRemainder_compact c k R hc).clm_comp _

theorem preconditioned_eq (c : Coefficient) (k R : ℝ) :
    Ring.inverse (StaticNewton.volumeBlock c) * DynamicVolume.volumeBlock c k R =
      CompactPerturbation.defect (compactPart c k R) := by
  change Ring.inverse (StaticNewton.volumeBlock c) *
    (StaticNewton.volumeBlock c - DynamicVolume.weightedRemainder c k R) =
      1 - Ring.inverse (StaticNewton.volumeBlock c) * DynamicVolume.weightedRemainder c k R
  rw [mul_sub, Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit c)]

theorem volumeBlock_factor (c : Coefficient) (k R : ℝ) :
    DynamicVolume.volumeBlock c k R =
      StaticNewton.volumeBlock c * CompactPerturbation.defect (compactPart c k R) := by
  rw [← preconditioned_eq, ← mul_assoc,
    Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c), one_mul]

theorem kernel_eq (c : Coefficient) (k R : ℝ) :
    LinearMap.ker (DynamicVolume.volumeBlock c k R) =
      LinearMap.ker (CompactPerturbation.defect (compactPart c k R)) := by
  ext x
  change DynamicVolume.volumeBlock c k R x = 0 ↔
    CompactPerturbation.defect (compactPart c k R) x = 0
  rw [volumeBlock_factor]
  change StaticNewton.volumeBlock c
    (CompactPerturbation.defect (compactPart c k R) x) = 0 ↔ _
  exact (ContinuousLinearMap.isUnit_iff_bijective.mp (StaticNewton.volumeBlock_isUnit c)).1.eq_iff'
    (map_zero _)

theorem kernel_finiteDimensional (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    FiniteDimensional ℂ (LinearMap.ker (DynamicVolume.volumeBlock c k R)) := by
  rw [kernel_eq]
  exact CompactPerturbation.kernel_finiteDimensional _ (compactPart_compact c k R hc)

theorem range_closed (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    IsClosed (Set.range (DynamicVolume.volumeBlock c k R)) := by
  have he : Set.range (DynamicVolume.volumeBlock c k R) =
      (fun y => (Ring.inverse (StaticNewton.volumeBlock c)) y) ⁻¹'
        Set.range (CompactPerturbation.defect (compactPart c k R)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨x, ?_⟩
      exact (congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L x) (preconditioned_eq c k R)).symm
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [volumeBlock_factor]
      change StaticNewton.volumeBlock c
        (CompactPerturbation.defect (compactPart c k R) x) = y
      rw [hx]
      exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L y)
        (Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c))
  rw [he]
  exact (CompactPerturbation.range_closed _ (compactPart_compact c k R hc)).preimage
    (Ring.inverse (StaticNewton.volumeBlock c)).continuous

theorem orthogonal_kernel_bound (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ (LinearMap.ker (DynamicVolume.volumeBlock c k R))ᗮ,
      ‖u‖ ≤ C * ‖DynamicVolume.volumeBlock c k R u‖ := by
  obtain ⟨C, hC, hb⟩ := CompactPerturbation.orthogonal_norm_bound _
    (compactPart_compact c k R hc)
  refine ⟨C,hC,?_⟩
  intro u hu
  rw [kernel_eq] at hu
  apply (hb u hu).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  rw [← preconditioned_eq]
  have hn := mul_le_mul_of_nonneg_right
    (StaticNewton.volumeBlock_inverse_norm_le c) (norm_nonneg (DynamicVolume.volumeBlock c k R u))
  exact ((Ring.inverse (StaticNewton.volumeBlock c)).le_opNorm _).trans (by simpa using hn)

end OQ14.VolumeFredholm

#print axioms OQ14.VolumeFredholm.compactPart_compact
#print axioms OQ14.VolumeFredholm.preconditioned_eq
#print axioms OQ14.VolumeFredholm.volumeBlock_factor
#print axioms OQ14.VolumeFredholm.kernel_eq
#print axioms OQ14.VolumeFredholm.kernel_finiteDimensional
#print axioms OQ14.VolumeFredholm.range_closed
#print axioms OQ14.VolumeFredholm.orthogonal_kernel_bound
