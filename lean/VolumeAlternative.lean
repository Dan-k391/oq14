import VolumeFredholm
import CompactAlternative

/-! # Unique solvability from homogeneous volume uniqueness

Compact support gives a genuine compact dynamic remainder. Homogeneous
uniqueness is the explicit remaining input; it is not a proved PDE theorem
in this file. No smallness condition on the support or contrast is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.VolumeAlternative

open Metric OQ14.DynamicConvolution
open OQ14.StaticCoefficient (Coefficient)

theorem injective_of_kernel_trivial (c : Coefficient) (k R : ℝ)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0) :
    Function.Injective (DynamicVolume.volumeBlock c k R) := by
  intro u v huv
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, huv, sub_self]

theorem preconditioned_injective (c : Coefficient) (k R : ℝ)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0) :
    Function.Injective (CompactPerturbation.defect (VolumeFredholm.compactPart c k R)) := by
  intro u v huv
  apply injective_of_kernel_trivial c k R hzero
  simpa only [VolumeFredholm.volumeBlock_factor, ContinuousLinearMap.mul_apply] using
    congrArg (StaticNewton.volumeBlock c) huv

theorem surjective_of_kernel_trivial (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0) :
    Function.Surjective (DynamicVolume.volumeBlock c k R) := by
  have hs := CompactAlternative.surjective_of_injective
    (VolumeFredholm.compactPart c k R) (VolumeFredholm.compactPart_compact c k R hc)
    (preconditioned_injective c k R hzero)
  intro f
  obtain ⟨u, hu⟩ := hs (Ring.inverse (StaticNewton.volumeBlock c) f)
  refine ⟨u, ?_⟩
  rw [VolumeFredholm.volumeBlock_factor]
  change StaticNewton.volumeBlock c
    (CompactPerturbation.defect (VolumeFredholm.compactPart c k R) u) = f
  rw [hu]
  exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel _ (StaticNewton.volumeBlock_isUnit c))

theorem volumeBlock_isUnit (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0) :
    IsUnit (DynamicVolume.volumeBlock c k R) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨injective_of_kernel_trivial c k R hzero, surjective_of_kernel_trivial c k R hc hzero⟩

theorem inverse_apply_volumeBlock (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0)
    (u : VectorL2) :
    Ring.inverse (DynamicVolume.volumeBlock c k R) (DynamicVolume.volumeBlock c k R u) = u :=
  congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L u)
    (Ring.inverse_mul_cancel _ (volumeBlock_isUnit c k R hc hzero))

theorem volumeBlock_apply_inverse (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0)
    (f : VectorL2) :
    DynamicVolume.volumeBlock c k R (Ring.inverse (DynamicVolume.volumeBlock c k R) f) = f :=
  congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L f)
    (Ring.mul_inverse_cancel _ (volumeBlock_isUnit c k R hc hzero))

theorem existsUnique_solution (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0)
    (f : VectorL2) :
    ∃! u : VectorL2, DynamicVolume.volumeBlock c k R u = f := by
  refine ⟨Ring.inverse (DynamicVolume.volumeBlock c k R) f,
    volumeBlock_apply_inverse c k R hc hzero f, ?_⟩
  intro u hu
  exact injective_of_kernel_trivial c k R hzero
    (hu.trans (volumeBlock_apply_inverse c k R hc hzero f).symm)

theorem solution_norm_bound (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hzero : ∀ u : VectorL2, DynamicVolume.volumeBlock c k R u = 0 → u = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ u f : VectorL2,
      DynamicVolume.volumeBlock c k R u = f → ‖u‖ ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := VolumeFredholm.orthogonal_kernel_bound c k R hc
  refine ⟨C, hC, ?_⟩
  intro u f hsol
  have hu : u ∈ (LinearMap.ker (DynamicVolume.volumeBlock c k R))ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro v hv
    rw [hzero v hv]
    simp
  simpa only [hsol] using hb u hu

end OQ14.VolumeAlternative

#print axioms OQ14.VolumeAlternative.injective_of_kernel_trivial
#print axioms OQ14.VolumeAlternative.preconditioned_injective
#print axioms OQ14.VolumeAlternative.surjective_of_kernel_trivial
#print axioms OQ14.VolumeAlternative.volumeBlock_isUnit
#print axioms OQ14.VolumeAlternative.inverse_apply_volumeBlock
#print axioms OQ14.VolumeAlternative.volumeBlock_apply_inverse
#print axioms OQ14.VolumeAlternative.existsUnique_solution
#print axioms OQ14.VolumeAlternative.solution_norm_bound
