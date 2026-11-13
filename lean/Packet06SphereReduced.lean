import Packet06LeftPreconditioner

/-! The actual preconditioned weighted sphere pencil in the electric sector. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SphereReduced
open Packet06SectorOperator Packet06SectorCrossing ModalWeightedMode

def staticBlock (n : ℝ) (hn : 1 < n) : Sector →L[ℂ] Sector := block n hn 0
def pencil (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] Sector :=
  Packet06LeftPreconditioner.pencil (staticBlock n hn) (block n hn z)
def leftFunctional (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] ℂ :=
  Packet06LeftPreconditioner.functional (staticBlock n hn)
    (Packet06SectorCrossing.leftFunctional n hn z)
def pencilDerivative (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] Sector :=
  Packet06LeftPreconditioner.pencil (staticBlock n hn) (blockDerivative n hn z)

theorem staticBlock_isUnit (n : ℝ) (hn : 1 < n) : IsUnit (staticBlock n hn) := by
  obtain ⟨hl,hr⟩ := compressedInverse_two_sided n hn 0
    (ComplexConvolutionAnalytic.volumeBlock_zero_isUnit (coefficient n hn) 1)
  exact ⟨⟨block n hn 0,compressedInverse n hn 0,hl,hr⟩,rfl⟩

theorem staticBlock_actual (n : ℝ) (hn : 1 < n) (u : Sector) :
    ((staticBlock n hn u : Sector) : VectorL2) = StaticNewton.volumeBlock (coefficient n hn) u := by
  change ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) 0 1 u = _
  rw [ComplexConvolutionAnalytic.volumeBlock,ComplexConvolutionAnalytic.weightedRemainder_zero,sub_zero]

theorem staticInverse_actual (n : ℝ) (hn : 1 < n) (u : Sector) :
    ((Ring.inverse (staticBlock n hn) u : Sector) : VectorL2) =
      Ring.inverse (StaticNewton.volumeBlock (coefficient n hn)) u := by
  let v : Sector := Ring.inverse (staticBlock n hn) u
  have hv : staticBlock n hn v = u :=
    congrArg (fun L : Sector →L[ℂ] Sector => L u)
      (Ring.mul_inverse_cancel _ (staticBlock_isUnit n hn))
  have he := congrArg Subtype.val hv
  rw [staticBlock_actual] at he
  have h := congrArg (fun y : VectorL2 => Ring.inverse (StaticNewton.volumeBlock (coefficient n hn)) y) he
  dsimp only at h
  have hl := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (v : VectorL2))
    (Ring.inverse_mul_cancel _ (StaticNewton.volumeBlock_isUnit (coefficient n hn)))
  change Ring.inverse (StaticNewton.volumeBlock (coefficient n hn))
    (StaticNewton.volumeBlock (coefficient n hn) v) = (v : VectorL2) at hl
  rw [hl] at h
  exact h

theorem pencil_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : Sector) :
    ((pencil n hn z u : Sector) : VectorL2) =
      ComplexConvolutionAnalytic.pencil (coefficient n hn) z 1 u := by
  change ((Ring.inverse (staticBlock n hn) (block n hn z u) : Sector) : VectorL2) = _
  rw [staticInverse_actual,block_actual,←ComplexConvolutionAnalytic.preconditioned_eq]
  rfl

theorem pencil_eq_compression (n : ℝ) (hn : 1 < n) (z : ℂ) :
    pencil n hn z = Sector.orthogonalProjection.comp
      ((ComplexConvolutionAnalytic.pencil (coefficient n hn) z 1).comp Sector.subtypeL) := by
  apply ContinuousLinearMap.ext
  intro u
  change pencil n hn z u = Sector.orthogonalProjection
    (ComplexConvolutionAnalytic.pencil (coefficient n hn) z 1 u)
  rw [←pencil_actual]
  exact (Submodule.orthogonalProjection_mem_subspace_eq_self _).symm

theorem pencil_analyticAt (n : ℝ) (hn : 1 < n) (z : ℂ) :
    AnalyticAt ℂ (pencil n hn) z := by
  have he : pencil n hn = fun v => Sector.orthogonalProjection.comp
      ((ComplexConvolutionAnalytic.pencil (coefficient n hn) v 1).comp Sector.subtypeL) :=
    funext (pencil_eq_compression n hn)
  rw [he]
  have hW := ComplexConvolutionAnalytic.pencil_analyticAt (coefficient n hn) z 1 (by norm_num)
  have h1 := (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip Sector.subtypeL).analyticAt
    (ComplexConvolutionAnalytic.pencil (coefficient n hn) z 1)).comp
      (f := fun v : ℂ => ComplexConvolutionAnalytic.pencil (coefficient n hn) v 1) hW
  exact ((ContinuousLinearMap.compL ℂ Sector VectorL2 Sector).analyticAt_bilinear
    (Sector.orthogonalProjection,(ComplexConvolutionAnalytic.pencil (coefficient n hn) z 1).comp Sector.subtypeL)).comp
      (f := fun v : ℂ => (Sector.orthogonalProjection,
        (ComplexConvolutionAnalytic.pencil (coefficient n hn) v 1).comp Sector.subtypeL))
        (analyticAt_const.prod h1)

theorem pencil_kernel_iff (n : ℝ) (hn : 1 < n) (z : ℂ) (u : Sector) :
    pencil n hn z u = 0 ↔ block n hn z u = 0 :=
  Packet06LeftPreconditioner.kernel_iff _ _ (staticBlock_isUnit n hn) u

theorem pencil_hasDerivAt (n : ℝ) (hn : 1 < n) (z : ℂ) :
    HasDerivAt (pencil n hn) (pencilDerivative n hn z) z :=
  Packet06LeftPreconditioner.hasDerivAt _ _ _ z (block_hasDerivAt n hn z)

theorem crossing_preserved (n : ℝ) (hn : 1 < n) (z : ℂ) (u : Sector) :
    leftFunctional n hn z (pencilDerivative n hn z u) =
      Packet06SectorCrossing.leftFunctional n hn z (blockDerivative n hn z u) :=
  Packet06LeftPreconditioner.pairing_undo _ _ (staticBlock_isUnit n hn) _ u

end OQ14.Packet06SphereReduced
#print axioms OQ14.Packet06SphereReduced.staticBlock_isUnit
#print axioms OQ14.Packet06SphereReduced.staticBlock_actual
#print axioms OQ14.Packet06SphereReduced.staticInverse_actual
#print axioms OQ14.Packet06SphereReduced.pencil_actual
#print axioms OQ14.Packet06SphereReduced.pencil_eq_compression
#print axioms OQ14.Packet06SphereReduced.pencil_analyticAt
#print axioms OQ14.Packet06SphereReduced.pencil_kernel_iff
#print axioms OQ14.Packet06SphereReduced.pencil_hasDerivAt
#print axioms OQ14.Packet06SphereReduced.crossing_preserved
