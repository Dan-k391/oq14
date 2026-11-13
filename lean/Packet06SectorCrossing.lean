import Packet06SectorOperator
import ModalVolumeNormalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SectorCrossing
open Complex OQ14.Packet06SectorOperator OQ14.ModalWeightedMode OQ14.ModalVolumeNormalization
open scoped Topology

theorem block_eq_compression (n : ℝ) (hn : 1 < n) (z : ℂ) :
    block n hn z = Sector.orthogonalProjection.comp
      ((ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1).comp Sector.subtypeL) := by
  apply ContinuousLinearMap.ext
  intro u
  change (⟨ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u,
    ModalMeridionalVolume.electricSector_invariant n hn z u u.property⟩ : Sector) =
      Sector.orthogonalProjection (ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) z 1 u)
  exact (Submodule.orthogonalProjection_mem_subspace_eq_self _).symm

def blockDerivative (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] Sector :=
  Sector.orthogonalProjection.comp
    ((deriv (fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) w 1) z).comp Sector.subtypeL)

theorem block_hasDerivAt (n : ℝ) (hn : 1 < n) (z : ℂ) :
    HasDerivAt (block n hn) (blockDerivative n hn z) z := by
  have ha := (ComplexConvolutionAnalytic.volumeBlock_differentiable (coefficient n hn) 1 (by norm_num) z).hasDerivAt
  have h1 := ha.clm_comp (hasDerivAt_const z Sector.subtypeL)
  have h2 := (hasDerivAt_const z Sector.orthogonalProjection).clm_comp h1
  have he : block n hn = fun w => Sector.orthogonalProjection.comp
      ((ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) w 1).comp Sector.subtypeL) :=
    funext (block_eq_compression n hn)
  rw [he]
  simpa only [blockDerivative, ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero, zero_add, add_zero] using h2

theorem block_derivative_actual (n : ℝ) (hn : 1 < n) (z : ℂ) (u : Sector) :
    ((blockDerivative n hn z u : Sector) : VectorL2) =
      deriv (fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) w 1) z u := by
  have h1 := ((block_hasDerivAt n hn z).clm_apply (hasDerivAt_const z u))
  have h2 := (((ComplexConvolutionAnalytic.volumeBlock_differentiable
    (coefficient n hn) 1 (by norm_num) z).hasDerivAt).clm_apply (hasDerivAt_const z (u : VectorL2)))
  have h3 := Sector.subtypeL.hasFDerivAt.comp_hasDerivAt z h1
  have he : (fun w => (block n hn w u : VectorL2)) =
      fun w => ComplexConvolutionAnalytic.volumeBlock (coefficient n hn) w 1 u := by
    funext w
    exact block_actual n hn w u
  change HasDerivAt (fun w => (block n hn w u : VectorL2)) _ z at h3
  rw [he] at h3
  have hh := h3.unique h2
  simpa only [map_zero, add_zero] using hh

def leftFunctional (n : ℝ) (hn : 1 < n) (z : ℂ) : Sector →L[ℂ] ℂ :=
  (ComplexVolumeReciprocity.pairFunctional (numerator n hn z : VectorL2)).comp Sector.subtypeL

theorem left_annihilates (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) (v : Sector) :
    leftFunctional n hn z (block n hn z v) = 0 := by
  exact ModalVolumeNormalization.kernel_left_functional n hn z (numerator n hn z : VectorL2)
    (ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hd).2 v

theorem crossing_nonzero (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (hs : deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z ≠ 0) :
    leftFunctional n hn z (blockDerivative n hn z (numerator n hn z)) ≠ 0 := by
  change OQ14.KernelReciprocity.vectorPair
    ((blockDerivative n hn z (numerator n hn z) : Sector) : VectorL2)
      (ModalVolumeData.numerator n hn z) ≠ 0
  rw [block_derivative_actual]
  exact numerator_pairing_nonzero n hn z hz hd hs

#print axioms OQ14.Packet06SectorCrossing.block_eq_compression
#print axioms OQ14.Packet06SectorCrossing.block_hasDerivAt
#print axioms OQ14.Packet06SectorCrossing.block_derivative_actual
#print axioms OQ14.Packet06SectorCrossing.left_annihilates
#print axioms OQ14.Packet06SectorCrossing.crossing_nonzero
end OQ14.Packet06SectorCrossing
