import Packet06SchurAnalytic
import Mathlib.Analysis.NormedSpace.HahnBanach.SeparatingDual

/-! Actual electric-sector sphere pole reduced to a scalar simple zero. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SphereSchur
open Packet06SectorOperator Packet06SectorCrossing Packet06RankOneRepair Packet06ScalarSchur

theorem exists_normalizer {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (u : E) (hu : u ≠ 0) : ∃ ψ : E →L[ℂ] ℂ, ψ u = 1 := by
  obtain ⟨f,hf⟩ := SeparatingDual.exists_ne_zero (R := ℂ) hu
  refine ⟨(f u)⁻¹ • f,?_⟩
  change (f u)⁻¹ * f u = 1
  exact inv_mul_cancel₀ hf

theorem actual_scalar_reduction (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    ∃ (w : Sector) (ψ : Sector →L[ℂ] ℂ),
      ψ (numerator n hn z) = 1 ∧ leftFunctional n hn z w = 1 ∧
      IsUnit (repair (block n hn z) w ψ) ∧
      scalar (block n hn z) w ψ = 0 ∧
      AnalyticAt ℂ (fun v => scalar (block n hn v) w ψ) z ∧
      HasDerivAt (fun v => scalar (block n hn v) w ψ)
        (leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))) z ∧
      leftFunctional n hn z (blockDerivative n hn z (numerator n hn z)) ≠ 0 ∧
      (∀ v, IsUnit (repair (block n hn v) w ψ) →
        (IsUnit (block n hn v) ↔ scalar (block n hn v) w ψ ≠ 0)) := by
  have hN := numerator_kernel n hn z hz hd
  have hs := Packet06SpherePole.determinant_simple n hn hna z hz hd
  have hc := crossing_nonzero n hn z hz hd hs
  let d := leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))
  let w : Sector := d⁻¹ • blockDerivative n hn z (numerator n hn z)
  have hw : leftFunctional n hn z w = 1 := by
    change leftFunctional n hn z (d⁻¹ • blockDerivative n hn z (numerator n hn z)) = 1
    rw [map_smul,smul_eq_mul]
    exact inv_mul_cancel₀ hc
  obtain ⟨ψ,hψ⟩ := exists_normalizer (numerator n hn z) hN.1
  obtain ⟨R,B,_,_,_,_,_,_,hrange,_,_⟩ :=
    (Packet06SpherePole.actual_sector_pole_and_cokernel n hn hna z hz hd).2
  have hsur : ∀ y, leftFunctional n hn z y = 0 → ∃ x, block n hn z x = y := by
    intro y hy
    have hm : y ∈ LinearMap.range (block n hn z).toLinearMap := by
      rw [hrange]
      exact hy
    exact hm
  have hker : ∀ x, block n hn z x = 0 → ∃ a : ℂ, x = a • numerator n hn z := by
    intro x hx
    obtain ⟨a,ha,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd x).mp hx
    exact ⟨a,ha⟩
  have hC := repair_isUnit (block n hn z) (numerator n hn z) w (leftFunctional n hn z) ψ
    hN.2 hψ hw (left_annihilates n hn z hz hd) hker hsur
  have hanalytic : AnalyticAt ℂ (block n hn) z := by
    have he : block n hn = fun v => Sector.orthogonalProjection.comp
        ((ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) v 1).comp Sector.subtypeL) :=
      funext (block_eq_compression n hn)
    rw [he]
    have hW := (ComplexConvolutionAnalytic.volumeBlock_differentiable
      (ModalWeightedMode.coefficient n hn) 1 (by norm_num)).analyticAt z
    have h1 := (((ContinuousLinearMap.compL ℂ Sector VectorL2 VectorL2).flip Sector.subtypeL).analyticAt
      (ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1)).comp
        (f := fun v : ℂ => ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) v 1) hW
    exact ((ContinuousLinearMap.compL ℂ Sector VectorL2 Sector).analyticAt_bilinear
      (Sector.orthogonalProjection,(ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) z 1).comp Sector.subtypeL)).comp
        (f := fun v : ℂ => (Sector.orthogonalProjection,
          (ComplexConvolutionAnalytic.volumeBlock (ModalWeightedMode.coefficient n hn) v 1).comp Sector.subtypeL))
          (analyticAt_const.prod h1)
  exact ⟨w,ψ,hψ,hw,hC,scalar_zero _ _ _ _ hC hN.2 hψ,
    Packet06SchurAnalytic.scalar_analyticAt _ w ψ z hanalytic hC,
    Packet06SchurAnalytic.scalar_crossing _ _ _ _ _ _ z (block_hasDerivAt n hn z) hC hN.2 hψ hw
      (left_annihilates n hn z hz hd),hc,
    fun v hv => isUnit_iff_scalar (block n hn v) w ψ hv⟩

end OQ14.Packet06SphereSchur
#print axioms OQ14.Packet06SphereSchur.exists_normalizer
#print axioms OQ14.Packet06SphereSchur.actual_scalar_reduction
