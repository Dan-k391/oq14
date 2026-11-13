import Packet06SphereReduced

/-! Simple scalar crossing for the actual norm-stable weighted sphere pencil. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SphereReducedSchur
open Packet06SectorOperator Packet06SphereReduced Packet06RankOneRepair Packet06ScalarSchur

theorem actual_scalar_reduction (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    ∃ (w : Sector) (ψ : Sector →L[ℂ] ℂ),
      ψ (numerator n hn z) = 1 ∧ leftFunctional n hn z w = 1 ∧
      IsUnit (repair (pencil n hn z) w ψ) ∧
      scalar (pencil n hn z) w ψ = 0 ∧
      AnalyticAt ℂ (fun v => scalar (pencil n hn v) w ψ) z ∧
      HasDerivAt (fun v => scalar (pencil n hn v) w ψ)
        (leftFunctional n hn z (pencilDerivative n hn z (numerator n hn z))) z ∧
      leftFunctional n hn z (pencilDerivative n hn z (numerator n hn z)) ≠ 0 ∧
      (∀ v, IsUnit (repair (pencil n hn v) w ψ) →
        (IsUnit (pencil n hn v) ↔ scalar (pencil n hn v) w ψ ≠ 0)) := by
  have hN := numerator_kernel n hn z hz hd
  have hNF : pencil n hn z (numerator n hn z) = 0 := (pencil_kernel_iff n hn z _).mpr hN.2
  have hs := Packet06SpherePole.determinant_simple n hn hna z hz hd
  have hc : leftFunctional n hn z (pencilDerivative n hn z (numerator n hn z)) ≠ 0 := by
    rw [crossing_preserved]
    exact Packet06SectorCrossing.crossing_nonzero n hn z hz hd hs
  let d := leftFunctional n hn z (pencilDerivative n hn z (numerator n hn z))
  let w : Sector := d⁻¹ • pencilDerivative n hn z (numerator n hn z)
  have hw : leftFunctional n hn z w = 1 := by
    change leftFunctional n hn z (d⁻¹ • pencilDerivative n hn z (numerator n hn z)) = 1
    rw [map_smul,smul_eq_mul]
    exact inv_mul_cancel₀ hc
  obtain ⟨ψ,hψ⟩ := Packet06SphereSchur.exists_normalizer (numerator n hn z) hN.1
  obtain ⟨R,B,_,_,_,_,_,_,hrange,_,_⟩ :=
    (Packet06SpherePole.actual_sector_pole_and_cokernel n hn hna z hz hd).2
  have hrangeF : LinearMap.range (pencil n hn z).toLinearMap =
      LinearMap.ker (leftFunctional n hn z).toLinearMap :=
    Packet06LeftPreconditioner.range_eq_kernel _ _ (staticBlock_isUnit n hn) _ hrange
  have hsur : ∀ y, leftFunctional n hn z y = 0 → ∃ x, pencil n hn z x = y := by
    intro y hy
    have hm : y ∈ LinearMap.range (pencil n hn z).toLinearMap := by
      rw [hrangeF]
      exact hy
    exact hm
  have hker : ∀ x, pencil n hn z x = 0 → ∃ a : ℂ, x = a • numerator n hn z := by
    intro x hx
    obtain ⟨a,ha,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd x).mp
      ((pencil_kernel_iff n hn z x).mp hx)
    exact ⟨a,ha⟩
  have hleft : ∀ x, leftFunctional n hn z (pencil n hn z x) = 0 := by
    intro x
    change Packet06LeftPreconditioner.functional (staticBlock n hn)
      (Packet06SectorCrossing.leftFunctional n hn z)
      (Packet06LeftPreconditioner.pencil (staticBlock n hn) (block n hn z) x) = 0
    rw [Packet06LeftPreconditioner.pairing_undo _ _ (staticBlock_isUnit n hn)]
    exact Packet06SectorCrossing.left_annihilates n hn z hz hd x
  have hC := repair_isUnit (pencil n hn z) (numerator n hn z) w (leftFunctional n hn z) ψ
    hNF hψ hw hleft hker hsur
  exact ⟨w,ψ,hψ,hw,hC,scalar_zero _ _ _ _ hC hNF hψ,
    Packet06SchurAnalytic.scalar_analyticAt _ w ψ z (pencil_analyticAt n hn z) hC,
    Packet06SchurAnalytic.scalar_crossing _ _ _ _ _ _ z (pencil_hasDerivAt n hn z)
      hC hNF hψ hw hleft,hc,
    fun v hv => isUnit_iff_scalar (pencil n hn v) w ψ hv⟩

end OQ14.Packet06SphereReducedSchur
#print axioms OQ14.Packet06SphereReducedSchur.actual_scalar_reduction
