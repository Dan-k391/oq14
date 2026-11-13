import Packet06ModePolePersistence

/-! Actual kernel and simple Schur data retained for subsequent material
perturbations, including rounding after the cone contrast is selected. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06SimpleCertificate
open Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open Packet06MaterialSector (pencil)

def Certified (c : StaticCoefficient.Coefficient) (S : ℝ) (z : ℂ) (u : Sector) : Prop :=
  ∃ (w : Sector) (ψ : Sector →L[ℂ] ℂ),
    IsUnit (repair (pencil c S z) w ψ) ∧
    ComplexConvolutionAnalytic.volumeBlock c z S u = 0 ∧ ψ u = 1 ∧
    deriv (fun v => scalar (pencil c S v) w ψ) z ≠ 0

theorem certified_nonzero (c : StaticCoefficient.Coefficient) (S : ℝ) (z : ℂ) (u : Sector)
    (h : Certified c S z u) : u ≠ 0 := by
  obtain ⟨w,ψ,_,_,hψ,_⟩ := h
  intro hu
  rw [hu,map_zero] at hψ
  exact zero_ne_one hψ

theorem repair_scale (A : Sector →L[ℂ] Sector) (w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (a : ℂ) (ha : a ≠ 0) : repair A (a • w) (a⁻¹ • ψ) = repair A w ψ := by
  ext x
  simp only [repair_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,smul_smul]
  have h : (a⁻¹ * ψ x) * a = ψ x := by field_simp
  rw [h]

theorem scalar_scale (A : Sector →L[ℂ] Sector) (w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (a : ℂ) (ha : a ≠ 0) : scalar A (a • w) (a⁻¹ • ψ) = scalar A w ψ := by
  unfold scalar
  rw [repair_scale A w ψ a ha,map_smul]
  simp only [ContinuousLinearMap.smul_apply,map_smul,smul_eq_mul]
  rw [←mul_assoc,mul_inv_cancel₀ ha,one_mul]

theorem certified_scale (c : StaticCoefficient.Coefficient) (S : ℝ) (z : ℂ) (u : Sector)
    (h : Certified c S z u) (a : ℂ) (ha : a ≠ 0) : Certified c S z (a • u) := by
  obtain ⟨w,ψ,hunit,hker,hψ,hder⟩ := h
  refine ⟨a • w,a⁻¹ • ψ,?_,?_,?_,?_⟩
  · rwa [repair_scale _ w ψ a ha]
  · change ComplexConvolutionAnalytic.volumeBlock c z S (a • (u : VectorL2)) = 0
    rw [map_smul,hker,smul_zero]
  · simp only [ContinuousLinearMap.smul_apply,map_smul,hψ,smul_eq_mul,mul_one,mul_inv_cancel₀ ha]
  · simpa only [scalar_scale _ w ψ a ha] using hder

end OQ14.Packet06SimpleCertificate
#print axioms OQ14.Packet06SimpleCertificate.certified_nonzero
#print axioms OQ14.Packet06SimpleCertificate.repair_scale
#print axioms OQ14.Packet06SimpleCertificate.scalar_scale
#print axioms OQ14.Packet06SimpleCertificate.certified_scale
