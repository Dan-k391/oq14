import Packet06CertifiedNormalization
import Packet06HighQualityBranch

/-! Actual sphere modes with physical normalization and reusable simple Schur data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06CertifiedSphere
open Metric Packet06SectorOperator Packet06SimpleCertificate
open Packet06PhysicalNormalization (reciprocalNorm)

theorem sphere_certificate (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (z : ℂ) (hz : z ≠ 0) (hdet : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    Certified (ModalWeightedMode.coefficient n hn) 1 z (numerator n hn z) := by
  obtain ⟨w,ψ,hψ,_,hunit,_,_,hder,hd,_⟩ :=
    Packet06SphereReducedSchur.actual_scalar_reduction n hn hna z hz hdet
  rw [←Packet06MaterialSector.sphere_pencil n hn] at hunit hder
  exact ⟨w,ψ,hunit,(ModalSphereVolumeKernel.numerator_in_kernel n hn z hz hdet).2,
    hψ,by rw [hder.deriv]; exact hd⟩

theorem physically_normalized_highQ_sphere (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ (z a : ℂ), z ≠ 0 ∧ a ≠ 0 ∧ ModalAlgebra.tmDet 1 (n : ℂ) z = 0 ∧
      0 < z.re ∧ z.im < 0 ∧ Q < z.re / (-2*z.im) ∧
      Certified (ModalWeightedMode.coefficient n hn) 1 z (a • numerator n hn z) ∧
      reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z (a • (numerator n hn z : VectorL2)) = 1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode (ModalWeightedMode.coefficient n hn)
        z 1 (a • (numerator n hn z : VectorL2)) := by
  obtain ⟨z,hz,hdet,_,hre,him,hquality⟩ := ModalAsymptotics.tm_high_quality_zeros 1 n hn 0 Q hQ
  have hcert := sphere_certificate n hn hna z hz hdet
  have hN : reciprocalNorm (ModalWeightedMode.coefficient n hn) 1 z (numerator n hn z) ≠ 0 :=
    Packet06PhysicalNormalization.reciprocalNorm_nonzero _ 1 (by norm_num) z hz _
      (ModalVolumeNormalization.numerator_pairing_nonzero n hn z hz hdet
        (Packet06SpherePole.determinant_simple n hn hna z hz hdet))
  obtain ⟨a,ha,_,hunit⟩ := Packet06PhysicalScale.physical_unit_scale
    (ModalWeightedMode.coefficient n hn) 1 (by norm_num) z (numerator n hn z) hN
  have hc := certified_scale _ 1 z (numerator n hn z) hcert a ha
  have hne : (a • (numerator n hn z : VectorL2)) ≠ 0 := fun h =>
    certified_nonzero _ 1 z (a • numerator n hn z) hc (Subtype.ext h)
  have hk := hc.choose_spec.choose_spec.2.1
  exact ⟨z,a,hz,ha,hdet,hre,him,hquality,hc,hunit,
    Packet06OutgoingMode.actual_outgoing_mode _ z 1 (by norm_num) _
      (ModalWeightedMode.coefficient_support n hn) hk hne⟩

end OQ14.Packet06CertifiedSphere
#print axioms OQ14.Packet06CertifiedSphere.sphere_certificate
#print axioms OQ14.Packet06CertifiedSphere.physically_normalized_highQ_sphere
