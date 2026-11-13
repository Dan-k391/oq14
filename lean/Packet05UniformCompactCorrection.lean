import Packet05UniformCompactGreen
import Packet05ContinuousH2Bound
import Packet05ActualCorrectionH2

/-! Uniform H2 and pointwise bounds for the actual complex Maxwell Green
correction, derived from its compact source and bounded frequency alone. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05UniformCompactCorrection
open MeasureTheory Set Metric Maxwell WeakCurl WeakPoynting DivCurlCompact

theorem uniform_compact_correction (R S Z : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S) (hZ : 0 ≤ Z)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball (0 : Space) R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : ℂ), ‖z‖ ≤ Z → ∀ (F : NewtonL2.ScalarL2) (ρ : Space → ℂ),
      (F : Space → ℂ) =ᵐ[volume] ρ → Integrable ρ → HasCompactSupport ρ →
      (∀ y, y ∉ closedBall 0 S → ρ y=0) →
      ∃ U : L2Scalar, ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial U (D i) i) ∧ (∀ i j, HasWeakPartial (D i) (T i j) j) ∧
        (∀ᵐ x ∂volume, U x=χ.function x*(z^2*KernelConvolution.response (ComplexGreenKernel.phi z) ρ x)) ∧
        ‖U‖ ≤ C*‖F‖ ∧ (∀ i, ‖D i‖ ≤ C*‖F‖) ∧ (∀ i j, ‖T i j‖ ≤ C*‖F‖) ∧
        ∀ x, χ.function x=1 → ‖z^2*KernelConvolution.response (ComplexGreenKernel.phi z) ρ x‖ ≤
          10*Packet05ExplicitAnisotropicBound.universalConstant*(C*‖F‖) := by
  obtain ⟨C,hC,hall⟩ := Packet05UniformCompactGreen.uniform_compact_green R S Z hR hS hZ χ hχ2 hχR
  refine ⟨Z^2*C,mul_nonneg (sq_nonneg Z) hC,?_⟩
  intro z hz F ρ hF hρ hcompact hs
  obtain ⟨U,D,T,hD,hT,hval,hUn,hDn,hTn⟩ := hall z hz F ρ hF hρ hcompact hs
  have hz2 : ‖z‖^2 ≤ Z^2 := (sq_le_sq₀ (norm_nonneg z) hZ).mpr hz
  have hnorm (v : L2Scalar) (hv : ‖v‖ ≤ C*‖F‖) : ‖z^2 • v‖ ≤ (Z^2*C)*‖F‖ := by
    rw [norm_smul,norm_pow]
    exact (mul_le_mul hz2 hv (norm_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  let f := fun x => χ.function x*(z^2*KernelConvolution.response (ComplexGreenKernel.phi z) ρ x)
  have hUf : (z^2 • U : L2Scalar) =ᵐ[volume] f := by
    filter_upwards [Lp.coeFn_smul (z^2) U,hval] with x hx hv
    rw [hx]
    simp only [Pi.smul_apply,smul_eq_mul,hv,f]
    ring
  have hf : Continuous f := χ.regular.continuous.mul (continuous_const.mul
    (Packet06ComplexScalarPotential.response_continuous z S ρ F hF hs))
  have hfc : HasCompactSupport f := χ.compact.mul_right
  have hD' (i : Fin 3) := Packet05ActualCorrectionH2.weak_partial_smul (z^2) U (D i) i (hD i)
  have hT' (i j : Fin 3) := Packet05ActualCorrectionH2.weak_partial_smul (z^2) (D i) (T i j) j (hT i j)
  refine ⟨z^2 • U,fun i => z^2 • D i,fun i j => z^2 • T i j,hD',hT',hUf,
    hnorm U hUn,fun i => hnorm (D i) (hDn i),fun i j => hnorm (T i j) (hTn i j),?_⟩
  intro x hx
  have hb := Packet05ContinuousH2Bound.continuous_h2_bound (z^2 • U) f hf hfc hUf
    (fun i => z^2 • D i) (fun i j => z^2 • T i j) hD' hT' ((Z^2*C)*‖F‖)
    (hnorm U hUn) (fun i => hnorm (D i) (hDn i)) (fun i j => hnorm (T i j) (hTn i j)) x
  simpa only [f,hx,one_mul] using hb

end OQ14.Packet05UniformCompactCorrection
#print axioms OQ14.Packet05UniformCompactCorrection.uniform_compact_correction
