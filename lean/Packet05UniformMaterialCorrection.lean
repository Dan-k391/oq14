import Packet05UniformCompactCorrection
import Packet05RoundedModeSupport

/-! Actual material sources with common support, susceptibility, frequency
and mode-norm bounds supply one compact H2 and pointwise correction bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05UniformMaterialCorrection
open MeasureTheory Set Metric Maxwell WeakCurl WeakPoynting DivCurlCompact

theorem material_source_norm (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2)
    (B L : ℝ) (hB : c.bound ≤ B) (hL : ‖u‖ ≤ L) (i : Fin 3) :
    ‖NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) i‖ ≤ Real.sqrt B*L := by
  exact (DynamicConvolution.component_norm i _).trans
    ((StaticCoefficient.applySqrt_norm c u).trans
      (mul_le_mul (Real.sqrt_le_sqrt hB) hL (norm_nonneg _) (Real.sqrt_nonneg _)))

theorem material_family_correction {A : Type*} (c : A → StaticCoefficient.Coefficient)
    (z : A → ℂ) (u : A → VectorFourier.VectorL2) (R S Z B L : ℝ)
    (hR : 0 ≤ R) (hS : 0 ≤ S) (hZ : 0 ≤ Z) (hL : 0 ≤ L)
    (hc : ∀ a x, x ∉ closedBall (0 : Space) S → (c a).value (VectorFourier.coordinateMap x)=0)
    (hb : ∀ a, (c a).bound ≤ B) (hz : ∀ a, ‖z a‖ ≤ Z) (hu : ∀ a, ‖u a‖ ≤ L)
    (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function) (hχR : tsupport χ.function ⊆ ball (0 : Space) R) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a k,
      ∃ U : L2Scalar, ∃ D : Fin 3 → L2Scalar, ∃ T : Fin 3 → Fin 3 → L2Scalar,
        (∀ i, HasWeakPartial U (D i) i) ∧ (∀ i j, HasWeakPartial (D i) (T i j) j) ∧
        (∀ᵐ x ∂volume, U x=χ.function x*Packet06ComplexPotential.correction (z a) (DynamicVolume.source (c a) (u a)) x k) ∧
        ‖U‖ ≤ N ∧ (∀ i, ‖D i‖ ≤ N) ∧ (∀ i j, ‖T i j‖ ≤ N) ∧
        ∀ x, χ.function x=1 → ‖Packet06ComplexPotential.correction (z a) (DynamicVolume.source (c a) (u a)) x k‖ ≤
          10*Packet05ExplicitAnisotropicBound.universalConstant*N := by
  obtain ⟨C,hC,hall⟩ := Packet05UniformCompactCorrection.uniform_compact_correction R S Z hR hS hZ χ hχ2 hχR
  refine ⟨C*(Real.sqrt B*L),mul_nonneg hC (mul_nonneg (Real.sqrt_nonneg _) hL),?_⟩
  intro a k
  obtain ⟨U,D,T,hD,hT,hval,hUn,hDn,hTn,hpoint⟩ := hall (z a) (hz a)
    (NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier (c a) (u a)) k)
    (DynamicVolume.source (c a) (u a) k) (StaticNewton.material_source_ae (c a) (u a) k)
    (DynamicVolume.source_integrable (c a) (u a) S (hc a) k)
    (MaterialField.source_compact (c a) (u a) S (hc a) k)
    (DynamicVolume.source_zero (c a) (u a) S (hc a) k)
  have hn := mul_le_mul_of_nonneg_left (material_source_norm (c a) (u a) B L (hb a) (hu a) k) hC
  refine ⟨U,D,T,hD,hT,hval,hUn.trans hn,fun i => (hDn i).trans hn,
    fun i j => (hTn i j).trans hn,?_⟩
  intro x hx
  apply (hpoint x hx).trans
  exact mul_le_mul_of_nonneg_left hn (by unfold Packet05ExplicitAnisotropicBound.universalConstant; positivity)

end OQ14.Packet05UniformMaterialCorrection
#print axioms OQ14.Packet05UniformMaterialCorrection.material_source_norm
#print axioms OQ14.Packet05UniformMaterialCorrection.material_family_correction
