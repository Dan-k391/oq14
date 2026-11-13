import Packet05RegionalNormalFlux
import Packet05LocalReciprocalDerivative

/-! Isolate and divide the normal diagonal flux term on a constant material
phase, without assuming a normal derivative for the unknown. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalNormalRecovery
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalPartial OQ14.Packet05RegionalNormalFlux
  OQ14.Packet05LocalReciprocalDerivative

theorem regional_isolate_scaled_partial (V : Set Space) (P F S E DP DF DS : L2Scalar)
    (ε : ℂ) (hε : ε ≠ 0) (i : Fin 3)
    (hP : HasPartialOn V P DP i) (hF : HasPartialOn V F DF i) (hS : HasPartialOn V S DS i)
    (hrel : ∀ᵐ x ∂volume, x ∈ V → P x + F x - ε*S x = ε*E x) :
    HasPartialOn V E (ε⁻¹ • (DP+DF-ε • DS)) i := by
  let T : L2Scalar := P+F-ε • S
  let DT : L2Scalar := DP+DF-ε • DS
  have hT : HasPartialOn V T DT i := by
    intro φ hφ
    have hp := hP φ hφ
    have hf := hF φ hφ
    have hs := hS φ hφ
    simp only [T, DT, map_sub, map_add, map_smul, smul_eq_mul]
    linear_combination hp+hf-ε*hs
  have heq : ∀ᵐ x ∂volume, x ∈ V → (ε • E : L2Scalar) x = T x := by
    filter_upwards [hrel, Lp.coeFn_add P F, Lp.coeFn_sub (P+F) (ε • S),
      Lp.coeFn_smul ε S, Lp.coeFn_smul ε E] with x hr ha hs hsm he hx
    change (ε • E : L2Scalar) x = (P+F-ε • S : L2Scalar) x
    rw [he,hs]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    rw [ha,hsm]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (hr hx).symm
  have hscaled : HasPartialOn V (ε • E) DT i := partial_on_of_ae_eq V (ε • E) T DT i hT heq
  intro φ hφ
  have hh := hscaled φ hφ
  simp only [map_smul, smul_eq_mul] at hh ⊢
  have he := congrArg (fun z : ℂ => ε⁻¹*z) hh
  simp only [mul_add, ← mul_assoc, inv_mul_cancel₀ hε, one_mul, mul_zero] at he
  exact he

theorem regional_recover_diagonal_normal (V W : Set Space) (A r χ : Test)
    (hrV : tsupport r.function ⊆ V) (hχW : tsupport χ.function ⊆ W)
    (hrecip : ∀ x ∈ W, r.function x * A.function x = 1)
    (u P F S DP DF DS : L2Scalar) (ε : ℂ) (hε : ε ≠ 0)
    (hP : HasPartialOn V P DP 2) (hF : HasPartialOn V F DF 2) (hS : HasPartialOn V S DS 2)
    (hrel : ∀ᵐ x ∂volume, x ∈ V →
      P x + F x - ε*S x = ε*scaleL2 A.function A.regular.continuous A.compact u x) :
    ∃ Du : L2Scalar, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact u) Du 2 := by
  have hdiag := regional_isolate_scaled_partial V P F S _ DP DF DS ε hε 2 hP hF hS hrel
  exact local_reciprocal_weak_partial V W A r χ hrV hχW hrecip u _ 2 hdiag

end OQ14.Packet05RegionalNormalRecovery
#print axioms OQ14.Packet05RegionalNormalRecovery.regional_isolate_scaled_partial
#print axioms OQ14.Packet05RegionalNormalRecovery.regional_recover_diagonal_normal
