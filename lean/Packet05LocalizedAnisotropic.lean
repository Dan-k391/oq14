import Packet05AnisotropicWeakEmbedding
import Packet05PartialProduct
import MaxwellCutoffCommutator

/-! Cutoff product rules assemble the actual anisotropic embedding inputs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05LocalizedAnisotropic
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.Packet05AnisotropicWeakEmbedding
  OQ14.Packet05PartialProduct OQ14.MaxwellCutoffCommutator

theorem weak_partial_add (u v Du Dv : L2Scalar) (i : Fin 3)
    (hu : HasWeakPartial u Du i) (hv : HasWeakPartial v Dv i) :
    HasWeakPartial (u+v) (Du+Dv) i := by
  intro φ
  have h1 := hu φ
  have h2 := hv φ
  simp only [map_add]
  linear_combination h1+h2

/-- A compact cutoff is continuous if the original field is H¹ and the
cutoffs of its tangential partials are also H¹. -/
theorem cutoff_continuous_of_tangential_h1 (u : L2Scalar) (D : Fin 3 → L2Scalar)
    (hD : ∀ i, HasWeakPartial u (D i) i) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hT : ∀ i, i ≠ 2 → ∀ j, ∃ v : L2Scalar,
      HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (D i)) v j) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact u x) =ᵐ[volume] f := by
  let F := scaleL2 χ.function χ.regular.continuous χ.compact u
  let deriv (i : Fin 3) := scaleL2 χ.function χ.regular.continuous χ.compact (D i) +
    scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) u
  have hfirst (i : Fin 3) : HasWeakPartial F (deriv i) i :=
    cutoff_weak_partial χ u (D i) i (hD i)
  have hsecond : ∀ i, i ≠ 2 → ∀ j, ∃ v, HasWeakPartial (deriv i) v j := by
    intro i hi j
    obtain ⟨v, hv⟩ := hT i hi j
    let dχ := derivativeCutoff χ hχ2 i
    have hp := cutoff_weak_partial dχ u (D j) j (hD j)
    refine ⟨v + (scaleL2 dχ.function dχ.regular.continuous dχ.compact (D j) +
      scaleL2 (fun x => dcoord dχ.function x j) (partial_continuous dχ.regular j)
        (dχ.compact.fderiv_apply ℝ (basis j)) u), ?_⟩
    exact weak_partial_add _ _ _ _ j hv hp
  classical
  let H : Fin 3 → Fin 3 → L2Scalar := fun i j =>
    if hi : i ≠ 2 then Classical.choose (hsecond i hi j) else 0
  have hH : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial (deriv i) (H i j) j := by
    intro i hi j
    simp only [H, dif_pos hi]
    exact Classical.choose_spec (hsecond i hi j)
  have hcompact : CompactRepresentative F :=
    ⟨fun x => χ.function x * u x, χ.compact.mul_right,
      scaleL2_ae χ.function χ.regular.continuous χ.compact u⟩
  exact continuous_of_weak_tangential_h1 F hcompact deriv hfirst H hH

end OQ14.Packet05LocalizedAnisotropic
#print axioms OQ14.Packet05LocalizedAnisotropic.weak_partial_add
#print axioms OQ14.Packet05LocalizedAnisotropic.cutoff_continuous_of_tangential_h1
