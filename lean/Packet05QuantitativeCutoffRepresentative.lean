import Packet05ExplicitAnisotropicBound
import Packet05LocalizedAnisotropic
import Packet05ScalarCutoffRepresentative

/-! Quantitative scalar representative from actual cutoff weak derivatives. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3600000
namespace OQ14.Packet05QuantitativeCutoffRepresentative
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.WeakConservation OQ14.DivCurlCompact OQ14.Packet05PartialProduct
  OQ14.MaxwellCutoffCommutator OQ14.Packet05LocalizedAnisotropic
  OQ14.Packet05ExplicitAnisotropicBound

def firstArray (u : L2Scalar) (D : Fin 3 → L2Scalar) (χ : Test) (i : Fin 3) : L2Scalar :=
  scaleL2 χ.function χ.regular.continuous χ.compact (D i) +
    scaleL2 (fun x => dcoord χ.function x i) (partial_continuous χ.regular i)
      (χ.compact.fderiv_apply ℝ (basis i)) u

def secondArray (u : L2Scalar) (D : Fin 3 → L2Scalar) (χ : Test)
    (hχ2 : ContDiff ℝ 2 χ.function) (V : Fin 3 → Fin 3 → L2Scalar)
    (i j : Fin 3) : L2Scalar :=
  let dχ := derivativeCutoff χ hχ2 i
  V i j + (scaleL2 dχ.function dχ.regular.continuous dχ.compact (D j) +
    scaleL2 (fun x => dcoord dχ.function x j) (partial_continuous dχ.regular j)
      (dχ.compact.fderiv_apply ℝ (basis j)) u)

theorem cutoff_tangential_sup_bound (u : L2Scalar) (D : Fin 3 → L2Scalar)
    (hD : ∀ i, HasWeakPartial u (D i) i) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (V : Fin 3 → Fin 3 → L2Scalar)
    (hV : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (D i)) (V i j) j) :
    ∃ f : Space → ℂ, Continuous f ∧
      (fun x => scaleL2 χ.function χ.regular.continuous χ.compact u x) =ᵐ[volume] f ∧
      ∀ x, ‖f x‖ ≤ universalConstant *
        (‖scaleL2 χ.function χ.regular.continuous χ.compact u‖ +
          ∑ i : Fin 3, ‖firstArray u D χ i‖ +
          ∑ i : Fin 2, ∑ j : Fin 3, ‖secondArray u D χ hχ2 V i.castSucc j‖) := by
  let F := scaleL2 χ.function χ.regular.continuous χ.compact u
  have hfirst (i : Fin 3) : HasWeakPartial F (firstArray u D χ i) i :=
    cutoff_weak_partial χ u (D i) i (hD i)
  have hsecond : ∀ i, i ≠ 2 → ∀ j,
      HasWeakPartial (firstArray u D χ i) (secondArray u D χ hχ2 V i j) j := by
    intro i hi j
    let dχ := derivativeCutoff χ hχ2 i
    have hp := cutoff_weak_partial dχ u (D j) j (hD j)
    exact weak_partial_add _ _ _ _ j (hV i hi j) hp
  have hcompact : CompactRepresentative F :=
    ⟨fun x => χ.function x * u x, χ.compact.mul_right,
      scaleL2_ae χ.function χ.regular.continuous χ.compact u⟩
  exact continuous_sup_bound F hcompact (firstArray u D χ) hfirst
    (secondArray u D χ hχ2 V) hsecond


theorem tangential_plateau_sup_bound (T : Set Space) (hT : IsOpen T)
    (κ : RealTest Set.univ) (χ : Test)
    (hκ : ∀ x ∈ T, κ.function x = 1) (hχ : ∀ x ∈ T, χ.function x = 1)
    (u : L2Scalar) (D : Fin 3 → L2Scalar)
    (hD : ∀ i, HasWeakPartial (OQ14.Packet05ScalarCutoffTransfer.cutScalar κ u) (D i) i)
    (hχ2 : ContDiff ℝ 2 χ.function) (V : Fin 3 → Fin 3 → L2Scalar)
    (hV : ∀ i, i ≠ 2 → ∀ j, HasWeakPartial
      (scaleL2 χ.function χ.regular.continuous χ.compact (D i)) (V i j) j) :
    ∃ f : Space → ℂ, Continuous f ∧ (u : Space → ℂ) =ᵐ[volume.restrict T] f ∧
      ∀ x, ‖f x‖ ≤ universalConstant *
        (‖scaleL2 χ.function χ.regular.continuous χ.compact (OQ14.Packet05ScalarCutoffTransfer.cutScalar κ u)‖ +
          ∑ i : Fin 3, ‖firstArray (OQ14.Packet05ScalarCutoffTransfer.cutScalar κ u) D χ i‖ +
          ∑ i : Fin 2, ∑ j : Fin 3,
            ‖secondArray (OQ14.Packet05ScalarCutoffTransfer.cutScalar κ u) D χ hχ2 V i.castSucc j‖) := by
  obtain ⟨f,hf,hae,hbound⟩ := cutoff_tangential_sup_bound
    (OQ14.Packet05ScalarCutoffTransfer.cutScalar κ u) D hD χ hχ2 V hV
  exact ⟨f,hf,OQ14.Packet05ScalarCutoffRepresentative.uncut_on_plateau T hT κ χ hκ hχ u f hae,hbound⟩

end OQ14.Packet05QuantitativeCutoffRepresentative
#print axioms OQ14.Packet05QuantitativeCutoffRepresentative.cutoff_tangential_sup_bound

#print axioms OQ14.Packet05QuantitativeCutoffRepresentative.tangential_plateau_sup_bound
