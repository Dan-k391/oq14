import Packet06ConcreteExcitation
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ExcitationTail
open Filter OQ14.StaticCoefficient
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem uniform_tail (c : ℕ → Coefficient) (D : ℝ) (_hD : 0 ≤ D) (hc : ∀ j, (c j).bound ≤ D)
    (z : ℕ → ℂ) (z₀ : ℂ) (hz : Tendsto z atTop (𝓝 z₀))
    (u : ℕ → V) (u₀ : V) (hu : Tendsto u atTop (𝓝 u₀))
    (P : ℕ → Prop) (hP : ∀ᶠ j in atTop, P j) :
    ∃ (J : ℕ) (Z L : ℝ), 0 ≤ L ∧ (∀ j, P (j+J)) ∧ (∀ j, ‖z (j+J)‖ ≤ Z) ∧
      ∀ j i, ‖NewtonL2.physicalCoordinate (sqrtMultiplier (c (j+J)) (u (j+J))) i‖ ≤ L := by
  have hzb : ∀ᶠ j in atTop, ‖z j‖ < ‖z₀‖+1 := (tendsto_order.mp hz.norm).2 _ (by linarith)
  have hub : ∀ᶠ j in atTop, ‖u j‖ < ‖u₀‖+1 := (tendsto_order.mp hu.norm).2 _ (by linarith)
  obtain ⟨J,hJ⟩ := (hP.and (hzb.and hub)).exists_forall_of_atTop
  refine ⟨J,‖z₀‖+1,Real.sqrt D*(‖u₀‖+1),by positivity,?_,?_,?_⟩
  · intro j
    exact (hJ (j+J) (by omega)).1
  · intro j
    exact (hJ (j+J) (by omega)).2.1.le
  · intro j i
    have hn := (hJ (j+J) (by omega)).2.2.le
    have hs : ‖sqrtMultiplier (c (j+J))‖ ≤ Real.sqrt D :=
      (sqrtMultiplier_norm_le _).trans (Real.sqrt_le_sqrt (hc _))
    calc
      _ ≤ ‖sqrtMultiplier (c (j+J)) (u (j+J))‖ := DynamicConvolution.component_norm i _
      _ ≤ ‖sqrtMultiplier (c (j+J))‖*‖u (j+J)‖ := (sqrtMultiplier _).le_opNorm _
      _ ≤ Real.sqrt D*(‖u₀‖+1) := mul_le_mul hs hn (norm_nonneg _) (Real.sqrt_nonneg _)
#print axioms OQ14.Packet06ExcitationTail.uniform_tail
end OQ14.Packet06ExcitationTail
