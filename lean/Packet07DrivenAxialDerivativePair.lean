import Packet07DrivenAxialPair

/-! The scalar test gradient transforms by the axial rotation matrix. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace OQ14.Packet07DrivenAxialDerivativePair
open MeasureTheory Maxwell DynamicSource MaterialMaxwell ModalAxialRotation Packet07DrivenAxialTests WeakAnnularMoment

theorem pair_partial_zero (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (i : Fin 3) (f : Test) :
    fieldPair F i (testPartial 0 (rotateTest θ f)) =
      (Real.cos θ : ℂ)*fieldPair F i (rotateTest θ (testPartial 0 f)) +
      (Real.sin θ : ℂ)*fieldPair F i (rotateTest θ (testPartial 1 f)) := by
  have h0 : Integrable (fun x => F x i*(rotateTest θ (testPartial 0 f)).val x) :=
    integrable_mul_compact _ _ (hF i) (rotateTest θ (testPartial 0 f)).val.continuous (rotateTest θ (testPartial 0 f)).property
  have h1 : Integrable (fun x => F x i*(rotateTest θ (testPartial 1 f)).val x) :=
    integrable_mul_compact _ _ (hF i) (rotateTest θ (testPartial 1 f)).val.continuous (rotateTest θ (testPartial 1 f)).property
  unfold fieldPair
  simp_rw [rotateTest_partial_zero,← rotateTest_apply,mul_add]
  simp only [show ∀ x : Space, F x i * ((Real.cos θ : ℂ) * (rotateTest θ (testPartial 0 f)).val x) =
    (Real.cos θ : ℂ)*(F x i*(rotateTest θ (testPartial 0 f)).val x) by intro x; ring,
    show ∀ x : Space, F x i * ((Real.sin θ : ℂ) * (rotateTest θ (testPartial 1 f)).val x) =
    (Real.sin θ : ℂ)*(F x i*(rotateTest θ (testPartial 1 f)).val x) by intro x; ring]
  rw [integral_add (h0.const_mul _) (h1.const_mul _),integral_const_mul,integral_const_mul]

theorem pair_partial_one (θ : ℝ) (F : Field) (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (i : Fin 3) (f : Test) :
    fieldPair F i (testPartial 1 (rotateTest θ f)) =
      -(Real.sin θ : ℂ)*fieldPair F i (rotateTest θ (testPartial 0 f)) +
      (Real.cos θ : ℂ)*fieldPair F i (rotateTest θ (testPartial 1 f)) := by
  have h0 : Integrable (fun x => F x i*(rotateTest θ (testPartial 0 f)).val x) :=
    integrable_mul_compact _ _ (hF i) (rotateTest θ (testPartial 0 f)).val.continuous (rotateTest θ (testPartial 0 f)).property
  have h1 : Integrable (fun x => F x i*(rotateTest θ (testPartial 1 f)).val x) :=
    integrable_mul_compact _ _ (hF i) (rotateTest θ (testPartial 1 f)).val.continuous (rotateTest θ (testPartial 1 f)).property
  unfold fieldPair
  simp_rw [rotateTest_partial_one,← rotateTest_apply,mul_add]
  simp only [show ∀ x : Space, F x i * (-(Real.sin θ : ℂ) * (rotateTest θ (testPartial 0 f)).val x) =
    -(Real.sin θ : ℂ)*(F x i*(rotateTest θ (testPartial 0 f)).val x) by intro x; ring,
    show ∀ x : Space, F x i * ((Real.cos θ : ℂ) * (rotateTest θ (testPartial 1 f)).val x) =
    (Real.cos θ : ℂ)*(F x i*(rotateTest θ (testPartial 1 f)).val x) by intro x; ring]
  rw [integral_add (h0.const_mul _) (h1.const_mul _),integral_const_mul,integral_const_mul]

theorem pair_partial_two (θ : ℝ) (F : Field) (i : Fin 3) (f : Test) :
    fieldPair F i (testPartial 2 (rotateTest θ f)) = fieldPair F i (rotateTest θ (testPartial 2 f)) := by
  unfold fieldPair
  apply integral_congr_ae
  filter_upwards with x
  rw [rotateTest_partial_two,rotateTest_apply]
end OQ14.Packet07DrivenAxialDerivativePair
#print axioms OQ14.Packet07DrivenAxialDerivativePair.pair_partial_zero
#print axioms OQ14.Packet07DrivenAxialDerivativePair.pair_partial_one
#print axioms OQ14.Packet07DrivenAxialDerivativePair.pair_partial_two
