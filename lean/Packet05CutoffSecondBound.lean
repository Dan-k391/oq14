import Packet05MixedCutoffSourceBounds

/-! Every compact C² chart cutoff has one finite bound for its first and
second coordinate derivatives. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffSecondBound
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  MaxwellCutoffCommutator

theorem derivative_bounds (θ : Test) (hθ2 : ContDiff ℝ 2 θ.function) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
      (∀ x, ‖θ.function x‖ ≤ a) ∧
      (∀ i x, ‖dcoord θ.function x i‖ ≤ b) ∧
      ∀ i j x, ‖dcoord (derivativeCutoff θ hθ2 i).function x j‖ ≤ c := by
  obtain ⟨a,ha⟩ := θ.compact.exists_bound_of_continuous θ.regular.continuous
  have hb (i : Fin 3) : ∃ B : ℝ, ∀ x, ‖dcoord θ.function x i‖ ≤ B :=
    (θ.compact.fderiv_apply ℝ (basis i)).exists_bound_of_continuous (partial_continuous θ.regular i)
  have hc (i j : Fin 3) : ∃ C : ℝ, ∀ x, ‖dcoord (derivativeCutoff θ hθ2 i).function x j‖ ≤ C :=
    ((derivativeCutoff θ hθ2 i).compact.fderiv_apply ℝ (basis j)).exists_bound_of_continuous
      (partial_continuous (derivativeCutoff θ hθ2 i).regular j)
  choose b hb' using hb
  choose c hc' using hc
  let B := ∑ i : Fin 3, max (b i) 0
  let C := ∑ i : Fin 3, ∑ j : Fin 3, max (c i j) 0
  refine ⟨max a 0,B,C,le_max_right _ _,Finset.sum_nonneg (fun _ _ => le_max_right _ _),
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _)),?_,?_,?_⟩
  · intro x
    exact (ha x).trans (le_max_left _ _)
  · intro i x
    exact (hb' i x).trans ((le_max_left _ _).trans
      (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ i)))
  · intro i j x
    exact (hc' i j x).trans ((le_max_left _ _).trans
      ((Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun _ _ => Finset.sum_nonneg (fun _ _ => le_max_right _ _)) (Finset.mem_univ i))))

end OQ14.Packet05CutoffSecondBound
#print axioms OQ14.Packet05CutoffSecondBound.derivative_bounds
