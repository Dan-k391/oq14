import Packet05CutoffLocalSecond

/-! Collect both local tangential directions and their four mixed partials
into the global cutoff fields expected by normal-flux continuity. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffTangentialArrays
open Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen OQ14.DivCurlCompact
  OQ14.Packet05RegionalPartial OQ14.Packet05CutoffLocalSecond

theorem cutoff_tangential_arrays (V : Set Space) (χ : Test) (hχ2 : ContDiff ℝ 2 χ.function)
    (hχV : tsupport χ.function ⊆ V) (C : L2Vector)
    (D : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector)
    (hD : ∀ i, i ≠ 2 → ∀ j, HasPartialOn V (C j) (D i j) i)
    (hH : ∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasPartialOn V (D i j) (H i t j) t) :
    ∃ C1 : Fin 3 → L2Vector, ∃ C2 : Fin 3 → Fin 3 → L2Vector,
      (∀ i, i ≠ 2 → ∀ j, HasWeakPartial
        (scaleL2 χ.function χ.regular.continuous χ.compact (C j)) (C1 i j) i) ∧
      (∀ i, i ≠ 2 → ∀ t, t ≠ 2 → ∀ j, HasWeakPartial (C1 i j) (C2 i t j) t) := by
  classical
  have hex (i : Fin 3) (hi : i ≠ 2) (j : Fin 3) :
      ∃ q, HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (C j)) q i ∧
        ∀ t, t ≠ 2 → ∃ r, HasWeakPartial q r t := by
    refine ⟨OQ14.Packet05CurlSourceH1.cutoffProductDerivative χ (C j) (D i j) i, ?_, ?_⟩
    · exact (cutoff_local_second V χ hχ2 hχV (C j) (D i j) (D i j) (H i i j)
        i i (hD i hi j) (hD i hi j) (hH i hi i hi j)).1
    · intro t ht
      exact ⟨_, (cutoff_local_second V χ hχ2 hχV (C j) (D i j) (D t j) (H i t j)
        i t (hD i hi j) (hD t ht j) (hH i hi t ht j)).2⟩
  let C1 (i : Fin 3) (j : Fin 3) := if hi : i ≠ 2 then Classical.choose (hex i hi j) else 0
  have hc1 (i : Fin 3) (hi : i ≠ 2) (j : Fin 3) :
      HasWeakPartial (scaleL2 χ.function χ.regular.continuous χ.compact (C j)) (C1 i j) i ∧
        ∀ t, t ≠ 2 → ∃ r, HasWeakPartial (C1 i j) r t := by
    simpa [C1,hi] using Classical.choose_spec (hex i hi j)
  let C2 (i t : Fin 3) (j : Fin 3) :=
    if hi : i ≠ 2 then if ht : t ≠ 2 then Classical.choose ((hc1 i hi j).2 t ht) else 0 else 0
  refine ⟨C1,C2,?_,?_⟩
  · intro i hi j
    exact (hc1 i hi j).1
  · intro i hi t ht j
    simpa [C2,hi,ht] using Classical.choose_spec ((hc1 i hi j).2 t ht)

end OQ14.Packet05CutoffTangentialArrays
#print axioms OQ14.Packet05CutoffTangentialArrays.cutoff_tangential_arrays
