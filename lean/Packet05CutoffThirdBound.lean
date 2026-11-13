import Packet05CutoffSecondBound

/-! A fixed compact C³ cutoff has a common bound on all third coordinate
partials needed by the regional forcing bootstrap. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05CutoffThirdBound
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact MaxwellCutoffCommutator

theorem third_derivative_bound (θ : Test) (hθ2 : ContDiff ℝ 2 θ.function)
    (hθ3 : ContDiff ℝ 3 θ.function) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k i t x,
      ‖dcoord (derivativeCutoff (derivativeCutoff θ hθ2 k)
        (by
          have hh : ContDiff ℝ 2 (fderiv ℝ θ.function) :=
            (contDiff_succ_iff_fderiv (n := 2)).mp hθ3 |>.2.2
          exact hh.clm_apply contDiff_const) i).function x t‖ ≤ C := by
  have hder2 (k : Fin 3) : ContDiff ℝ 2 (derivativeCutoff θ hθ2 k).function := by
    have hh : ContDiff ℝ 2 (fderiv ℝ θ.function) :=
      (contDiff_succ_iff_fderiv (n := 2)).mp hθ3 |>.2.2
    exact hh.clm_apply contDiff_const
  have hex (k : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ i t x,
      ‖dcoord (derivativeCutoff (derivativeCutoff θ hθ2 k) (hder2 k) i).function x t‖ ≤ C := by
    obtain ⟨_,_,C,_,_,hC,_,_,h⟩ := Packet05CutoffSecondBound.derivative_bounds (derivativeCutoff θ hθ2 k) (hder2 k)
    exact ⟨C,hC,h⟩
  choose C hC using hex
  let D := ∑ k : Fin 3, C k
  refine ⟨D,Finset.sum_nonneg (fun k _ => (hC k).1),?_⟩
  intro k i t x
  exact ((hC k).2 i t x).trans (Finset.single_le_sum (fun l _ => (hC l).1) (Finset.mem_univ k))

end OQ14.Packet05CutoffThirdBound
#print axioms OQ14.Packet05CutoffThirdBound.third_derivative_bound
