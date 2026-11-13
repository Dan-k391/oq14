import Packet05GraphSlopeBounds

/-! Compact C³ graph extensions have pointwise global first and second slope
bounds, uniformly over all Cartesian components. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05SlopeUniformBounds
open Maxwell WeakCurl WeakPoynting WeakGreen DivCurlCompact ConicalJunctionPhysical
  Packet05PhysicalGraphChart Packet05GraphSlope Packet05GraphSlopeMultiplier Packet05GraphSlopeBounds
abbrev Plane := ConicalSmoothJunction.Plane

theorem slope_uniform_bounds (g : Plane → ℝ) (hg : ContDiff ℝ 3 g) (hgc : HasCompactSupport g) :
    ∃ B L1 L2 : ℝ, 0 ≤ B ∧ 0 ≤ L1 ∧ 0 ≤ L2 ∧
      (∀ i x, ‖slopeC g i x‖ ≤ B) ∧
      (∀ i j x, ‖dcoord (slopeC g i) x j‖ ≤ L1) ∧
      ∀ i j k x, ‖dcoord (fun y => dcoord (slopeC g i) y j) x k‖ ≤ L2 := by
  have h0 (i : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖slopeC g i x‖ ≤ C := by
    obtain ⟨C,hC⟩ := (planeSlope_compact g hgc i).exists_bound_of_continuous (planeSlope_regular g hg i).continuous
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro x
    rw [slope_plane_formula g (hg.of_le (by decide)) i]
    exact (hC _).trans (le_max_left _ _)
  have h1 (i j : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖dcoord (slopeC g i) x j‖ ≤ C := by
    have hr := planeSlope_regular g hg i
    have hc := (planeSlope_compact g hgc i).fderiv_apply ℝ (planeDirection j)
    have hcont : Continuous (fun p => fderiv ℝ (planeSlope g i) p (planeDirection j)) :=
      ((hr.of_le (show (1 : WithTop ℕ∞) ≤ 2 by decide)).continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro x
    rw [slope_plane_formula g (hg.of_le (by decide)) i, lifted_partial _ (hr.of_le (by decide))]
    exact (hC _).trans (le_max_left _ _)
  have h2 (i j k : Fin 3) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖dcoord (fun y => dcoord (slopeC g i) y j) x k‖ ≤ C := by
    have hr := planeSlope_regular g hg i
    let f : Plane → ℂ := fun p => fderiv ℝ (planeSlope g i) p (planeDirection j)
    have hf : ContDiff ℝ 1 f :=
      (hr.contDiff_fderiv_apply (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
    have hfcomp : HasCompactSupport f := (planeSlope_compact g hgc i).fderiv_apply ℝ (planeDirection j)
    have hcont : Continuous (fun p => fderiv ℝ f p (planeDirection k)) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨C,hC⟩ := (hfcomp.fderiv_apply ℝ (planeDirection k)).exists_bound_of_continuous hcont
    refine ⟨max C 0,le_max_right _ _,?_⟩
    intro x
    have heq : (fun y => dcoord (slopeC g i) y j) = fun y => f (horizontal y) := by
      funext y
      rw [slope_plane_formula g (hg.of_le (by decide)) i,lifted_partial _ (hr.of_le (by decide))]
    rw [heq,lifted_partial f hf]
    exact (hC _).trans (le_max_left _ _)
  choose B hB using h0
  choose L hL using h1
  choose T hT using h2
  let B' := ∑ i : Fin 3, B i
  let L' := ∑ i : Fin 3, ∑ j : Fin 3, L i j
  let T' := ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, T i j k
  refine ⟨B',L',T',Finset.sum_nonneg (fun i _ => (hB i).1),
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hL i j).1)),
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ => (hT i j k).1))),?_,?_,?_⟩
  · intro i x
    exact ((hB i).2 x).trans (Finset.single_le_sum (fun j _ => (hB j).1) (Finset.mem_univ i))
  · intro i j x
    exact ((hL i j).2 x).trans ((Finset.single_le_sum (fun k _ => (hL i k).1) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => (hL k l).1)) (Finset.mem_univ i)))
  · intro i j k x
    exact ((hT i j k).2 x).trans ((Finset.single_le_sum (fun l _ => (hT i j l).1) (Finset.mem_univ k)).trans
      ((Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => (hT i l m).1)) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (fun l _ => Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun q _ => (hT l m q).1))) (Finset.mem_univ i))))

end OQ14.Packet05SlopeUniformBounds
#print axioms OQ14.Packet05SlopeUniformBounds.slope_uniform_bounds
