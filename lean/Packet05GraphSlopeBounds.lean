import Packet05ActualGraphExtension
import Packet05GraphPiolaH2

/-! Global bounded graph-slope derivatives are consequences of a compact C³
plane extension; no independent bounded-coefficient assumption is needed. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05GraphSlopeBounds
open MeasureTheory OQ14.Maxwell OQ14.ConicalJunctionPhysical
  OQ14.Packet05PhysicalGraphChart OQ14.Packet05GraphSlope
  OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05GraphPiolaH2
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

def planeDirection (i : Fin 3) : Plane := horizontalLinear.toContinuousLinearMap (basis i)
def planeSlope (g : Plane → ℝ) (i : Fin 3) (p : Plane) : ℂ :=
  (fderiv ℝ g p (planeDirection i) : ℂ)

theorem slope_plane_formula (g : Plane → ℝ) (hg : ContDiff ℝ 1 g) (i : Fin 3) :
    slopeC g i = fun x => planeSlope g i (horizontal x) := by
  funext x
  simp only [slopeC, Packet05GraphSlope.slope, liftedHeight_fderiv g hg, planeSlope, planeDirection,
    ContinuousLinearMap.comp_apply]

theorem lifted_partial (f : Plane → ℂ) (hf : ContDiff ℝ 1 f) (j : Fin 3) (x : Maxwell.Space) :
    dcoord (fun y => f (horizontal y)) x j =
      fderiv ℝ f (horizontal x) (planeDirection j) := by
  change fderiv ℝ (f ∘ horizontalLinear.toContinuousLinearMap) x (basis j) = _
  rw [fderiv_comp x (hf.differentiable (by norm_num) _)
    (horizontalLinear.toContinuousLinearMap.differentiable x),
    horizontalLinear.toContinuousLinearMap.fderiv]
  rfl

theorem planeSlope_regular (g : Plane → ℝ) (hg : ContDiff ℝ 3 g) (i : Fin 3) :
    ContDiff ℝ 2 (planeSlope g i) := by
  apply Complex.ofRealCLM.contDiff.comp
  exact (hg.contDiff_fderiv_apply (by norm_num)).comp (contDiff_id.prodMk contDiff_const)

theorem planeSlope_compact (g : Plane → ℝ) (hc : HasCompactSupport g) (i : Fin 3) :
    HasCompactSupport (planeSlope g i) := by
  exact (hc.fderiv_apply ℝ (planeDirection i)).comp_left (g := Complex.ofReal) (by simp)

theorem slope_bounds (g : Plane → ℝ) (hg : ContDiff ℝ 3 g) (hc : HasCompactSupport g) :
    (∃ B : Fin 3 → ℝ, ∀ i x, ‖slopeC g i x‖ ≤ B i) ∧
    (∀ i j, MemLp (fun x => dcoord (slopeC g i) x j) ⊤ volume) ∧
    (∀ i j k, MemLp (fun x => dcoord (fun y => dcoord (slopeC g i) y j) x k) ⊤ volume) := by
  classical
  have hreg (i : Fin 3) := planeSlope_regular g hg i
  have hcompact (i : Fin 3) := planeSlope_compact g hc i
  have hb (i : Fin 3) : ∃ B : ℝ, ∀ x, ‖slopeC g i x‖ ≤ B := by
    obtain ⟨B,hB⟩ := (hcompact i).exists_bound_of_continuous (hreg i).continuous
    refine ⟨B, ?_⟩
    intro x
    rw [slope_plane_formula g (hg.of_le (by decide)) i]
    exact hB _
  choose B hB using hb
  refine ⟨⟨B,hB⟩, ?_, ?_⟩
  · intro i j
    have h1 : ContDiff ℝ 1 (planeSlope g i) := (hreg i).of_le (by decide)
    have hc1 := (hcompact i).fderiv_apply ℝ (planeDirection j)
    have hd : Continuous (fun p => fderiv ℝ (planeSlope g i) p (planeDirection j)) :=
      (h1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨C,hC⟩ := hc1.exists_bound_of_continuous hd
    apply memLp_top_of_bound (partial_continuous (slopeC_contDiff g (hg.of_le (by decide)) i) j).measurable.aestronglyMeasurable C
    filter_upwards with x
    rw [slope_plane_formula g (hg.of_le (by decide)) i, lifted_partial _ h1]
    exact hC _
  · intro i j k
    let f : Plane → ℂ := fun p => fderiv ℝ (planeSlope g i) p (planeDirection j)
    have hf : ContDiff ℝ 1 f :=
      ((hreg i).contDiff_fderiv_apply (by norm_num)).comp (contDiff_id.prodMk contDiff_const)
    have hfcomp : HasCompactSupport f := (hcompact i).fderiv_apply ℝ (planeDirection j)
    have hfd : Continuous (fun p => fderiv ℝ f p (planeDirection k)) :=
      (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
    obtain ⟨C,hC⟩ := (hfcomp.fderiv_apply ℝ (planeDirection k)).exists_bound_of_continuous hfd
    have heq : (fun x => dcoord (slopeC g i) x j) = fun x => f (horizontal x) := by
      funext x
      rw [slope_plane_formula g (hg.of_le (by decide)) i, lifted_partial _ ((hreg i).of_le (by decide))]
    rw [heq]
    have hflift : ContDiff ℝ 1 (fun x => f (horizontal x)) :=
      hf.comp horizontalLinear.toContinuousLinearMap.contDiff
    apply memLp_top_of_bound (partial_continuous hflift k).measurable.aestronglyMeasurable C
    filter_upwards with x
    rw [lifted_partial f hf]
    exact hC _

end OQ14.Packet05GraphSlopeBounds
#print axioms OQ14.Packet05GraphSlopeBounds.slope_plane_formula
#print axioms OQ14.Packet05GraphSlopeBounds.lifted_partial
#print axioms OQ14.Packet05GraphSlopeBounds.planeSlope_regular
#print axioms OQ14.Packet05GraphSlopeBounds.planeSlope_compact
#print axioms OQ14.Packet05GraphSlopeBounds.slope_bounds
