import Packet06RoundedVolumeLimits

/-! Genuine two-sided material-weighted maxima on each compact peak ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06PhaseWeightedMaximum
open Set Metric Filter Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet05BinaryPhaseMaximum Packet05ActualMaximum Packet06RoundedVolumeLimits
open scoped Topology
abbrev Space := Maxwell.Space

def phasePermittivity (n η : ℝ) (b : Bool) : ℝ := if b then (1+η)*n^2 else n^2

def weighted (n η : ℝ) (d : MaximumData) (b : Bool) (x : Space) : ℝ :=
  phasePermittivity n η b * (physicalAmplitude (phaseField d.inside d.outside b) x)^2

theorem weighted_attains {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (z : ℂ) (v : Packet06SectorOperator.Sector)
    (j : ℕ) (i : Fin N) (r : ℝ) (hr : 0 < r) (d : MaximumData)
    (hd : Valid n hn g η hη z v j i r d) :
    ∃ b x, x ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b ∧
      (∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
        weighted n η d b' y ≤ weighted n η d b x) ∧
      (Packet06PhysicalVolumeLimits.amplitude (vector d))^2 ≤ weighted n η d b x := by
  let K := closedBall (g.center i) r
  have hc (b : Bool) : ContinuousOn (weighted n η d b) (K ∩ phaseDomain (body g j) b) := by
    unfold weighted
    cases b with
    | false => exact continuousOn_const.mul ((amplitude_continuousOn d.outside _ hd.2.1).pow 2)
    | true => exact continuousOn_const.mul ((amplitude_continuousOn d.inside _ hd.1).pow 2)
  obtain ⟨b,x,hx,hmax⟩ := Packet05FiniteBranchMaximum.finite_closed_branches_attain_max
    K (isCompact_closedBall _ _) ⟨g.center i,mem_closedBall_self hr.le⟩ (phaseDomain (body g j))
    (fun b => by cases b <;> exact isClosed_closure) (phase_domains_cover (body g j) K)
    (weighted n η d) hc
  refine ⟨b,x,hx,hmax,?_⟩
  have he : 1 ≤ phasePermittivity n η d.side := by
    have hn2 : 1 ≤ n^2 := by nlinarith
    cases h : d.side <;> simp only [phasePermittivity,h,Bool.false_eq_true,if_false,if_true] <;> nlinarith [mul_nonneg hη (sq_nonneg n)]
  have ha : (Packet06PhysicalVolumeLimits.amplitude (vector d))^2 =
      (physicalAmplitude (phaseField d.inside d.outside d.side) d.point)^2 := by rfl
  rw [ha]
  have hle := mul_le_mul_of_nonneg_right he (sq_nonneg (physicalAmplitude (phaseField d.inside d.outside d.side) d.point))
  have hw : (physicalAmplitude (phaseField d.inside d.outside d.side) d.point)^2 ≤ weighted n η d d.side d.point := by
    simpa [weighted] using hle
  exact hw.trans (hmax d.side d.point hd.2.2.2.2.1)
end OQ14.Packet06PhaseWeightedMaximum
#print axioms OQ14.Packet06PhaseWeightedMaximum.weighted_attains
