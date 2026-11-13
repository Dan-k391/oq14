import Packet07LobeCorridor

/-! Uniform small-rounding conditions for finitely many axial corridors. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet07CorridorEventually
open Filter Set
open scoped Topology

theorem eventually_corridor_bounds {ι : Type*} [Fintype ι]
    (m a : ι → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ i,
      (2*m i+1) * ConicalTipRounding.radius n < a i/3 ∧
      (2*ConicalTipRounding.radius n)^2 < (a i)^2/9 ∧
      ConicalTipRounding.radius n < (a i)^2/3 := by
  have hr : Tendsto ConicalTipRounding.radius atTop (𝓝 0) := by
    simpa only [ConicalTipRounding.radius] using tendsto_one_div_add_atTop_nhds_zero_nat
  have hr2 : Tendsto (fun n => (2*ConicalTipRounding.radius n)^2) atTop (𝓝 0) := by
    simpa using (hr.const_mul 2).pow 2
  apply Filter.eventually_all.mpr
  intro i
  have hai : 0 < a i := ha i
  have hc : Tendsto (fun n => (2*m i+1)*ConicalTipRounding.radius n) atTop (𝓝 0) := by
    simpa using hr.const_mul (2*m i+1)
  exact (hc.eventually (gt_mem_nhds (by positivity : 0 < a i/3))).and
    ((hr2.eventually (gt_mem_nhds (by positivity : 0 < (a i)^2/9))).and
      (hr.eventually (gt_mem_nhds (by positivity : 0 < (a i)^2/3))))

/-- Reflection in the interface carries the positive corridor into the same
    actual rounded inclusion on its negative side. -/
theorem negative_corridor (n : ℕ) (m a : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+1) * ConicalTipRounding.radius n < a/3)
    (hrad : (2 * ConicalTipRounding.radius n)^2 < a^2/9)
    (hj : ConicalTipRounding.radius n < a^2/3)
    (u : Packet07LobeCorridor.Plane) (z : ℝ)
    (hu : ‖u‖ ≤ 2*ConicalTipRounding.radius n)
    (hz0 : -(2*a/3) ≤ z) (hz1 : z ≤ -(a/3)) :
    (u,z) ∈ ConicalSmoothJunction.inclusion n m a := by
  have h := Packet07LobeCorridor.positive_corridor n m a hm ha hcap hrad hj u (-z) hu (by linarith) (by linarith)
  simpa only [ConicalSmoothJunction.inclusion, mem_setOf_eq,
    ConicalSmoothJunction.coneMargin, ConicalSmoothJunction.ballMargin,
    Prod.fst, Prod.snd, abs_neg, neg_sq] using h
end OQ14.Packet07CorridorEventually
#print axioms OQ14.Packet07CorridorEventually.eventually_corridor_bounds
#print axioms OQ14.Packet07CorridorEventually.negative_corridor
