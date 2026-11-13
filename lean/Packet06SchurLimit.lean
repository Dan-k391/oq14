import Packet06SchurAnalytic
import Packet06SimpleZeroSequence
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SchurLimit
open Filter Metric Set Packet06RankOneRepair Packet06ScalarSchur
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Continuous composition preserves local uniform convergence at points where
its outer map is continuous and the limit is continuous. -/
theorem locally_uniform_comp {X Y Z : Type*} [TopologicalSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
    (U : Set X) (F : ℕ → X → Y) (f : X → Y) (g : Y → Z)
    (hF : TendstoLocallyUniformlyOn F f atTop U) (hf : ContinuousOn f U)
    (hg : ∀ x ∈ U, ContinuousAt g (f x)) :
    TendstoLocallyUniformlyOn (fun n x => g (F n x)) (fun x => g (f x)) atTop U := by
  apply Metric.tendstoLocallyUniformlyOn_iff.mpr
  intro ε hε x hx
  have htarget : ∀ᶠ y in 𝓝 (f x), dist (g y) (g (f x)) < ε/2 :=
    (hg x hx).tendsto (Metric.ball_mem_nhds (g (f x)) (by positivity))
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp htarget
  have hclose := (Metric.tendstoLocallyUniformlyOn_iff.mp hF) (δ/2) (by positivity) x hx
  obtain ⟨t,ht,htF⟩ := hclose
  have htlimit : ∀ᶠ y in 𝓝[U] x, dist (f y) (f x) < δ/2 :=
    (hf x hx).tendsto (Metric.ball_mem_nhds (f x) (by positivity))
  refine ⟨t ∩ {y | dist (f y) (f x) < δ/2}, inter_mem ht htlimit, ?_⟩
  filter_upwards [htF] with n hn y hy
  have hy2 : dist (f y) (f x) < δ/2 := hy.2
  have hfy : f y ∈ ball (f x) δ := by
    rw [mem_ball]
    linarith
  have hny : F n y ∈ ball (f x) δ := by
    rw [mem_ball]
    have htri := dist_triangle (F n y) (f y) (f x)
    have hn' := hn y hy.1
    rw [dist_comm] at hn'
    linarith
  have h1 := hδsub hfy
  have h2 := hδsub hny
  change dist (g (f y)) (g (f x)) < ε/2 at h1
  change dist (g (F n y)) (g (f x)) < ε/2 at h2
  have ht := dist_triangle (g (f y)) (g (f x)) (g (F n y))
  rw [dist_comm (g (f x)) (g (F n y))] at ht
  linarith
#print axioms OQ14.Packet06SchurLimit.locally_uniform_comp
end OQ14.Packet06SchurLimit
