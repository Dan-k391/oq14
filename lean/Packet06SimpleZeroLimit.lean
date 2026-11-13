import Packet06SimpleZero
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SimpleZero
open Filter Metric Set
open scoped Topology

theorem zeros_tend_to_simple_normalized (U : Set ℂ) (hU : IsOpen U) (a : ℂ) (haU : a ∈ U)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hzero : f a = 0) (hder : deriv f a = 1)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∃ z, dist z a < ε ∧ F n z = 0 := by
  intro ε hε
  have hdercont : ContinuousAt (deriv f) a :=
    ((hf.deriv hU) a haU).differentiableAt (hU.mem_nhds haU) |>.continuousAt
  have hnear : ∀ᶠ z in 𝓝 a, ‖1 - deriv f z‖ < (1/4 : ℝ) := by
    have h := hdercont.tendsto (Metric.ball_mem_nhds (deriv f a) (by norm_num : (0:ℝ)<1/4))
    filter_upwards [h] with z hz
    simpa only [mem_ball, dist_eq_norm, hder, norm_sub_rev] using hz
  have hboth : U ∩ {z : ℂ | ‖1-deriv f z‖ < (1/4 : ℝ)} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds haU) hnear
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hboth
  let r : ℝ := min δ ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; have := min_le_left δ ε; linarith
  have hrε : r < ε := by dsimp [r]; have := min_le_right δ ε; linarith
  have hball : closedBall a r ⊆ U := fun z hz => (hδsub (closedBall_subset_ball hrδ hz)).1
  have hnear' : ∀ z ∈ closedBall a r, ‖1-deriv f z‖ < (1/4 : ℝ) :=
    fun z hz => (hδsub (closedBall_subset_ball hrδ hz)).2
  have hdc := hconv.deriv hF hU
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hdc
    (closedBall a r) hball (isCompact_closedBall a r)
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp hunif) (1/4) (by norm_num)
  have hpoint : Tendsto (fun n => F n a) atTop (𝓝 0) := by simpa [hzero] using hconv.tendsto_at haU
  have hpoint' := hpoint.eventually (Metric.ball_mem_nhds (0 : ℂ) (show 0 < r/2 by positivity))
  filter_upwards [hF,hsmall,hpoint'] with n hFn hdn han
  have hdiff : ∀ z ∈ closedBall a r, DifferentiableAt ℂ (F n) z :=
    fun z hz => (hFn z (hball hz)).differentiableAt (hU.mem_nhds (hball hz))
  have hderbound : ∀ z ∈ closedBall a r, ‖1-deriv (F n) z‖ ≤ 1/2 := by
    intro z hz
    have hn := hdn z hz
    have hnorm : ‖deriv f z - deriv (F n) z‖ < (1/4 : ℝ) := by simpa [dist_eq_norm] using hn
    have ht : ‖1-deriv (F n) z‖ ≤ ‖1-deriv f z‖ + ‖deriv f z-deriv (F n) z‖ := by
      convert norm_add_le (1-deriv f z) (deriv f z-deriv (F n) z) using 1
      congr 1
      ring
    linarith [hnear' z hz]
  have hval : ‖F n a‖ ≤ r/2 := by
    have : ‖F n a‖ < r/2 := by simpa only [mem_ball,dist_zero_right] using han
    exact this.le
  obtain ⟨z,hz,hz0⟩ := zero_of_small_derivative_error (F n) a r hr hdiff hderbound hval
  exact ⟨z, (mem_closedBall.mp hz).trans_lt hrε, hz0⟩
theorem unique_simple_zeros_normalized (U : Set ℂ) (hU : IsOpen U) (a : ℂ) (haU : a ∈ U)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hzero : f a = 0) (hder : deriv f a = 1)
    (hF : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U) :
    ∀ ε > 0, ∃ r > 0, r < ε ∧ ∀ᶠ n in atTop, ∃ z ∈ closedBall a r,
      F n z = 0 ∧ deriv (F n) z ≠ 0 ∧
      ∀ w ∈ closedBall a r, F n w = 0 → w = z := by
  intro ε hε
  have hdercont : ContinuousAt (deriv f) a :=
    ((hf.deriv hU) a haU).differentiableAt (hU.mem_nhds haU) |>.continuousAt
  have hnear : ∀ᶠ z in 𝓝 a, ‖1 - deriv f z‖ < (1/4 : ℝ) := by
    have h := hdercont.tendsto (Metric.ball_mem_nhds (deriv f a) (by norm_num : (0:ℝ)<1/4))
    filter_upwards [h] with z hz
    simpa only [mem_ball, dist_eq_norm, hder, norm_sub_rev] using hz
  have hboth : U ∩ {z : ℂ | ‖1-deriv f z‖ < (1/4 : ℝ)} ∈ 𝓝 a :=
    inter_mem (hU.mem_nhds haU) hnear
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp hboth
  let r : ℝ := min δ ε / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := by dsimp [r]; have := min_le_left δ ε; linarith
  have hrε : r < ε := by dsimp [r]; have := min_le_right δ ε; linarith
  have hball : closedBall a r ⊆ U := fun z hz => (hδsub (closedBall_subset_ball hrδ hz)).1
  have hnear' : ∀ z ∈ closedBall a r, ‖1-deriv f z‖ < (1/4 : ℝ) :=
    fun z hz => (hδsub (closedBall_subset_ball hrδ hz)).2
  have hdc := hconv.deriv hF hU
  have hunif := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hdc
    (closedBall a r) hball (isCompact_closedBall a r)
  have hsmall := (Metric.tendstoUniformlyOn_iff.mp hunif) (1/4) (by norm_num)
  have hpoint : Tendsto (fun n => F n a) atTop (𝓝 0) := by simpa [hzero] using hconv.tendsto_at haU
  have hpoint' := hpoint.eventually (Metric.ball_mem_nhds (0 : ℂ) (show 0 < r/2 by positivity))
  refine ⟨r, hr, hrε, ?_⟩
  filter_upwards [hF,hsmall,hpoint'] with n hFn hdn han
  have hdiff : ∀ z ∈ closedBall a r, DifferentiableAt ℂ (F n) z :=
    fun z hz => (hFn z (hball hz)).differentiableAt (hU.mem_nhds (hball hz))
  have hderbound : ∀ z ∈ closedBall a r, ‖1-deriv (F n) z‖ ≤ 1/2 := by
    intro z hz
    have hn := hdn z hz
    have hnorm : ‖deriv f z - deriv (F n) z‖ < (1/4 : ℝ) := by simpa [dist_eq_norm] using hn
    have ht : ‖1-deriv (F n) z‖ ≤ ‖1-deriv f z‖ + ‖deriv f z-deriv (F n) z‖ := by
      convert norm_add_le (1-deriv f z) (deriv f z-deriv (F n) z) using 1
      congr 1
      ring
    linarith [hnear' z hz]
  have hval : ‖F n a‖ ≤ r/2 := by
    have : ‖F n a‖ < r/2 := by simpa only [mem_ball,dist_zero_right] using han
    exact this.le
  obtain ⟨z,hz,hz0⟩ := zero_of_small_derivative_error (F n) a r hr hdiff hderbound hval
  have hunique := unique_and_simple_of_small_derivative_error (F n) a r hdiff hderbound
  exact ⟨z, hz, hz0, hunique.1 z hz, fun w hw hw0 => hunique.2 w hw z hz hw0 hz0⟩
#print axioms OQ14.Packet06SimpleZero.unique_simple_zeros_normalized
#print axioms OQ14.Packet06SimpleZero.zeros_tend_to_simple_normalized
end OQ14.Packet06SimpleZero
