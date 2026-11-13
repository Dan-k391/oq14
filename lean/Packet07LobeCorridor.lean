import Packet07LobeNonempty

/-! A common connected axial corridor inside each sufficiently rounded lobe. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07LobeCorridor
open Set Metric Filter
open scoped Topology
abbrev Plane := ConicalSmoothCapGraph.Plane

/-- Under explicit smallness inequalities, a whole axial cylinder lies in
    the positive lobe of the actual rounded cone-ball inclusion. -/
theorem positive_corridor (n : ℕ) (m a : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+1) * ConicalTipRounding.radius n < a/3)
    (hrad : (2 * ConicalTipRounding.radius n)^2 < a^2/9)
    (hj : ConicalTipRounding.radius n < a^2/3)
    (u : Plane) (z : ℝ) (hu : ‖u‖ ≤ 2*ConicalTipRounding.radius n)
    (hz0 : a/3 ≤ z) (hz1 : z ≤ 2*a/3) :
    (u,z) ∈ ConicalSmoothJunction.inclusion n m a := by
  have he : 0 < ConicalTipRounding.radius n := ConicalTipRounding.radius_positive n
  have hcap' := ConicalJunctionRadial.cap_upper n m hm u
  have hcone : 0 < ConicalSmoothJunction.coneMargin n m (u,z) := by
    unfold ConicalSmoothJunction.coneMargin
    have hmu := mul_le_mul_of_nonneg_left hu hm.le
    rw [abs_of_pos (by linarith : 0 < z)]
    nlinarith
  have hu2 : ‖u‖^2 ≤ (2*ConicalTipRounding.radius n)^2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  have hzsq : z^2 ≤ (2*a/3)^2 :=
    pow_le_pow_left₀ (by linarith : 0 ≤ z) hz1 2
  have hball : a^2/3 < ConicalSmoothJunction.ballMargin a (u,z) := by
    unfold ConicalSmoothJunction.ballMargin
    nlinarith
  have hball0 : 0 < ConicalSmoothJunction.ballMargin a (u,z) := lt_trans (by positivity) hball
  have hc0 : ConicalSmoothJunction.correction n
      (ConicalSmoothJunction.coneMargin n m (u,z)) (ConicalSmoothJunction.ballMargin a (u,z)) = 0 := by
    apply ConicalSmoothJunction.correction_zero
    have hballE : ConicalTipRounding.radius n < ConicalSmoothJunction.ballMargin a (u,z) := lt_trans hj hball
    nlinarith [sq_nonneg (ConicalSmoothJunction.coneMargin n m (u,z)),
      sq_nonneg (ConicalSmoothJunction.ballMargin a (u,z) - ConicalTipRounding.radius n)]
  refine ⟨hcone,hball0,?_⟩
  rw [hc0]
  positivity

/-- The central axial corridor as an explicit convex three-dimensional set. -/
def corridor (n : ℕ) (a : ℝ) : Set (Plane × ℝ) :=
  closedBall (0 : Plane) (2*ConicalTipRounding.radius n) ×ˢ Icc (a/3) (2*a/3)

theorem corridor_connected (n : ℕ) (a : ℝ) (ha : 0 < a) : IsConnected (corridor n a) := by
  have hc : Convex ℝ (corridor n a) :=
    (convex_closedBall (0 : Plane) (2*ConicalTipRounding.radius n)).prod (convex_Icc (a/3) (2*a/3))
  have hn : (corridor n a).Nonempty := by
    refine ⟨(0,a/2),?_⟩
    change (0 : Plane) ∈ closedBall (0 : Plane) (2*ConicalTipRounding.radius n) ∧ a/2 ∈ Icc (a/3) (2*a/3)
    constructor
    · simp only [mem_closedBall, dist_self]
      exact mul_nonneg (by norm_num) (ConicalTipRounding.radius_positive n).le
    · constructor <;> linarith
  exact hc.isConnected hn

theorem corridor_subset_inclusion (n : ℕ) (m a : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+1) * ConicalTipRounding.radius n < a/3)
    (hrad : (2 * ConicalTipRounding.radius n)^2 < a^2/9)
    (hj : ConicalTipRounding.radius n < a^2/3) :
    corridor n a ⊆ ConicalSmoothJunction.inclusion n m a := by
  intro ⟨u,z⟩ hz
  have hu : ‖u‖ ≤ 2*ConicalTipRounding.radius n := by
    simpa only [mem_closedBall, dist_zero_right] using hz.1
  exact positive_corridor n m a hm ha hcap hrad hj u z hu hz.2.1 hz.2.2

end OQ14.Packet07LobeCorridor
#print axioms OQ14.Packet07LobeCorridor.positive_corridor

#print axioms OQ14.Packet07LobeCorridor.corridor_connected
#print axioms OQ14.Packet07LobeCorridor.corridor_subset_inclusion
