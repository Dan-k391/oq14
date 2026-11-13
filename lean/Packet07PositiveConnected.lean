import Packet07RadialPath

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet07PositiveConnected
open Set Metric

def positiveLobe (n : ℕ) (m a : ℝ) : Set (ConicalSmoothCapGraph.Plane × ℝ) :=
  ConicalSmoothJunction.inclusion n m a ∩ {x | 0 < x.2}

theorem positive_path_connected (n : ℕ) (m a : ℝ) (hm : 0 < m) (ha : 0 < a)
    (hcap : (2*m+2)*ConicalTipRounding.radius n < a/2)
    (hrad : (2*ConicalTipRounding.radius n)^2 < a^2/8)
    (heball : ConicalTipRounding.radius n < a^2/8)
    (hc : (2*m+1)*ConicalTipRounding.radius n < a/3)
    (hr : (2*ConicalTipRounding.radius n)^2 < a^2/9) :
    IsPathConnected (positiveLobe n m a) := by
  have he : 0 < ConicalTipRounding.radius n := ConicalTipRounding.radius_positive n
  have hj : ConicalTipRounding.radius n < a^2/3 := by nlinarith
  let C := Packet07LobeCorridor.corridor n a
  have hCsub : C ⊆ positiveLobe n m a := by
    intro ⟨u,z⟩ h
    refine ⟨Packet07LobeCorridor.corridor_subset_inclusion n m a hm ha hc hr hj h, ?_⟩
    change 0 < z
    have hz : a/3 ≤ z := h.2.1
    linarith
  have hC : IsPathConnected C := by
    have hconv : Convex ℝ C :=
      (convex_closedBall (0 : ConicalSmoothCapGraph.Plane) (2*ConicalTipRounding.radius n)).prod
        (convex_Icc (a/3) (2*a/3))
    exact hconv.isPathConnected (Packet07LobeCorridor.corridor_connected n a ha).nonempty
  have hbase : ((0 : ConicalSmoothCapGraph.Plane),a/2) ∈ C := by
    constructor
    · simp only [mem_closedBall, dist_self]
      linarith
    · constructor <;> linarith
  refine ⟨_, hCsub hbase, ?_⟩
  rintro ⟨u,z⟩ ⟨hinc,hz⟩
  have hvertical : ∀ v : ConicalSmoothCapGraph.Plane,
      ‖v‖ ≤ 2*ConicalTipRounding.radius n →
      (v,z) ∈ ConicalSmoothJunction.inclusion n m a →
      JoinedIn (positiveLobe n m a) (v,z) ((0 : ConicalSmoothCapGraph.Plane),a/2) := by
    intro v hv hi
    have hvpath := Packet07VerticalPath.vertical_joined n m a z v hm ha hcap hrad heball hv hz hi
    have hvc : (v,a/2) ∈ C := by
      constructor
      · simpa only [mem_closedBall, dist_zero_right] using hv
      · constructor <;> linarith
    exact hvpath.trans ((hC.joinedIn _ hvc _ hbase).mono hCsub)
  by_cases hu : ‖u‖ ≤ 2*ConicalTipRounding.radius n
  · exact (hvertical u hu hinc).symm
  · have hur : 2*ConicalTipRounding.radius n < ‖u‖ := lt_of_not_ge hu
    have hnorm : 0 < ‖u‖ := by linarith
    let c : ℝ := 2*ConicalTipRounding.radius n / ‖u‖
    have hc0 : 0 ≤ c := div_nonneg (by linarith) hnorm.le
    have hc1 : c ≤ 1 := by dsimp [c]; rw [div_le_one hnorm]; linarith
    have hceq : c*‖u‖ = 2*ConicalTipRounding.radius n := by dsimp [c]; field_simp
    have hcv : ‖c • u‖ = 2*ConicalTipRounding.radius n := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, hceq]
    have hp := Packet07RadialPath.radial_joined n m a z c u hm hz hc0 hc1 (by linarith) hinc
    have hi : (c • u,z) ∈ ConicalSmoothJunction.inclusion n m a := hp.target_mem.1
    exact (hp.trans (hvertical (c • u) hcv.le hi)).symm

end OQ14.Packet07PositiveConnected
#print axioms OQ14.Packet07PositiveConnected.positive_path_connected
