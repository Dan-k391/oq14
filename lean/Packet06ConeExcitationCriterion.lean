import Packet06ZeroPairBound
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeExcitationCriterion
open Filter Set Metric MeasureTheory OQ14.Maxwell OQ14.ConicalProjectionData OQ14.ConicalLocalStability
open scoped Topology

theorem eventually_nonzero (q P : ℕ → ℂ) (P₀ : ℂ) (bound : ℝ)
    (hP : Tendsto P atTop (𝓝 P₀)) (hstrict : bound < ‖P₀‖)
    (hzero : ∀ j, q j = 0 → ‖P j‖ ≤ bound) : ∀ᶠ j in atTop, q j ≠ 0 := by
  have hnorm : Tendsto (fun j => ‖P j‖) atTop (𝓝 ‖P₀‖) := hP.norm
  have hlarge : ∀ᶠ j in atTop, bound < ‖P j‖ :=
    (tendsto_order.mp hnorm).1 bound hstrict
  filter_upwards [hlarge] with j hj hq
  exact (not_lt_of_ge (hzero j hq)) hj
def zeroBoundConstant (t D α : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) (hα : 0 < α) : ℝ :=
  Classical.choose (Packet06ZeroPairBound.estimate t D α ht ht1 hD hα)

theorem actual_systems_eventually_nonzero (t D α : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) (hα : 0 < α)
    (p : ℕ → ConicalStaticVolume.Data) (hpt : ∀ j, (p j).threshold = t)
    (hpd : ∀ j, (p j).contrast ≤ D) (hν : ∀ j, (p j).exponent < 1)
    (hhalf : ∀ᶠ j in atTop, (1/2 : ℝ) ≤ (p j).exponent)
    (b : ℝ) (hb : 0 < b) (hbi : ∀ j, b < (p j).cutoff.rIn)
    (M : ℝ) (hM : 0 ≤ M) (s : ∀ j, System (p j) b)
    (hW : ∀ j i x, x ∈ closedBall (0 : Maxwell.Space) b →
      ‖(s j).correction i x-(s j).correction i 0‖ ≤ M*‖x‖^α)
    (ζ : ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hc : HasCompactSupport ζ)
    (hs : tsupport ζ ⊆ Ioo (0 : ℝ) b) (P₀ : ℂ)
    (hP : Tendsto (fun j => totalPair (s j) ζ hζ hc) atTop (𝓝 P₀))
    (hlarge : zeroBoundConstant t D α ht ht1 hD hα*M*
      (∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r|) < ‖P₀‖) :
    ∀ᶠ j in atTop, ConicalIntrinsicCoefficient.coefficient (s j) hb (hbi j) (hν j) ≠ 0 := by
  have hzero := (Classical.choose_spec (Packet06ZeroPairBound.estimate t D α ht ht1 hD hα)).2
  have hnorm : Tendsto (fun j => ‖totalPair (s j) ζ hζ hc‖) atTop (𝓝 ‖P₀‖) := hP.norm
  have hgood : ∀ᶠ j in atTop, zeroBoundConstant t D α ht ht1 hD hα*M*
      (∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r|) < ‖totalPair (s j) ζ hζ hc‖ :=
    (tendsto_order.mp hnorm).1 _ hlarge
  filter_upwards [hgood,hhalf] with j hj hh hq
  have hh' := hzero (p j) (hpt j) (hpd j) (hν j) hh b hb (hbi j) M (s j) hM (hW j) hq ζ hζ hc hs
  exact (not_lt_of_ge hh') hj
#print axioms OQ14.Packet06ConeExcitationCriterion.eventually_nonzero
#print axioms OQ14.Packet06ConeExcitationCriterion.actual_systems_eventually_nonzero
end OQ14.Packet06ConeExcitationCriterion
