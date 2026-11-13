import Packet06ConeExcitationCriterion
import Packet06StrictAnnulus
import Packet06SpherePairIntegral
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ModeExcitation
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ConicalProjectionData
  OQ14.ConicalLocalStability OQ14.Packet06ConeExcitationCriterion
open scoped Topology

theorem eventual_actual_excitation (p : ℕ → ConicalStaticVolume.Data) (ell d : ℕ → ℝ)
    (hellp : ∀ j, (p j).eigenvalue = ell j) (hdp : ∀ j, (p j).contrast = d j)
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (htp : ∀ j, (p j).threshold = t)
    (hell : Tendsto ell atTop (𝓝 2)) (hd : Tendsto d atTop (𝓝 0))
    (hellb : ∀ j, ell j ∈ Icc (0 : ℝ) 2) (D : ℝ) (hD : 0 ≤ D) (hdb : ∀ j, d j ∈ Icc (0 : ℝ) D)
    (hν : ∀ j, (p j).exponent < 1) (hhalf : ∀ᶠ j in atTop, (1/2 : ℝ) ≤ (p j).exponent)
    (b : ℝ) (hb : 0 < b) (hbi : ∀ j, b < (p j).cutoff.rIn)
    (M α : ℝ) (hM : 0 ≤ M) (hα : 0 < α) (s : ∀ j, System (p j) b)
    (hW : ∀ j i x, x ∈ closedBall (0 : Maxwell.Space) b →
      ‖(s j).correction i x-(s j).correction i 0‖ ≤ M*‖x‖^α)
    (g : ℕ → ConicalRungeBall.BallL2 b) (g₀ : ConicalRungeBall.BallL2 b)
    (hg : Tendsto g atTop (𝓝 g₀))
    (hactual : ∀ j i, (g j i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)] totalCoordinate (s j) i)
    (F : Field) (hF : ∀ i, Continuous (fun x => F x i)) (center : Maxwell.Space)
    (hbase : ∀ i, (g₀ i : Maxwell.Space → ℂ) =ᵐ[volume.restrict (closedBall 0 b)] fun x => F (center+x) i)
    (A : ℂ) (hA : A ≠ 0) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (hclose : ∀ r : ℝ, |r| < R₀ → ‖Packet06SphereProjection.average F center r-A‖ < ‖A‖/2) :
    ∀ᶠ j in atTop, ConicalIntrinsicCoefficient.coefficient (s j) hb (hbi j) (hν j) ≠ 0 := by
  let K := zeroBoundConstant t D α ht ht1 hD hα
  have hK : 0 ≤ K := (Classical.choose_spec (Packet06ZeroPairBound.estimate t D α ht ht1 hD hα)).1
  have hcont := Packet06SphereProjection.average_continuous F hF center
  obtain ⟨ζ,hζ,hc,hs,hstrict⟩ := Packet06StrictAnnulus.choose_test t K M α b R₀ ht hK hM hα hb hR₀
    (Packet06SphereProjection.average F center) hcont A hA hclose
  have hpair := Packet06PhysicalPairLimit.actual_total_pair_tendsto p ell d hellp hdp t ht ht1 htp
    hell hd hellb D hD hdb b s g g₀ hg hactual ζ hζ hc hs
  have he := Packet06SpherePairIntegral.limit_pair_integral b t ht ht1 g₀ F hF center hbase ζ hζ hc hs
  rw [he] at hpair
  exact actual_systems_eventually_nonzero t D α ht ht1 hD hα p htp (fun j => (hdp j).trans_le (hdb j).2)
    hν hhalf b hb hbi M hM s hW ζ hζ hc hs _ hpair hstrict
#print axioms OQ14.Packet06ModeExcitation.eventual_actual_excitation
end OQ14.Packet06ModeExcitation
