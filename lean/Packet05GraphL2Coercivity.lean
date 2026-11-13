import Packet05GraphHermitianForm
import Packet05GraphSlopeMultiplier
import Packet05UniformGraphMetric
import WeakPoynting.DivCurl

/-! Quantitative L² coercivity of the actual graph metric, with an explicit
constant controlled by a bound on the graph slopes. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphL2Coercivity
open MeasureTheory OQ14.ConicalJunctionPhysical OQ14.WeakCurl OQ14.DivCurl
  OQ14.Packet05GraphSlope OQ14.Packet05GraphSlopeMultiplier OQ14.Packet05UniformGraphMetric
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_metric_l2_coercive (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (Q : L2Vector) (M : ℝ) (hM : ∀ x, |OQ14.Packet05GraphSlope.slope g 0 x| ≤ M ∧
      |OQ14.Packet05GraphSlope.slope g 1 x| ≤ M)
    (B0 B1 : ℝ) (hB0 : ∀ x, ‖slopeC g 0 x‖ ≤ B0) (hB1 : ∀ x, ‖slopeC g 1 x‖ ≤ B1) :
    ‖Q 0‖^2 + ‖Q 1‖^2 + ‖Q 2‖^2 ≤ (2+4*M^2) *
      (‖Q 0 - slopeMul g hg 0 B0 hB0 (Q 2)‖^2 +
       ‖Q 1 - slopeMul g hg 1 B1 hB1 (Q 2)‖^2 + ‖Q 2‖^2) := by
  let R0 := Q 0 - slopeMul g hg 0 B0 hB0 (Q 2)
  let R1 := Q 1 - slopeMul g hg 1 B1 hB1 (Q 2)
  have ha : Integrable (fun x => Complex.normSq (Q 0 x) + Complex.normSq (Q 1 x) + Complex.normSq (Q 2 x)) :=
    ((scalar_normSq_integrable (Q 0)).add (scalar_normSq_integrable (Q 1))).add (scalar_normSq_integrable (Q 2))
  have hb : Integrable (fun x => (2+4*M^2) *
      (Complex.normSq (R0 x) + Complex.normSq (R1 x) + Complex.normSq (Q 2 x))) :=
    (((scalar_normSq_integrable R0).add (scalar_normSq_integrable R1)).add (scalar_normSq_integrable (Q 2))).const_mul _
  have hi := integral_mono_ae ha hb (show ∀ᵐ x ∂volume,
      Complex.normSq (Q 0 x) + Complex.normSq (Q 1 x) + Complex.normSq (Q 2 x) ≤
        (2+4*M^2) * (Complex.normSq (R0 x) + Complex.normSq (R1 x) + Complex.normSq (Q 2 x)) by
    filter_upwards [Lp.coeFn_sub (Q 0) (slopeMul g hg 0 B0 hB0 (Q 2)),
      Lp.coeFn_sub (Q 1) (slopeMul g hg 1 B1 hB1 (Q 2)),
      slopeMul_ae g hg 0 B0 hB0 (Q 2), slopeMul_ae g hg 1 B1 hB1 (Q 2)] with x hr0 hr1 hs0 hs1
    have h0 : R0 x = Q 0 x - slopeC g 0 x * Q 2 x := by
      change (Q 0 - slopeMul g hg 0 B0 hB0 (Q 2) : L2Scalar) x = _
      rw [hr0]
      simp only [Pi.sub_apply, hs0]
    have h1 : R1 x = Q 1 x - slopeC g 1 x * Q 2 x := by
      change (Q 1 - slopeMul g hg 1 B1 hB1 (Q 2) : L2Scalar) x = _
      rw [hr1]
      simp only [Pi.sub_apply, hs1]
    rw [h0,h1]
    exact complex_graph_metric_uniform _ _ M _ _ _ (hM x).1 (hM x).2)
  rw [integral_const_mul] at hi
  have el := integral_add ((scalar_normSq_integrable (Q 0)).add (scalar_normSq_integrable (Q 1))) (scalar_normSq_integrable (Q 2))
  have er := integral_add ((scalar_normSq_integrable R0).add (scalar_normSq_integrable R1)) (scalar_normSq_integrable (Q 2))
  have el' := integral_add (scalar_normSq_integrable (Q 0)) (scalar_normSq_integrable (Q 1))
  have er' := integral_add (scalar_normSq_integrable R0) (scalar_normSq_integrable R1)
  simp only [Pi.add_apply] at el er
  rw [el, er, el', er', ← scalar_norm_squared (Q 0), ← scalar_norm_squared (Q 1),
    ← scalar_norm_squared (Q 2), ← scalar_norm_squared R0, ← scalar_norm_squared R1] at hi
  exact hi

end OQ14.Packet05GraphL2Coercivity
#print axioms OQ14.Packet05GraphL2Coercivity.graph_metric_l2_coercive
