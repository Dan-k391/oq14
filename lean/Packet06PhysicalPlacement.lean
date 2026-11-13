import Packet06PlacedKernel
import Packet06FrequencyPlacement
import Packet06OutgoingMode
import Packet07PlanarCenters

/-! Exact frequency placement of the actual normalized mode, and cluster control. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06PhysicalPlacement
open Metric Set Maxwell Packet06PlacedKernel Packet06PhysicalNormalization

def point (s : ℝ) (a x : Space) : Space := a+s⁻¹ • Packet06CyclicRotation.rotate x

theorem point_distance (s : ℝ) (hs : 0 < s) (a x : Space) :
    dist (point s a x) a = s⁻¹*‖x‖ := by
  simp only [point,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs),Packet06CyclicRotation.rotate_norm]

theorem cluster_inside (s r δ : ℝ) (hs : 0 < s) (hδ : δ ≤ r*s)
    (a x : Space) (hx : x ∈ ball 0 δ) : point s a x ∈ ball a r := by
  rw [mem_ball,point_distance s hs a x]
  have hx' : ‖x‖ < δ := by simpa using hx
  have hmul := mul_lt_mul_of_pos_left (hx'.trans_le hδ) (inv_pos.mpr hs)
  calc s⁻¹*‖x‖ < s⁻¹*(r*s) := hmul
    _ = r := by field_simp

theorem frequency_cluster (target r : ℝ) (ht : 0 < target) (hr : 0 < r)
    (z₀ z : ℂ) (hz₀ : 0 < z₀.re) (hz : 0 < z.re)
    (hclose : |z.re-z₀.re| < z₀.re/2) (a x : Space)
    (hx : x ∈ ball 0 (r*target/(2*z₀.re))) :
    point (target/z.re) a x ∈ ball a r := by
  have hupper : z.re < 2*z₀.re := by have := (abs_lt.mp hclose).2; linarith
  apply cluster_inside (target/z.re) r (r*target/(2*z₀.re)) (div_pos ht hz) _ a x hx
  rw [div_le_iff₀ (by positivity : 0 < 2*z₀.re)]
  have hdiv : z.re*(target/z.re)=target := mul_div_cancel₀ _ hz.ne'
  have hbound := mul_le_mul_of_nonneg_left hupper.le (div_pos ht hz).le
  nlinarith

theorem normalized_outgoing_at_frequency (c : StaticCoefficient.Coefficient)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : reciprocalNorm c R z u=1) (hz : 0 < z.re) (hi : z.im < 0)
    (Q : ℝ) (hQ : Q < z.re/(-2*z.im)) (target : ℝ) (ht : 0 < target) (a : Space) :
    ∃ s : ℝ, 0 < s ∧ ((s : ℂ)*z).re=target ∧ ((s : ℂ)*z).im<0 ∧
      Q < ((s : ℂ)*z).re/(-2*((s : ℂ)*z).im) ∧
      (∀ x : Space, x ∉ closedBall 0 (R/s+‖a‖) →
        (placedCoefficient s a c).value (VectorFourier.coordinateMap x)=0) ∧
      ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z)
        (R/s+‖a‖) (placedUnknown s a u)=0 ∧
      reciprocalNorm (placedCoefficient s a c) (R/s+‖a‖) ((s : ℂ)*z)
        (placedUnknown s a u)=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode (placedCoefficient s a c) ((s : ℂ)*z)
        (R/s+‖a‖) (placedUnknown s a u) := by
  obtain ⟨s,hs,hre,him,hquality⟩ :=
    Packet06FrequencyPlacement.positive_real_frequency z target hz ht
  obtain ⟨hsupport,hkernel,hunit,hne⟩ := placed_normalized_kernel c R hR hc z u hu hN s hs a
  have hratio : ((s : ℂ)*z).re/(-2*((s : ℂ)*z).im)=z.re/(-2*z.im) := by
    simpa only [neg_mul,div_neg,neg_div] using hquality
  refine ⟨s,hs,hre,?_,?_,hsupport,hkernel,hunit,?_⟩
  · rw [him]; exact mul_neg_of_pos_of_neg hs hi
  · rw [hratio]; exact hQ
  · exact Packet06OutgoingMode.actual_outgoing_mode _ _ _
      (add_nonneg (div_nonneg hR hs.le) (norm_nonneg a)) _ hsupport hkernel hne

end OQ14.Packet06PhysicalPlacement
#print axioms OQ14.Packet06PhysicalPlacement.point_distance
#print axioms OQ14.Packet06PhysicalPlacement.cluster_inside
#print axioms OQ14.Packet06PhysicalPlacement.frequency_cluster
#print axioms OQ14.Packet06PhysicalPlacement.normalized_outgoing_at_frequency
