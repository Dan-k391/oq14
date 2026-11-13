import Packet06PlacedMaterialField
import Packet06VectorPeak
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.Packet06PlacedPeaks
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06CyclicRotation
open OQ14.WeakCurl (previous next)

theorem point_qmp (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) :
    Measure.QuasiMeasurePreserving (Packet06PhysicalPlacement.point s a) volume volume := by
  have hrot := rotation.measurePreserving.quasiMeasurePreserving
  have hscale := DilationL2.smul_qmp_space s⁻¹ (inv_ne_zero hs.ne')
  have hshift := (measurePreserving_add_left (volume : Measure Maxwell.Space) a).quasiMeasurePreserving
  exact hshift.comp (hscale.comp hrot)

theorem inverse_point (s : ℝ) (hs : 0 < s) (a x : Maxwell.Space) :
    unrotate (s • (Packet06PhysicalPlacement.point s a x-a)) = x := by
  simp only [Packet06PhysicalPlacement.point,add_sub_cancel_left,smul_smul,mul_inv_cancel₀ hs.ne',one_smul]
  exact unrotate_rotate x

theorem point_ball (s : ℝ) (hs : 0 < s) (a center x : Maxwell.Space) (r : ℝ)
    (hx : x ∈ ball center r) :
    Packet06PhysicalPlacement.point s a x ∈ ball (Packet06PhysicalPlacement.point s a center) (r/s) := by
  have hrot : rotate (x-center) = rotate x-rotate center := rotation.map_sub x center
  have hd : dist (Packet06PhysicalPlacement.point s a x) (Packet06PhysicalPlacement.point s a center) =
      s⁻¹*dist x center := by
    simp only [dist_eq_norm,Packet06PhysicalPlacement.point,add_sub_add_left_eq_sub,← smul_sub,← hrot,
      norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs),rotate_norm]
  rw [mem_ball,hd,div_eq_mul_inv]
  exact (mul_lt_mul_of_pos_left hx (inv_pos.mpr hs)).trans_eq (by ring)

theorem material_peak (c : StaticCoefficient.Coefficient) (R T : ℝ) (hR : 0 ≤ R) (hRT : R ≤ T)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (z : ℂ) (u : VectorFourier.VectorL2) (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c R z u=1)
    (s : ℝ) (hs : 0 < s) (a center : Maxwell.Space) (U : ℝ) (hU : R/s+‖a‖ ≤ U)
    (r M : ℝ) (k : Fin 3)
    (hχ : ∀ x ∈ ball center r, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hpeak : 0 < (volume.restrict (ball center r)) {x | M <
      ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z R T u) k x‖}) :
    0 < (volume.restrict (ball (Packet06PhysicalPlacement.point s a center) (r/s))) {y |
      ((Real.sqrt s*s : ℝ)*M) < ‖Packet06LocalPencil.response (Packet06PlacedKernel.placedCoefficient s a c)
        ((s : ℂ)*z) (R/s+‖a‖) U (Packet06PlacedKernel.placedUnknown s a u) (VectorFourier.coordinateMap y) (next k)‖} := by
  by_contra hn
  have hzero : (volume.restrict (ball (Packet06PhysicalPlacement.point s a center) (r/s))) {y |
      ((Real.sqrt s*s : ℝ)*M) < ‖Packet06LocalPencil.response (Packet06PlacedKernel.placedCoefficient s a c)
        ((s : ℂ)*z) (R/s+‖a‖) U (Packet06PlacedKernel.placedUnknown s a u) (VectorFourier.coordinateMap y) (next k)‖} = 0 :=
    le_antisymm (le_of_not_gt hn) bot_le
  have hnot : ∀ᵐ y : Maxwell.Space, y ∈ ball (Packet06PhysicalPlacement.point s a center) (r/s) →
      ¬ ((Real.sqrt s*s : ℝ)*M < ‖Packet06LocalPencil.response (Packet06PlacedKernel.placedCoefficient s a c)
        ((s : ℂ)*z) (R/s+‖a‖) U (Packet06PlacedKernel.placedUnknown s a u) (VectorFourier.coordinateMap y) (next k)‖) := by
    exact ae_imp_of_ae_restrict (by rw [ae_iff]; simpa using hzero)
  have hcov := Packet06PlacedMaterialField.placed_response_material_ae c R T hR hRT hc z u hu hN s hs a U hU (next k)
  have hpull := (point_qmp s hs a).ae (hnot.and hcov)
  have hcoord := NewtonL2.physicalCoordinate_ae (Packet06LocalPencil.response c z R T u) k
  have hne : (Real.sqrt s*s : ℝ) > 0 := mul_pos (Real.sqrt_pos.2 hs) hs
  have hbad : ∀ᵐ x : Maxwell.Space ∂volume.restrict (ball center r),
      ¬ (M < ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z R T u) k x‖) := by
    filter_upwards [ae_restrict_of_ae hpull,ae_restrict_of_ae hcoord,ae_restrict_mem measurableSet_ball] with x hx hcoord' hxb
    have hp := hx.2 (by simpa only [inverse_point s hs a x] using hχ x hxb)
    have hprev : previous (next k) = k := by fin_cases k <;> rfl
    rw [inverse_point s hs a x,hprev] at hp
    have hb := hx.1 (point_ball s hs a center x r hxb)
    rw [hp,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hne,←hcoord'] at hb
    intro hgt
    apply hb
    exact mul_lt_mul_of_pos_left hgt hne
  rw [ae_iff] at hbad
  have hz : (volume.restrict (ball center r)) {x | M < ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z R T u) k x‖} = 0 := by
    simpa only [not_not] using hbad
  exact (ne_of_gt hpeak) hz
#print axioms OQ14.Packet06PlacedPeaks.point_qmp
#print axioms OQ14.Packet06PlacedPeaks.inverse_point
#print axioms OQ14.Packet06PlacedPeaks.point_ball
#print axioms OQ14.Packet06PlacedPeaks.material_peak
end OQ14.Packet06PlacedPeaks
