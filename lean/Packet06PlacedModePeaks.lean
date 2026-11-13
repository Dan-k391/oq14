import Packet06RoundedPlacement
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace OQ14.Packet06PlacedModePeaks
open MeasureTheory Metric Set OQ14.Maxwell OQ14.Packet06PhysicalPlacement
  OQ14.Packet06PlacedKernel
open scoped Topology

theorem place_mode {N : ℕ} (c : StaticCoefficient.Coefficient) (z : ℂ) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (hz : 0 < z.re) (hi : z.im < 0) (Q : ℝ) (hQ : Q < z.re/(-2*z.im))
    (target : ℝ) (htarget : 0 < target) (a : Maxwell.Space)
    (zbase : ℂ) (hbase : 0 < zbase.re) (hclose : |z.re-zbase.re| < zbase.re/2)
    (center : Fin N → Maxwell.Space) (r : ℝ) (_hr : 0 < r) (coord : Fin N → Fin 3) (M : ℝ)
    (hχ : ∀ i x, x ∈ ball (center i) r → c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hpeak : ∀ i, 0 < (volume.restrict (ball (center i) r)) {x |
      max M 0/(Real.sqrt (target/(2*zbase.re))*(target/(2*zbase.re))) <
        ‖NewtonL2.physicalCoordinate (Packet06LocalPencil.response c z 1 1 u) (coord i) x‖}) :
    ∃ (s : ℝ), 0 < s ∧ ((s : ℂ)*z).re=target ∧ ((s : ℂ)*z).im<0 ∧
      Q < ((s : ℂ)*z).re/(-2*((s : ℂ)*z).im) ∧
      (∀ x : Maxwell.Space, x ∉ closedBall 0 (1/s+‖a‖) →
        (placedCoefficient s a c).value (VectorFourier.coordinateMap x)=0) ∧
      ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖)
        (placedUnknown s a u)=0 ∧
      Packet06PhysicalNormalization.reciprocalNorm (placedCoefficient s a c) (1/s+‖a‖) ((s : ℂ)*z)
        (placedUnknown s a u)=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖)
        (placedUnknown s a u) ∧
      ∀ i, 0 < (volume.restrict (ball (point s a (center i)) (r/s))) {x | M <
        ‖Packet06LocalPencil.response (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖) (1/s+‖a‖)
          (placedUnknown s a u) (VectorFourier.coordinateMap x)‖} := by
  let s := target/z.re
  have hs : 0 < s := div_pos htarget hz
  have hre : ((s : ℂ)*z).re=target := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    dsimp [s]
    field_simp
  have him : ((s : ℂ)*z).im<0 := by simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; exact mul_neg_of_pos_of_neg hs hi
  have hratio : ((s : ℂ)*z).re/(-2*((s : ℂ)*z).im) = z.re/(-2*z.im) := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    have hs0 : (s : ℝ) ≠ 0 := hs.ne'
    field_simp [hs0, ne_of_lt hi]
    ring
  obtain ⟨hpc,hpk,hNp,hne⟩ := placed_normalized_kernel c 1 (by norm_num) hc z u hu hN s hs a
  have hout := Packet06OutgoingMode.actual_outgoing_mode _ _ _
    (add_nonneg (div_nonneg (by norm_num) hs.le) (norm_nonneg a)) _ hpc hpk hne
  have hzupper : z.re < 2*zbase.re := by have h := (abs_lt.mp hclose).2; linarith
  have hsmin : target/(2*zbase.re) ≤ s := by
    dsimp [s]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*zbase.re) hz).mpr
    nlinarith
  have hsminpos : 0 < target/(2*zbase.re) := div_pos htarget (by positivity)
  refine ⟨s,hs,hre,him,by rw [hratio]; exact hQ,hpc,hpk,hNp,hout,?_⟩
  intro i
  have hp := Packet06PlacedPeaks.material_peak c 1 1 (by norm_num) le_rfl hc z u hu hN s hs a (center i)
    (1/s+‖a‖) le_rfl r (max M 0/(Real.sqrt (target/(2*zbase.re))*(target/(2*zbase.re)))) (coord i)
    (hχ i) (hpeak i)
  have hsbound := Packet06RoundedPlacement.scaled_threshold s (target/(2*zbase.re)) M hsminpos hsmin
  apply hp.trans_le
  apply measure_mono
  intro x hx
  change (Real.sqrt s*s)*(max M 0/(Real.sqrt (target/(2*zbase.re))*(target/(2*zbase.re)))) <
    ‖Packet06LocalPencil.response (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖) (1/s+‖a‖)
      (placedUnknown s a u) (VectorFourier.coordinateMap x) (OQ14.WeakCurl.next (coord i))‖ at hx
  change M < ‖Packet06LocalPencil.response (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖) (1/s+‖a‖)
    (placedUnknown s a u) (VectorFourier.coordinateMap x)‖
  exact (hsbound.trans_lt hx).trans_le (PiLp.norm_apply_le _ _)
#print axioms OQ14.Packet06PlacedModePeaks.place_mode
end OQ14.Packet06PlacedModePeaks
