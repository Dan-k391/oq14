import Packet06PlacedHotspot
import Packet06RoundedPlacement

/-! Exact prescribed-frequency placement of all actual hotspots of one
reciprocally normalized outgoing mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlaceModeHotspots
open Set Metric Maxwell Packet06PhysicalPlacement Packet06PlacedKernel
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06PlacedHotspot

theorem threshold_mono (c : StaticCoefficient.Coefficient) (z : ℂ)
    (v : VectorFourier.VectorL2) (body : Set Space) (center : Space) (r M T B : ℝ)
    (hMT : M ≤ T) (h : PhysicalHotspot c z v body center r T B) :
    PhysicalHotspot c z v body center r M B := by
  obtain ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hplane,hT,hrest⟩ := h
  exact ⟨inside,outside,hi,ho,hiae,hoae,b,x,hx,hplane,hMT.trans_lt hT,hrest⟩

theorem place_mode_hotspots {N : ℕ} (c : StaticCoefficient.Coefficient) (z : ℂ)
    (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 1 → c.value (VectorFourier.coordinateMap x)=0)
    (hχ : ∀ x ∈ ball (0 : Space) 1, c.value (VectorFourier.coordinateMap x) ≠ 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z 1 u=0)
    (hN : Packet06PhysicalNormalization.reciprocalNorm c 1 z u=1)
    (hz : 0 < z.re) (hi : z.im < 0) (Q : ℝ) (hQ : Q < z.re/(-2*z.im))
    (target : ℝ) (htarget : 0 < target) (a : Space) (ha : a 2=0)
    (zbase : ℂ) (hbase : 0 < zbase.re) (hclose : |z.re-zbase.re| < zbase.re/2)
    (body : Set Space) (hb : IsOpen body) (center : Fin N → Space) (r M B : ℝ)
    (hball : ∀ i, closedBall (center i) r ⊆ ball (0 : Space) 1)
    (hhot : ∀ i, Packet06RoundedHotspot.HotspotAbove c z u body (center i) r
      (max M 0/(Real.sqrt (target/(2*zbase.re))*(target/(2*zbase.re)))) B) :
    let s := target/z.re
    0 < s ∧ ((s : ℂ)*z).re=target ∧ ((s : ℂ)*z).im<0 ∧
      Q < ((s : ℂ)*z).re/(-2*((s : ℂ)*z).im) ∧
      (∀ x : Space, x ∉ closedBall 0 (1/s+‖a‖) →
        (placedCoefficient s a c).value (VectorFourier.coordinateMap x)=0) ∧
      ComplexConvolutionAnalytic.volumeBlock (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖)
        (placedUnknown s a u)=0 ∧
      Packet06PhysicalNormalization.reciprocalNorm (placedCoefficient s a c) (1/s+‖a‖) ((s : ℂ)*z)
        (placedUnknown s a u)=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode (placedCoefficient s a c) ((s : ℂ)*z) (1/s+‖a‖)
        (placedUnknown s a u) ∧
      ∀ i, PhysicalHotspot (placedCoefficient s a c) ((s : ℂ)*z) (placedUnknown s a u)
        (placement s (div_pos htarget hz) a '' body) (point s a (center i)) (r/s) M (scale s*B) := by
  dsimp only
  let s := target/z.re
  have hs : 0 < s := div_pos htarget hz
  have hre : ((s : ℂ)*z).re=target := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    dsimp [s]
    field_simp
  have him : ((s : ℂ)*z).im<0 := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_neg_of_pos_of_neg hs hi
  have hratio : ((s : ℂ)*z).re/(-2*((s : ℂ)*z).im)=z.re/(-2*z.im) := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    field_simp [hs.ne',ne_of_lt hi]
    ring
  obtain ⟨hpc,hpk,hNp,hne⟩ := placed_normalized_kernel c 1 (by norm_num) hc z u hu hN s hs a
  have hout := Packet06OutgoingMode.actual_outgoing_mode _ _ _
    (add_nonneg (div_nonneg (by norm_num) hs.le) (norm_nonneg a)) _ hpc hpk hne
  have hsmin : target/(2*zbase.re) ≤ s := by
    dsimp [s]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*zbase.re) hz).mpr
    have hh := (abs_lt.mp hclose).2
    nlinarith
  have hthreshold := Packet06RoundedPlacement.scaled_threshold s (target/(2*zbase.re)) M
    (div_pos htarget (by positivity)) hsmin
  refine ⟨hs,hre,him,by rw [hratio]; exact hQ,hpc,hpk,hNp,hout,?_⟩
  intro i
  apply threshold_mono _ _ _ _ _ _ _ _ _ hthreshold
  exact placed_actual_hotspot c hc hχ z u hu hN body hb (center i) r _ B (hball i)
    (hhot i) s hs a ha

end OQ14.Packet06PlaceModeHotspots
#print axioms OQ14.Packet06PlaceModeHotspots.threshold_mono
#print axioms OQ14.Packet06PlaceModeHotspots.place_mode_hotspots
