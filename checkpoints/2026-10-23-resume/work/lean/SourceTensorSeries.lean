import SourceTensorResponse
import VectorReactionPositive

/-! The actual material core tensor equals the complete total-index reaction series. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.SourceTensorSeries
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceDielectricModes
open OQ14.SourceModeDatum OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization OQ14.SphereHarmonicHilbert

def kernel (c : Coefficient) (d : Data) (i j : Fin 3) (p : Space × Space) : ℂ :=
  if hy : ‖p.2‖<d.R then SourceTensorResponse.reaction c d p.2 hy p.1 i j else 0

def term (d : Data) (a : TotalIndex) (i j : Fin 3) : Space × Space → ℂ :=
  VectorReactionTerms.term true a i j d.gs d.R d.X d.hR+
    VectorReactionTerms.term false a i j (d.gs.map teLayer) d.R d.X d.hR

def series (d : Data) (i j : Fin 3) (p : Space × Space) : ℂ := ∑' a : TotalIndex,term d a i j p

theorem term_zero (d : Data) (a : Index 0) (i j : Fin 3) : term d ⟨0,a⟩ i j=0 := by
  simp only [term,VectorReactionPositive.term_zero,add_zero]

theorem kernel_eq_series (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (b B T : ℝ) (hb : 0≤b) (hB : 0≤B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B)
    (hT : 2≤T) (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hTR : T<d.R) (hbR : b<d.R)
    (p : Space × Space) (hp : ‖p‖≤b) (i j : Fin 3) : kernel c d i j p=series d i j p := by
  have hx : ‖p.1‖<d.R := ((norm_fst_le p).trans hp).trans_lt hbR
  have hy : ‖p.2‖≤b := (norm_snd_le p).trans hp
  have hyR : ‖p.2‖<d.R := hy.trans_lt hbR
  have h := SourceTensorResponse.actual_hasSum c d hm hdisp hu b B T hb hB hscale hT hBT hTR p.1 p.2 hx hy hyR i j
  have he : HasSum (fun a : PositiveIndex => term d (VectorLimitIdentification.positive a) i j p)
      (SourceTensorResponse.reaction c d p.2 hyR p.1 i j) := h
  have ht := (VectorLimitIdentification.positive_hasSum_iff
    (fun a : TotalIndex => term d a i j p)
    (fun a => congrFun (term_zero d a i j) p)
    (SourceTensorResponse.reaction c d p.2 hyR p.1 i j)).mp he
  exact (dif_pos hyR).trans ht.tsum_eq.symm

theorem kernel_eventually_series (c : Coefficient) (d : Data)
    (hm : ∀ x : Space,(c.value (VectorFourier.coordinateMap x) : ℂ)=sigma d ‖x‖-1)
    (hdisp : ∀ g∈d.gs,g.q^2=g.σ) (hu : IsUnit (DynamicVolume.volumeBlock c 1 d.X))
    (b B T : ℝ) (hb : 0≤b) (hB : 0≤B) (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B)
    (hT : 2≤T) (hBT : 2*(B*AngularExteriorBounds.base)≤T) (hTR : T<d.R) (hbR : b<d.R)
    (p : Space × Space) (hp : ‖p‖<b) (i j : Fin 3) :
    kernel c d i j=ᶠ[nhds p] series d i j := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hp)] with z hz
  exact kernel_eq_series c d hm hdisp hu b B T hb hB hscale hT hBT hTR hbR z (mem_ball_zero_iff.mp hz).le i j

end OQ14.SourceTensorSeries
#print axioms OQ14.SourceTensorSeries.term_zero
#print axioms OQ14.SourceTensorSeries.kernel_eq_series
#print axioms OQ14.SourceTensorSeries.kernel_eventually_series
