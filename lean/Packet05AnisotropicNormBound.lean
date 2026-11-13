import Packet05FourierDerivativeNorm
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05AnisotropicNormBound
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.DivCurlCompact
  OQ14.Packet05WeakFourier OQ14.Packet05AnisotropicEmbedding
  OQ14.Packet05AnisotropicWeakEmbedding OQ14.Packet05FourierDerivativeNorm

theorem finite_majorant {ι : Type} [Fintype ι] (w : Space → ℂ) (hw : MemLp w 2 volume)
    (f : ι → Space → ℂ) (hf : ∀ i, MemLp (f i) 2 volume)
    (h : ∀ x, ‖w x‖ ≤ ∑ i, ‖f i x‖) :
    ‖hw.toLp w‖ ≤ ∑ i, ‖(hf i).toLp (f i)‖ := by
  classical
  have hm := eLpNorm_mono_real (p := (2 : ENNReal)) (μ := volume) h
  have hs := eLpNorm_sum_le (s := Finset.univ)
    (f := fun i x => ‖f i x‖) (fun i _ => (hf i).norm.aestronglyMeasurable)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have he : eLpNorm w 2 volume ≤ ∑ i, eLpNorm (f i) 2 volume := by
    apply hm.trans
    have heq : (∑ i, fun x => ‖f i x‖) = (fun x => ∑ i, ‖f i x‖) := by ext x; simp
    rw [heq] at hs
    simpa only [eLpNorm_norm] using hs
  have ht : (∑ i, eLpNorm (f i) 2 volume) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr (fun i _ => (hf i).eLpNorm_ne_top)
  have hr := ENNReal.toReal_mono ht he
  rw [ENNReal.toReal_sum (fun i _ => (hf i).eLpNorm_ne_top)] at hr
  simpa only [Lp.norm_toLp] using hr

end OQ14.Packet05AnisotropicNormBound
#print axioms OQ14.Packet05AnisotropicNormBound.finite_majorant
