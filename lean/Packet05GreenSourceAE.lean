import Packet05CompactGreenH2

/-! Convolution depends only on the actual source's almost-everywhere class. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet05GreenSourceAE
open MeasureTheory OQ14.Maxwell OQ14.KernelConvolution

theorem response_source_congr (q ρ σ : Space → ℂ) (h : ρ =ᵐ[volume] σ) :
    response q ρ = response q σ := by
  funext x
  unfold response
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

end OQ14.Packet05GreenSourceAE
#print axioms OQ14.Packet05GreenSourceAE.response_source_congr
