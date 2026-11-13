import RiccatiRaising
import RadialBoundarySelection
import OutgoingModeGluing
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04RaisingSelection
open Complex MeasureTheory Set Filter OQ14.RadialRellich OQ14.ModalAlgebra
open scoped Topology

theorem outgoing_raising (l : ℕ) (z : ℂ) (hz : z ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    (l+1 : ℂ) * outgoing l z r - (r : ℂ) * outgoingD l z r =
      (z * r) * outgoing (l+1) z r := by
  have hn := mul_ne_zero hz (Complex.ofReal_ne_zero.mpr hr)
  dsimp only [outgoing, outgoingD]
  rw [RiccatiRaising.xi_raising l (z*r) hn]
  field_simp [hn]
  ring

theorem incoming_raising (l : ℕ) (z : ℂ) (hz : z ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    (l+1 : ℂ) * incoming l z r - (r : ℂ) * incomingD l z r =
      (z * r) * incoming (l+1) z r := by
  have hn := mul_ne_zero hz (Complex.ofReal_ne_zero.mpr hr)
  dsimp only [incoming, incomingD]
  rw [RiccatiRaising.xiMinus_raising l (z*r) hn]
  field_simp [hn]
  ring

theorem incoming_coefficient_zero (l : ℕ) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (a b c : ℂ)
    (he : (fun r => a * outgoing l z r + b * incoming l z r)
      =ᵐ[volume.restrict (Ioo 1 T)] fun r => c * outgoing l z r) : b = 0 := by
  have hn (r : ℝ) (hr : r ∈ Ioo 1 T) : r ≠ 0 := by linarith [hr.1]
  have ho : ContinuousOn (outgoing l z) (Ioo 1 T) := fun r hr =>
    (outgoing_hasDerivAt l z hz r (hn r hr)).continuousAt.continuousWithinAt
  have hi : ContinuousOn (incoming l z) (Ioo 1 T) := fun r hr =>
    (incoming_hasDerivAt l z hz r (hn r hr)).continuousAt.continuousWithinAt
  have heq := Measure.eqOn_open_of_ae_eq he isOpen_Ioo
    ((continuousOn_const.mul ho).add (continuousOn_const.mul hi)) (continuousOn_const.mul ho)
  let r := (1+T)/2
  have hr : r ∈ Ioo 1 T := by dsimp [r]; constructor <;> linarith
  have hevent : (fun t => a * outgoing l z t + b * incoming l z t)
      =ᶠ[𝓝 r] fun t => c * outgoing l z t := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
    exact heq ht
  have hder := ((outgoing_hasDerivAt l z hz r (hn r hr)).const_mul a).add
    ((incoming_hasDerivAt l z hz r (hn r hr)).const_mul b)
  have hd : a*outgoingD l z r+b*incomingD l z r=c*outgoingD l z r :=
    (hder.congr_of_eventuallyEq hevent.symm).unique
      ((outgoing_hasDerivAt l z hz r (hn r hr)).const_mul c)
  have hv := heq hr
  have hm : b * (outgoing l z r * incomingD l z r - incoming l z r * outgoingD l z r) = 0 := by
    linear_combination outgoing l z r * hd - outgoingD l z r * hv
  rw [radial_wronskian l z hz r (hn r hr)] at hm
  exact (mul_eq_zero.mp hm).resolve_right
    (mul_ne_zero (mul_ne_zero (by norm_num) I_ne_zero) hz)

theorem ode_raised_outgoing_selection (l : ℕ) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (f df : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo 1 T, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo 1 T, HasDerivAt df (radialCoefficient l z r * f r) r)
    (c : ℂ) (hraise : ∀ᵐ r : ℝ ∂volume.restrict (Ioo 1 T),
      (l+1 : ℂ)*f r-(r : ℂ)*df r = c*(z*r)*outgoing (l+1) z r) :
    ∃ a : ℂ, ∀ r ∈ Ioo 1 T, f r = a * outgoing l z r := by
  obtain ⟨a,b,hexp⟩ := RadialBoundarySelection.radial_ode_expansion_interval
    l z hz 1 T (by norm_num) f df hf hdf
  have hn (r : ℝ) (hr : r ∈ Ioo 1 T) : r ≠ 0 := by linarith [hr.1]
  have hd (r : ℝ) (hr : r ∈ Ioo 1 T) :
      df r = a * outgoingD l z r + b * incomingD l z r := by
    have he : f =ᶠ[𝓝 r] fun t => a * outgoing l z t + b * incoming l z t := by
      filter_upwards [isOpen_Ioo.mem_nhds hr] with t ht
      exact hexp t ht
    exact ((hf r hr).congr_of_eventuallyEq he.symm).unique
      (((outgoing_hasDerivAt l z hz r (hn r hr)).const_mul a).add
        ((incoming_hasDerivAt l z hz r (hn r hr)).const_mul b))
  have hb : b = 0 := incoming_coefficient_zero (l+1) z hz T hT a b c (by
    filter_upwards [hraise, ae_restrict_mem measurableSet_Ioo] with r hh hr
    rw [hexp r hr, hd r hr] at hh
    have h1 := outgoing_raising l z hz r (hn r hr)
    have h2 := incoming_raising l z hz r (hn r hr)
    apply mul_left_cancel₀ (mul_ne_zero hz (Complex.ofReal_ne_zero.mpr (hn r hr)))
    linear_combination hh - a*h1 - b*h2)
  refine ⟨a, fun r hr => ?_⟩
  simpa only [hb, zero_mul, add_zero] using hexp r hr

end OQ14.Packet04RaisingSelection
#print axioms OQ14.Packet04RaisingSelection.outgoing_raising
#print axioms OQ14.Packet04RaisingSelection.incoming_raising
#print axioms OQ14.Packet04RaisingSelection.incoming_coefficient_zero
#print axioms OQ14.Packet04RaisingSelection.ode_raised_outgoing_selection
