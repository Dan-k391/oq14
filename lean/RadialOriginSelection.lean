import RadialBoundarySelection
import RiccatiOriginLimits

/-! Genuine regular radial selection from actual origin continuity and the ODE. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialOriginSelection

open Complex Filter Set OQ14.RadialRellich OQ14.RadialBoundarySelection
  OQ14.RiccatiOriginSeries OQ14.RiccatiOriginLimits
open scoped Topology

def regular (l : ℕ) (k : ℂ) (r : ℝ) : ℂ := origin l (k*r)

def regularD (l : ℕ) (k : ℂ) (r : ℝ) : ℂ := k*originD l (k*r)

theorem regular_continuousAt_zero (l : ℕ) (k : ℂ) : ContinuousAt (regular l k) 0 := by
  have harg : ContinuousAt (fun r : ℝ => k*(r : ℂ)) 0 :=
    (continuous_const.mul Complex.continuous_ofReal).continuousAt
  exact (origin_hasDerivAt l (k*(0 : ℝ))).continuousAt.comp (f := fun r : ℝ => k*(r : ℂ)) harg

theorem regularD_continuousAt_zero (l : ℕ) (k : ℂ) : ContinuousAt (regularD l k) 0 := by
  have hD : ContinuousAt (originD l) 0 := by
    rw [show originD l=(fun z : ℂ => z^l*normalizedSlope l z) from funext (originD_factor l)]
    exact (continuousAt_id.pow l).mul (normalizedSlope_continuousAt_zero l)
  have hD' : ContinuousAt (originD l) (k*(0 : ℝ)) := by simpa only [ofReal_zero,mul_zero] using hD
  have harg : ContinuousAt (fun r : ℝ => k*(r : ℂ)) 0 :=
    (continuous_const.mul Complex.continuous_ofReal).continuousAt
  exact continuousAt_const.mul (hD'.comp (f := fun r : ℝ => k*(r : ℂ)) harg)

theorem regular_zero (l : ℕ) (k : ℂ) : regular l k 0=0 := by simp only [regular,ofReal_zero,mul_zero,origin_zero]

theorem regular_hankel (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    regular l k r=(outgoing l k r+incoming l k r)/2 := by
  exact origin_eq_psi l _ (mul_ne_zero hk (ofReal_ne_zero.mpr hr))

theorem regularD_hankel (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    regularD l k r=(outgoingD l k r+incomingD l k r)/2 := by
  rw [regularD,originD_eq_psiD l _ (mul_ne_zero hk (ofReal_ne_zero.mpr hr))]
  unfold OQ14.ModalAlgebra.psiD outgoingD incomingD
  ring

theorem regular_hasDerivAt (l : ℕ) (k : ℂ) (r : ℝ) :
    HasDerivAt (regular l k) (regularD l k r) r := by
  have h := ((origin_hasDerivAt l (k*r)).comp (r : ℂ)
    ((hasDerivAt_id (r : ℂ)).const_mul k)).comp_ofReal
  convert h using 1
  dsimp [regularD]
  ring

theorem regularD_hasDerivAt (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (regularD l k) (radialCoefficient l k r*regular l k r) r := by
  have he : regularD l k =ᶠ[𝓝 r] fun t => (outgoingD l k t+incomingD l k t)/2 := by
    filter_upwards [eventually_ne_nhds hr] with t ht
    exact regularD_hankel l k hk t ht
  have hd := ((outgoingD_hasDerivAt l k hk r hr).add (incomingD_hasDerivAt l k hk r hr)).div_const 2
  convert hd.congr_of_eventuallyEq he using 1
  rw [regular_hankel l k hk r hr]
  ring

theorem regular_outgoing_wronskian (l : ℕ) (k : ℂ) (hk : k ≠ 0) (r : ℝ) (hr : r ≠ 0) :
    regular l k r*outgoingD l k r-outgoing l k r*regularD l k r=I*k := by
  rw [regular_hankel l k hk r hr,regularD_hankel l k hk r hr]
  linear_combination -(radial_wronskian l k hk r hr)/2

theorem regular_selection (l : ℕ) (k : ℂ) (hk : k ≠ 0) (L : ℝ) (hL : 0 < L)
    (f df : ℝ → ℂ) (hfc : ContinuousAt f 0) (hdfc : ContinuousAt df 0) (hf0 : f 0=0)
    (hf : ∀ r ∈ Ioo 0 L,HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo 0 L,HasDerivAt df (radialCoefficient l k r*f r) r) :
    ∃ a : ℂ,∀ r ∈ Ioo 0 L,f r=a*regular l k r := by
  have hn (r : ℝ) (hr : r ∈ Ioo 0 L) : r ≠ 0 := ne_of_gt hr.1
  have hW : I*k ≠ 0 := mul_ne_zero I_ne_zero hk
  obtain ⟨a,b,hexp⟩ := ode_two_solution_expansion_on (Ioo 0 L) isOpen_Ioo (convex_Ioo 0 L).isPreconnected
    f df (regular l k) (regularD l k) (outgoing l k) (outgoingD l k) (radialCoefficient l k)
    (I*k) hW hf hdf (fun r _ => regular_hasDerivAt l k r)
    (fun r hr => regularD_hasDerivAt l k hk r (hn r hr))
    (fun r hr => outgoing_hasDerivAt l k hk r (hn r hr))
    (fun r hr => outgoingD_hasDerivAt l k hk r (hn r hr))
    (fun r hr => regular_outgoing_wronskian l k hk r (hn r hr))
  let w : ℝ → ℂ := fun r => f r*regularD l k r-regular l k r*df r
  have hwc : ContinuousAt w 0 := (hfc.mul (regularD_continuousAt_zero l k)).sub
    ((regular_continuousAt_zero l k).mul hdfc)
  have hwd (r : ℝ) (hr : r ∈ Ioo 0 L) : HasDerivAt w 0 r :=
    ode_wronskian_hasDerivAt f df (regular l k) (regularD l k) (radialCoefficient l k) r
      (hf r hr) (hdf r hr) (regular_hasDerivAt l k r) (regularD_hasDerivAt l k hk r (hn r hr))
  obtain ⟨c,hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo 0 L).isPreconnected
    (fun r hr => (hwd r hr).differentiableAt.differentiableWithinAt) (fun r hr => (hwd r hr).deriv)
  have hcl : (0 : ℝ) ∈ closure (Ioo 0 L) := by
    rw [closure_Ioo hL.ne]
    exact ⟨le_rfl,hL.le⟩
  have hc0 : w 0=c := by
    have h := hwc.continuousWithinAt.mem_closure hcl (fun r hr =>
      show w r ∈ ({c} : Set ℂ) from Set.mem_singleton_iff.mpr (hc r hr))
    simpa only [closure_singleton,Set.mem_singleton_iff] using h
  have hcz : c=0 := by simpa only [w,hf0,regular_zero,zero_mul,sub_self] using hc0.symm
  have hwz (r : ℝ) (hr : r ∈ Ioo 0 L) : w r=0 := (hc r hr).trans hcz
  let r₀ := L/2
  have hr₀ : r₀ ∈ Ioo 0 L := ⟨half_pos hL,by dsimp [r₀]; linarith⟩
  have heq : f =ᶠ[𝓝 r₀] fun r => a*regular l k r+b*outgoing l k r := by
    filter_upwards [isOpen_Ioo.mem_nhds hr₀] with r hr
    exact hexp r hr
  have hdd : df r₀=a*regularD l k r₀+b*outgoingD l k r₀ :=
    (hf r₀ hr₀).unique ((((regular_hasDerivAt l k r₀).const_mul a).add
      ((outgoing_hasDerivAt l k hk r₀ (hn r₀ hr₀)).const_mul b)).congr_of_eventuallyEq heq)
  have hb : b=0 := by
    have hw := hwz r₀ hr₀
    dsimp only [w] at hw
    rw [hexp r₀ hr₀,hdd] at hw
    have hbw : b*(I*k)=0 := by
      linear_combination -hw-b*(regular_outgoing_wronskian l k hk r₀ (hn r₀ hr₀))
    exact (mul_eq_zero.mp hbw).resolve_right hW
  refine ⟨a,?_⟩
  intro r hr
  simpa only [hb,zero_mul,add_zero] using hexp r hr

end OQ14.RadialOriginSelection

#print axioms OQ14.RadialOriginSelection.regular_continuousAt_zero
#print axioms OQ14.RadialOriginSelection.regularD_continuousAt_zero
#print axioms OQ14.RadialOriginSelection.regular_zero
#print axioms OQ14.RadialOriginSelection.regular_hankel
#print axioms OQ14.RadialOriginSelection.regularD_hankel
#print axioms OQ14.RadialOriginSelection.regular_hasDerivAt
#print axioms OQ14.RadialOriginSelection.regularD_hasDerivAt
#print axioms OQ14.RadialOriginSelection.regular_outgoing_wronskian
#print axioms OQ14.RadialOriginSelection.regular_selection
