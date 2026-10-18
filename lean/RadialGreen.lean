import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Actual radial-transfer source algebra

The entries below are real and obey the determinant-one identity of a
lossless radial Maxwell transfer. Its complex outgoing continuation,
nonzero source denominator, exact reaction coefficient and source-load
Wronskian cancellation are derived from those entries. No Green-kernel
convergence or complete-device theorem is assumed or claimed here.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace OQ14.RadialGreen

open Complex
open scoped ComplexConjugate

structure RealTransfer where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  det_one : a * d - b * c = 1

def outAlpha (m : RealTransfer) : ℂ := (m.d : ℂ) + (-m.b : ℝ) * I
def outBeta (m : RealTransfer) : ℂ := (-m.c : ℝ) + (m.a : ℂ) * I
def sourceGamma (m : RealTransfer) : ℂ := outAlpha m / outBeta m
def coreGain (m : RealTransfer) : ℂ := 1 / ((m.a : ℂ) + (m.c : ℂ) * I)

theorem outgoing_continuation_first (m : RealTransfer) :
    (m.a : ℂ) * outAlpha m + (m.b : ℂ) * outBeta m = 1 := by
  apply Complex.ext <;> simp [outAlpha, outBeta]
  · nlinarith [m.det_one]
  · ring

theorem outgoing_continuation_second (m : RealTransfer) :
    (m.c : ℂ) * outAlpha m + (m.d : ℂ) * outBeta m = I := by
  apply Complex.ext <;> simp [outAlpha, outBeta]
  · ring
  · nlinarith [m.det_one]

theorem outBeta_ne_zero (m : RealTransfer) : outBeta m ≠ 0 := by
  intro h
  have hc := congrArg Complex.re h
  have ha := congrArg Complex.im h
  simp [outBeta] at hc ha
  have hm := m.det_one
  simp [ha, hc] at hm

theorem outBeta_normSq (m : RealTransfer) :
    Complex.normSq (outBeta m) = m.a ^ 2 + m.c ^ 2 := by
  rw [outBeta, Complex.normSq_add_mul_I]
  ring

theorem denominator_pos (m : RealTransfer) : 0 < m.a ^ 2 + m.c ^ 2 := by
  rw [← outBeta_normSq]
  exact Complex.normSq_pos.mpr (outBeta_ne_zero m)

theorem sourceGamma_re (m : RealTransfer) :
    (sourceGamma m).re = (-m.c * m.d - m.a * m.b) /
      (m.a ^ 2 + m.c ^ 2) := by
  simp only [sourceGamma, Complex.div_re, outBeta_normSq]
  simp [outAlpha, outBeta]
  ring

theorem sourceGamma_im (m : RealTransfer) :
    (sourceGamma m).im = -1 / (m.a ^ 2 + m.c ^ 2) := by
  simp only [sourceGamma, Complex.div_im, outBeta_normSq]
  simp [outAlpha, outBeta]
  have hd := ne_of_gt (denominator_pos m)
  field_simp
  nlinarith [m.det_one]

theorem sourceGamma_formula (m : RealTransfer) :
    sourceGamma m =
      (((-m.c * m.d - m.a * m.b : ℝ) : ℂ) - I) /
        ((m.a ^ 2 + m.c ^ 2 : ℝ) : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.div_ofReal_re, Complex.sub_re, Complex.ofReal_re,
      Complex.I_re, sub_zero] using sourceGamma_re m
  · simpa only [Complex.div_ofReal_im, Complex.sub_im, Complex.ofReal_im,
      Complex.I_im, zero_sub] using sourceGamma_im m

theorem sourceGamma_im_negative (m : RealTransfer) :
    (sourceGamma m).im < 0 := by
  rw [sourceGamma_im]
  exact div_neg_of_neg_of_pos (by norm_num) (denominator_pos m)

theorem coreGain_normSq (m : RealTransfer) :
    Complex.normSq (coreGain m) = -(sourceGamma m).im := by
  rw [sourceGamma_im]
  simp [coreGain, map_div₀, Complex.normSq_add_mul_I]
  ring

/-- The reduced radial Wronskian in a vacuum core. -/
def vacuumWronskian (psi psip chi chip : ℝ) : ℝ :=
  psi * chip - psip * chi

def loadDenom (psi psip : ℝ) (h : ℂ) : ℂ := h * psi - psip
def loadGamma (psi psip chi chip : ℝ) (h : ℂ) : ℂ :=
  ((chip : ℂ) - h * chi) / loadDenom psi psip h

theorem loadDenom_ne_zero (psi psip : ℝ) (h : ℂ)
    (hp : 0 < psi) (hpp : 0 < psip) (hh : h.re ≤ 0) :
    loadDenom psi psip h ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  simp [loadDenom] at hr
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hh (le_of_lt hp)]

theorem source_value_cancellation (psi psip chi chip : ℝ) (h : ℂ)
    (hw : vacuumWronskian psi psip chi chip = 1)
    (hd : loadDenom psi psip h ≠ 0) :
    (chi : ℂ) + loadGamma psi psip chi chip h * psi =
      1 / loadDenom psi psip h := by
  have hwc : (psi : ℂ) * chip - (psip : ℂ) * chi = 1 := by
    exact_mod_cast hw
  unfold loadGamma
  field_simp
  unfold loadDenom at *
  linear_combination hwc

theorem source_derivative_cancellation (psi psip chi chip : ℝ) (h : ℂ)
    (hw : vacuumWronskian psi psip chi chip = 1)
    (hd : loadDenom psi psip h ≠ 0) :
    (chip : ℂ) + loadGamma psi psip chi chip h * psip =
      h / loadDenom psi psip h := by
  have hwc : (psi : ℂ) * chip - (psip : ℂ) * chi = 1 := by
    exact_mod_cast hw
  unfold loadGamma
  field_simp
  unfold loadDenom at *
  linear_combination h * hwc

theorem loadDenom_normSq (psi psip : ℝ) (h : ℂ) :
    Complex.normSq (loadDenom psi psip h) =
      Complex.normSq h * psi ^ 2 + psip ^ 2 - 2 * psi * psip * h.re := by
  simp [loadDenom, Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

theorem loadDenom_normSq_lower (psi psip : ℝ) (h : ℂ)
    (hp : 0 ≤ psi) (hpp : 0 ≤ psip) (hh : h.re ≤ 0) :
    Complex.normSq h * psi ^ 2 + psip ^ 2 ≤
      Complex.normSq (loadDenom psi psip h) := by
  rw [loadDenom_normSq]
  have hprod := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hp) hpp) hh
  linarith

/-- Real part of the radial power/load pairing. -/
def radialLoad (u p : ℂ) : ℝ := (p * conj u).re

theorem radialLoad_components (u p : ℂ) :
    radialLoad u p = p.re * u.re + p.im * u.im := by
  simp [radialLoad, Complex.mul_re]

theorem normSq_hasDerivAt {u : ℝ → ℂ} {du : ℂ} {x : ℝ}
    (hu : HasDerivAt u du x) :
    HasDerivAt (fun t => Complex.normSq (u t))
      (2 * radialLoad (u x) du) x := by
  have hr : HasDerivAt (fun t => (u t).re) du.re x := by
    simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hu
  have hi : HasDerivAt (fun t => (u t).im) du.im x := by
    simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hu
  convert (hr.mul hr).add (hi.mul hi) using 1
  simp [radialLoad_components]
  ring

theorem barrier_load_hasDerivAt {u p : ℝ → ℂ} {x ε V : ℝ}
    (hu : HasDerivAt u ((ε : ℂ) * p x) x)
    (hp : HasDerivAt p ((V : ℂ) * u x) x) :
    HasDerivAt (fun t => radialLoad (u t) (p t))
      (ε * Complex.normSq (p x) + V * Complex.normSq (u x)) x := by
  have hur : HasDerivAt (fun t => (u t).re) (ε * (p x).re) x := by
    simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hu
  have hui : HasDerivAt (fun t => (u t).im) (ε * (p x).im) x := by
    simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hu
  have hpr : HasDerivAt (fun t => (p t).re) (V * (u x).re) x := by
    simpa using Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hp
  have hpi : HasDerivAt (fun t => (p t).im) (V * (u x).im) x := by
    simpa using Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hp
  convert (hpr.mul hur).add (hpi.mul hui) using 1
  · funext t
    exact radialLoad_components (u t) (p t)
  · simp [Complex.normSq]
    ring

theorem barrier_state_hasDerivAt {u p : ℝ → ℂ} {x ε V : ℝ}
    (hu : HasDerivAt u ((ε : ℂ) * p x) x)
    (hp : HasDerivAt p ((V : ℂ) * u x) x) :
    HasDerivAt (fun t => Complex.normSq (u t))
      (2 * ε * radialLoad (u x) (p x)) x ∧
    HasDerivAt (fun t => Complex.normSq (p t))
      (2 * V * radialLoad (u x) (p x)) x := by
  constructor
  · convert normSq_hasDerivAt hu using 1
    simp [radialLoad_components]
    ring
  · convert normSq_hasDerivAt hp using 1
    simp [radialLoad_components]
    ring

theorem barrier_load_deriv_nonneg {u p : ℝ → ℂ} {x ε V : ℝ}
    (hu : HasDerivAt u ((ε : ℂ) * p x) x)
    (hp : HasDerivAt p ((V : ℂ) * u x) x)
    (hε : 0 ≤ ε) (hV : 0 ≤ V) :
    0 ≤ deriv (fun t => radialLoad (u t) (p t)) x := by
  rw [(barrier_load_hasDerivAt hu hp).deriv]
  exact add_nonneg (mul_nonneg hε (Complex.normSq_nonneg _))
    (mul_nonneg hV (Complex.normSq_nonneg _))

theorem barrier_state_deriv_nonpos {u p : ℝ → ℂ} {x ε V : ℝ}
    (hu : HasDerivAt u ((ε : ℂ) * p x) x)
    (hp : HasDerivAt p ((V : ℂ) * u x) x)
    (hε : 0 ≤ ε) (hV : 0 ≤ V) (hload : radialLoad (u x) (p x) ≤ 0) :
    deriv (fun t => Complex.normSq (u t)) x ≤ 0 ∧
    deriv (fun t => Complex.normSq (p t)) x ≤ 0 := by
  obtain ⟨hdu, hdp⟩ := barrier_state_hasDerivAt hu hp
  rw [hdu.deriv, hdp.deriv]
  exact ⟨mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hε) hload,
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hV) hload⟩

/-- On a real radial barrier interval the outgoing endpoint load forces both
state magnitudes to decrease outwards. The hypotheses are the actual
first-order ODEs, not a pre-assumed monotonicity property. -/
theorem barrier_interval_monotonicity
    {u p : ℝ → ℂ} {ε V : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (huC : ContinuousOn u (Set.Icc a b))
    (hpC : ContinuousOn p (Set.Icc a b))
    (hode : ∀ x ∈ Set.Ioo a b,
      HasDerivAt u ((ε x : ℂ) * p x) x ∧
      HasDerivAt p ((V x : ℂ) * u x) x)
    (hε : ∀ x ∈ Set.Ioo a b, 0 ≤ ε x)
    (hV : ∀ x ∈ Set.Ioo a b, 0 ≤ V x)
    (hright : radialLoad (u b) (p b) ≤ 0) :
    MonotoneOn (fun x => radialLoad (u x) (p x)) (Set.Icc a b) ∧
    AntitoneOn (fun x => Complex.normSq (u x)) (Set.Icc a b) ∧
    AntitoneOn (fun x => Complex.normSq (p x)) (Set.Icc a b) := by
  have hLC : ContinuousOn (fun x => radialLoad (u x) (p x)) (Set.Icc a b) := by
    simpa only [radialLoad_components] using
      ((Complex.continuous_re.comp_continuousOn hpC).mul
        (Complex.continuous_re.comp_continuousOn huC)).add
      ((Complex.continuous_im.comp_continuousOn hpC).mul
        (Complex.continuous_im.comp_continuousOn huC))
  have hmono : MonotoneOn (fun x => radialLoad (u x) (p x)) (Set.Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hLC
    · intro x hx
      have hi : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
      exact (barrier_load_hasDerivAt (hode x hi).1 (hode x hi).2).differentiableAt.differentiableWithinAt
    · intro x hx
      have hi : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
      exact barrier_load_deriv_nonneg (hode x hi).1 (hode x hi).2 (hε x hi) (hV x hi)
  have hn : ∀ x ∈ Set.Icc a b, radialLoad (u x) (p x) ≤ 0 := by
    intro x hx
    exact le_trans (hmono hx ⟨hab, le_rfl⟩ hx.2) hright
  refine ⟨hmono, ?_, ?_⟩
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (Complex.continuous_normSq.comp_continuousOn huC)
    · intro x hx
      have hi : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
      exact (barrier_state_hasDerivAt (hode x hi).1 (hode x hi).2).1.differentiableAt.differentiableWithinAt
    · intro x hx
      have hi : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
      exact (barrier_state_deriv_nonpos (hode x hi).1 (hode x hi).2
        (hε x hi) (hV x hi) (hn x ⟨le_of_lt hi.1, le_of_lt hi.2⟩)).1
  · apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
      (Complex.continuous_normSq.comp_continuousOn hpC)
    · intro x hx
      have hi : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
      exact (barrier_state_hasDerivAt (hode x hi).1 (hode x hi).2).2.differentiableAt.differentiableWithinAt
    · intro x hx
      have hi : x ∈ Set.Ioo a b := by simpa only [interior_Icc] using hx
      exact (barrier_state_deriv_nonpos (hode x hi).1 (hode x hi).2
        (hε x hi) (hV x hi) (hn x ⟨le_of_lt hi.1, le_of_lt hi.2⟩)).2

/-- The radial first-order system preserves the complex Wronskian. -/
theorem radial_wronskian_hasDerivAt
    {u₁ p₁ u₂ p₂ : ℝ → ℂ} {x ε V : ℝ}
    (hu₁ : HasDerivAt u₁ ((ε : ℂ) * p₁ x) x)
    (hp₁ : HasDerivAt p₁ ((V : ℂ) * u₁ x) x)
    (hu₂ : HasDerivAt u₂ ((ε : ℂ) * p₂ x) x)
    (hp₂ : HasDerivAt p₂ ((V : ℂ) * u₂ x) x) :
    HasDerivAt (fun t => u₁ t * p₂ t - p₁ t * u₂ t) 0 x := by
  convert (hu₁.mul hp₂).sub (hp₁.mul hu₂) using 1
  ring

/-- The real fundamental matrix has zero determinant derivative, directly
from its actual trace-zero radial ODE. -/
theorem transfer_determinant_hasDerivAt
    {a b c d : ℝ → ℝ} {x ε V : ℝ}
    (ha : HasDerivAt a (ε * c x) x)
    (hb : HasDerivAt b (ε * d x) x)
    (hc : HasDerivAt c (V * a x) x)
    (hd : HasDerivAt d (V * b x) x) :
    HasDerivAt (fun t => a t * d t - b t * c t) 0 x := by
  convert (ha.mul hd).sub (hb.mul hc) using 1
  ring

end OQ14.RadialGreen

#print axioms OQ14.RadialGreen.outgoing_continuation_first
#print axioms OQ14.RadialGreen.outgoing_continuation_second
#print axioms OQ14.RadialGreen.outBeta_ne_zero
#print axioms OQ14.RadialGreen.outBeta_normSq
#print axioms OQ14.RadialGreen.denominator_pos
#print axioms OQ14.RadialGreen.sourceGamma_re
#print axioms OQ14.RadialGreen.sourceGamma_im
#print axioms OQ14.RadialGreen.sourceGamma_formula
#print axioms OQ14.RadialGreen.sourceGamma_im_negative
#print axioms OQ14.RadialGreen.coreGain_normSq
#print axioms OQ14.RadialGreen.loadDenom_ne_zero
#print axioms OQ14.RadialGreen.source_value_cancellation
#print axioms OQ14.RadialGreen.source_derivative_cancellation
#print axioms OQ14.RadialGreen.loadDenom_normSq
#print axioms OQ14.RadialGreen.loadDenom_normSq_lower
#print axioms OQ14.RadialGreen.radialLoad_components
#print axioms OQ14.RadialGreen.normSq_hasDerivAt
#print axioms OQ14.RadialGreen.barrier_load_hasDerivAt
#print axioms OQ14.RadialGreen.barrier_state_hasDerivAt
#print axioms OQ14.RadialGreen.barrier_load_deriv_nonneg
#print axioms OQ14.RadialGreen.barrier_state_deriv_nonpos
#print axioms OQ14.RadialGreen.barrier_interval_monotonicity
#print axioms OQ14.RadialGreen.radial_wronskian_hasDerivAt
#print axioms OQ14.RadialGreen.transfer_determinant_hasDerivAt
