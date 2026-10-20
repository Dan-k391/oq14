import RiccatiOriginLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! # Actual regular Riccati positivity in the radial barrier -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RiccatiBarrier

open Filter Set Metric OQ14.RiccatiOriginSeries OQ14.RiccatiOriginLimits
open OQ14.HankelRealBasis OQ14.HankelEnergy
open scoped Topology

theorem positive_second_order (u du q : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (huc : Continuous u) (hduc : Continuous du)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (du x) x)
    (hdu : ∀ x ∈ Icc a b, HasDerivAt du (q x*u x) x)
    (hq : ∀ x ∈ Icc a b, 0 ≤ q x) (hua : 0 < u a) (hdua : 0 < du a) :
    ∀ x ∈ Icc a b, 0 < u x ∧ 0 < du x := by
  have huPos : ∀ x ∈ Icc a b, 0 < u x := by
    intro x hx
    by_contra hxneg
    let S := Icc a x ∩ {t : ℝ | u t ≤ 0}
    have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_le huc continuous_const)
    obtain ⟨t,ht,hmin⟩ := hS.exists_isMinOn ⟨x,⟨⟨hx.1,le_rfl⟩,not_lt.mp hxneg⟩⟩
      continuous_id.continuousOn
    have ht0 : u t ≤ 0 := ht.2
    have hat : a < t := by
      have hta : a ≤ t := ht.1.1
      by_contra hnot
      have he : t = a := le_antisymm (not_lt.mp hnot) hta
      have htneg := ht0
      rw [he] at htneg
      linarith
    have htb : t ≤ b := ht.1.2.trans hx.2
    have hpos (s : ℝ) (hs : s ∈ Ioo a t) : 0 < u s := by
      by_contra hnot
      have hsS : s ∈ S := by
        refine ⟨⟨hs.1.le,hs.2.le.trans ht.1.2⟩,?_⟩
        change u s ≤ 0
        exact le_of_not_gt hnot
      have hts : t ≤ s := hmin hsS
      linarith [hs.2]
    have hmonoD : MonotoneOn du (Icc a t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a t) hduc.continuousOn
      · intro s hs
        rw [interior_Icc] at hs
        exact (hdu s ⟨hs.1.le,hs.2.le.trans htb⟩).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hdu s ⟨hs.1.le,hs.2.le.trans htb⟩).deriv]
        exact mul_nonneg (hq s ⟨hs.1.le,hs.2.le.trans htb⟩) (hpos s hs).le
    have hmonoU : MonotoneOn u (Icc a t) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc a t) huc.continuousOn
      · intro s hs
        rw [interior_Icc] at hs
        exact (hu s ⟨hs.1.le,hs.2.le.trans htb⟩).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hu s ⟨hs.1.le,hs.2.le.trans htb⟩).deriv]
        exact (hdua.trans_le (hmonoD ⟨le_rfl,hat.le⟩ ⟨hs.1.le,hs.2.le⟩ hs.1.le)).le
    have hut : u a ≤ u t := hmonoU ⟨le_rfl,hat.le⟩ ⟨hat.le,le_rfl⟩ hat.le
    linarith [ht0]
  have hmonoD : MonotoneOn du (Icc a b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hduc.continuousOn
    · intro s hs
      rw [interior_Icc] at hs
      exact (hdu s ⟨hs.1.le,hs.2.le⟩).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hdu s ⟨hs.1.le,hs.2.le⟩).deriv]
      exact mul_nonneg (hq s ⟨hs.1.le,hs.2.le⟩) (huPos s ⟨hs.1.le,hs.2.le⟩).le
  intro x hx
  exact ⟨huPos x hx,hdua.trans_le (hmonoD ⟨le_rfl,hab⟩ hx hx.1)⟩

def u (l : ℕ) (r : ℝ) : ℝ := (origin l (r : ℂ)).re
def du (l : ℕ) (r : ℝ) : ℝ := (originD l (r : ℂ)).re
def ν (l : ℕ) : ℝ := (l : ℝ)*(l+1)

theorem u_continuous (l : ℕ) : Continuous (u l) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact Complex.continuous_re.continuousAt.comp
    ((origin_hasDerivAt l (r : ℂ)).continuousAt.comp (f := Complex.ofReal) (x := r)
      Complex.continuous_ofReal.continuousAt)

theorem du_continuous (l : ℕ) : Continuous (du l) := by
  have heq : originD l = deriv (origin l) := funext (fun z => (origin_hasDerivAt l z).deriv.symm)
  apply continuous_iff_continuousAt.mpr
  intro r
  have hc : ContinuousAt (originD l) (r : ℂ) := by
    rw [heq]
    exact (origin_analyticAt l (r : ℂ)).deriv.continuousAt
  exact Complex.continuous_re.continuousAt.comp
    (hc.comp (f := Complex.ofReal) (x := r) Complex.continuous_ofReal.continuousAt)

theorem u_eq_regular (l : ℕ) (r : ℝ) (hr : r ≠ 0) : u l r = regular l r := by
  have h := congrArg Complex.re (origin_eq_psi l (r : ℂ) (Complex.ofReal_ne_zero.mpr hr))
  rw [← regular_eq_psi] at h
  exact h

theorem du_eq_regularD (l : ℕ) (r : ℝ) (hr : r ≠ 0) : du l r = regularD l r := by
  have h := congrArg Complex.re (originD_eq_psiD l (r : ℂ) (Complex.ofReal_ne_zero.mpr hr))
  rw [← regularD_eq_psiD] at h
  exact h

theorem u_hasDerivAt (l : ℕ) (r : ℝ) : HasDerivAt (u l) (du l r) r :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt r ((origin_hasDerivAt l (r : ℂ)).comp_ofReal)

theorem u_zero (l : ℕ) : u l 0 = 0 := by simp [u,origin_zero]

theorem du_hasDerivAt (l : ℕ) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (du l) ((ν l/r^2-1)*u l r) r := by
  have heq : du l =ᶠ[𝓝 r] regularD l := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hr] with t ht
    exact du_eq_regularD l t ht
  have hd := (real_basis_ode l r hr).1.congr_of_eventuallyEq heq
  convert hd using 1
  rw [u_eq_regular l r hr]
  simp [ν,weight,angular]

theorem barrier_positive (l : ℕ) (R : ℝ) (hR : 0 < R) (hbarrier : R^2 < ν l)
    (x : ℝ) (hx : x ∈ Ioc 0 R) : 0 < regular l x ∧ 0 < regularD l x := by
  have hp : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  have hlt : ∀ᶠ a : ℝ in 𝓝[>] 0, a < x := nhdsWithin_le_nhds (gt_mem_nhds hx.1)
  obtain ⟨a,ha,hax,hua,hdua⟩ := (hp.and (hlt.and (eventually_regular_positive l))).exists
  have ha' : 0 < u l a := by rwa [u_eq_regular l a ha.ne']
  have hda' : 0 < du l a := by rwa [du_eq_regularD l a ha.ne']
  have hres := positive_second_order (u l) (du l) (fun t => ν l/t^2-1) a x hax.le
    (u_continuous l) (du_continuous l) (fun t _ => u_hasDerivAt l t)
    (fun t ht => du_hasDerivAt l t (ne_of_gt (ha.trans_le ht.1)))
    (fun t ht => by
      have htpos : 0 < t := ha.trans_le ht.1
      have htR : t ≤ R := ht.2.trans hx.2
      have hs : t^2 < ν l := (sq_le_sq₀ htpos.le hR.le |>.mpr htR).trans_lt hbarrier
      exact sub_nonneg.mpr ((le_div_iff₀ (sq_pos_of_pos htpos)).mpr (by nlinarith))) ha' hda' x ⟨hax.le,le_rfl⟩
  simpa only [u_eq_regular l x hx.1.ne',du_eq_regularD l x hx.1.ne'] using hres

end OQ14.RiccatiBarrier

#print axioms OQ14.RiccatiBarrier.positive_second_order
#print axioms OQ14.RiccatiBarrier.u_continuous
#print axioms OQ14.RiccatiBarrier.du_continuous
#print axioms OQ14.RiccatiBarrier.u_eq_regular
#print axioms OQ14.RiccatiBarrier.du_eq_regularD
#print axioms OQ14.RiccatiBarrier.u_hasDerivAt
#print axioms OQ14.RiccatiBarrier.u_zero
#print axioms OQ14.RiccatiBarrier.du_hasDerivAt
#print axioms OQ14.RiccatiBarrier.barrier_positive
