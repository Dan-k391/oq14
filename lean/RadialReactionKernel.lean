import RadialStackHighTail

/-! Actual two-radius scalar reaction and its first mixed radial derivatives. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.RadialReactionKernel

open Set OQ14.HankelRealBasis OQ14.RiccatiBarrier

def reaction (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R)
    (x y : ℝ) : ℂ :=
  RadialSource.scalarGreen l gs R X hR x y -
    (regular l (min x y) : ℂ)*irregular l (max x y)

theorem reaction_eq (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R)
    (x y : ℝ) : reaction l gs R X hR x y =
      RadialSource.gamma l gs R X hR*(regular l x : ℂ)*regular l y := by
  rw [reaction,RadialSource.scalarGreen_formula]
  ring

theorem reaction_hasDerivAt_left (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (x y : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t => reaction l gs R X hR t y)
      (RadialSource.gamma l gs R X hR*(regularD l x : ℂ)*regular l y) x := by
  simpa only [reaction_eq] using
    (((real_basis_hasDerivAt l x hx).1.ofReal_comp.const_mul
      (RadialSource.gamma l gs R X hR)).mul_const (regular l y : ℂ))

theorem reaction_hasDerivAt_right (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t => reaction l gs R X hR x t)
      (RadialSource.gamma l gs R X hR*(regular l x : ℂ)*regularD l y) y := by
  simpa only [reaction_eq,mul_assoc] using
    ((real_basis_hasDerivAt l y hy).1.ofReal_comp.const_mul
      (RadialSource.gamma l gs R X hR*(regular l x : ℂ)))

theorem regular_monotone_barrier (l : ℕ) (R : ℝ) (hR : 0 < R) (hb : R^2 < ν l) :
    MonotoneOn (regular l) (Ioc 0 R) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc _ _)
  · intro x hx
    exact (real_basis_hasDerivAt l x hx.1.ne').1.continuousAt.continuousWithinAt
  · intro x hx
    exact (real_basis_hasDerivAt l x (interior_subset hx).1.ne').1.hasDerivWithinAt
  · intro x hx
    exact (barrier_positive l R hR hb x (interior_subset hx)).2.le

theorem regular_compact_bound (l : ℕ) (R s x : ℝ) (hR : 0 < R) (hb : R^2 < ν l)
    (hx : 0 < x) (hxs : x ≤ s) (hsR : s ≤ R) :
    |regular l x| ≤ regular l s := by
  rw [abs_of_pos (barrier_positive l R hR hb x ⟨hx,hxs.trans hsR⟩).1]
  exact regular_monotone_barrier l R hR hb ⟨hx,hxs.trans hsR⟩ ⟨hx.trans_le hxs,hsR⟩ hxs

theorem regularD_compact_bound (l : ℕ) (R a s x : ℝ) (hR : 0 < R) (hb : R^2 < ν l)
    (ha : 0 < a) (hax : a ≤ x) (hxs : x ≤ s) (hsR : s ≤ R) :
    |regularD l x| ≤ ((l : ℝ)+1)/a*regular l s := by
  have hx : 0 < x := ha.trans_le hax
  have hp := barrier_positive l R hR hb x ⟨hx,hxs.trans hsR⟩
  have hlog := (RiccatiLogDerivative.barrier_logDerivative_bounds l R hR hb x ⟨hx,hxs.trans hsR⟩).2
  have hload : x*regularD l x ≤ ((l : ℝ)+1)*regular l x := (div_le_iff₀ hp.1).mp hlog
  have hs := regular_compact_bound l R s x hR hb hx hxs hsR
  rw [abs_of_pos hp.1] at hs
  rw [abs_of_pos hp.2]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ ha).mpr
  have hprod := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ (l : ℝ)+1)
  nlinarith [mul_le_mul_of_nonneg_right hax hp.2.le]

def radialFactor (l : ℕ) (d : Bool) (x : ℝ) : ℝ :=
  if d then regularD l x else regular l x

def derivativeComponent (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ) (hR : 0 < R)
    (d e : Bool) (x y : ℝ) : ℂ :=
  RadialSource.gamma l gs R X hR*(radialFactor l d x : ℂ)*radialFactor l e y

theorem component_false_false (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (x y : ℝ) :
    derivativeComponent l gs R X hR false false x y = reaction l gs R X hR x y := by
  simp only [derivativeComponent,radialFactor,Bool.false_eq_true,ite_false,reaction_eq]

theorem component_mixed_hasDerivAt (l : ℕ) (gs : List RadialStack.Layer) (R X : ℝ)
    (hR : 0 < R) (x y : ℝ) (hy : y ≠ 0) :
    HasDerivAt (fun t => derivativeComponent l gs R X hR true false x t)
      (derivativeComponent l gs R X hR true true x y) y := by
  simpa only [derivativeComponent,radialFactor,Bool.false_eq_true,ite_false,ite_true,mul_assoc] using
    ((real_basis_hasDerivAt l y hy).1.ofReal_comp.const_mul
      (RadialSource.gamma l gs R X hR*(regularD l x : ℂ)))

def gapConstant (a : ℝ) : ℝ := max 1 (1/a)

theorem radialFactor_compact_bound (l : ℕ) (R a s x : ℝ) (d : Bool)
    (hR : 0 < R) (hb : R^2 < ν l) (ha : 0 < a) (hax : a ≤ x)
    (hxs : x ≤ s) (hsR : s ≤ R) :
    |radialFactor l d x| ≤ gapConstant a*((l : ℝ)+1)*regular l s := by
  have hx : 0 < x := ha.trans_le hax
  have hs : 0 < regular l s := (barrier_positive l R hR hb s ⟨hx.trans_le hxs,hsR⟩).1
  have hc : 1 ≤ gapConstant a := le_max_left _ _
  have hca : 1/a ≤ gapConstant a := le_max_right _ _
  cases d with
  | false =>
    change |regular l x| ≤ _
    apply (regular_compact_bound l R s x hR hb hx hxs hsR).trans
    have hh : 1 ≤ gapConstant a*((l : ℝ)+1) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) l]
    nlinarith
  | true =>
    change |regularD l x| ≤ _
    apply (regularD_compact_bound l R a s x hR hb ha hax hxs hsR).trans
    apply mul_le_mul_of_nonneg_right _ hs.le
    convert mul_le_mul_of_nonneg_right hca (by positivity : 0 ≤ (l : ℝ)+1) using 1
    ring

theorem component_norm_bound (l : ℕ) (gs : List RadialStack.Layer) (R X a s x y : ℝ)
    (hR : 0 < R) (d e : Bool) (hb : R^2 < ν l) (ha : 0 < a)
    (hx : x ∈ Icc a s) (hy : y ∈ Icc a s) (hsR : s ≤ R) :
    ‖derivativeComponent l gs R X hR d e x y‖ ≤
      gapConstant a^2*((l : ℝ)+1)^2*(‖RadialSource.gamma l gs R X hR‖*(regular l s)^2) := by
  have h1 := radialFactor_compact_bound l R a s x d hR hb ha hx.1 hx.2 hsR
  have h2 := radialFactor_compact_bound l R a s y e hR hb ha hy.1 hy.2 hsR
  simp only [derivativeComponent,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  have hprod := mul_le_mul h1 h2 (abs_nonneg _) (by
    have hc : 0 ≤ gapConstant a := zero_le_one.trans (le_max_left _ _)
    have hs := (barrier_positive l R hR hb s ⟨ha.trans_le (hx.1.trans hx.2),hsR⟩).1
    positivity)
  have hm := mul_le_mul_of_nonneg_left hprod (norm_nonneg (RadialSource.gamma l gs R X hR))
  convert hm using 1 <;> ring

end OQ14.RadialReactionKernel

#print axioms OQ14.RadialReactionKernel.reaction_eq
#print axioms OQ14.RadialReactionKernel.reaction_hasDerivAt_left
#print axioms OQ14.RadialReactionKernel.reaction_hasDerivAt_right
#print axioms OQ14.RadialReactionKernel.regular_monotone_barrier
#print axioms OQ14.RadialReactionKernel.regular_compact_bound
#print axioms OQ14.RadialReactionKernel.regularD_compact_bound
#print axioms OQ14.RadialReactionKernel.component_false_false
#print axioms OQ14.RadialReactionKernel.component_mixed_hasDerivAt
#print axioms OQ14.RadialReactionKernel.radialFactor_compact_bound
#print axioms OQ14.RadialReactionKernel.component_norm_bound
