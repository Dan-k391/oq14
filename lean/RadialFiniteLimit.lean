import RadialApproximation

/-! Fixed finite physical stacks converge to their explicit constant-coefficient
transfer products as the common starting radius tends to infinity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RadialFiniteLimit
open Set Filter OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialStack OQ14.RadialApproximation
open scoped Topology

structure Segment where
  q : ℝ
  σ : ℝ
  width : ℝ
  q_pos : 0 < q
  σ_pos : 0 < σ
  width_nonneg : 0 ≤ width

def width : List Segment → ℝ
  | [] => 0
  | g::gs => g.width+width gs

theorem width_nonnegative (gs : List Segment) : 0 ≤ width gs := by
  induction gs with
  | nil => exact le_rfl
  | cons g gs ih => exact add_nonneg g.width_nonneg ih

def propagate (l : ℕ) : List Segment → ℝ → State → State
  | [], _, s => s
  | g::gs, R, s => propagate l gs (R+g.width) (state l g.q g.σ R s (R+g.width))

def reference : List Segment → State → State
  | [], s => s
  | g::gs, s => reference gs (RadialReference.solution g.q g.σ g.q_pos.ne' g.σ_pos.ne' s g.width)

theorem shifted_layer_limit (l : ℕ) (g : Segment) (c : ℝ) (s : ℝ → State)
    (s₀ : State) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R : ℝ => state l g.q g.σ (R+c) (s R) (R+c+g.width)) atTop
      (𝓝 (RadialReference.solution g.q g.σ g.q_pos.ne' g.σ_pos.ne' s₀ g.width)) := by
  have hminus : Tendsto (fun R : ℝ => R-c) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c) tendsto_id
  have hplus : Tendsto (fun R : ℝ => R+c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have h := actual_reference_limit l g.q g.σ g.width g.q_pos.ne' g.σ_pos g.width_nonneg
    (fun R => s (R-c)) s₀ (hs.comp hminus)
  simpa only [Function.comp_def,add_sub_cancel_right] using h.comp hplus

theorem finite_stack_limit (l : ℕ) (gs : List Segment) (c : ℝ) (s : ℝ → State)
    (s₀ : State) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R : ℝ => propagate l gs (R+c) (s R)) atTop (𝓝 (reference gs s₀)) := by
  induction gs generalizing c s s₀ with
  | nil => exact hs
  | cons g gs ih =>
    have h := ih (c+g.width)
      (fun R => state l g.q g.σ (R+c) (s R) (R+c+g.width))
      (RadialReference.solution g.q g.σ g.q_pos.ne' g.σ_pos.ne' s₀ g.width)
      (shifted_layer_limit l g c s s₀ hs)
    simpa only [propagate,reference,add_assoc] using h

def Segment.layer (g : Segment) (R : ℝ) (hR : 0 < R) : Layer where
  q := g.q
  σ := g.σ
  a := R
  b := R+g.width
  q_pos := g.q_pos
  σ_pos := g.σ_pos
  a_pos := hR
  ordered := le_add_of_nonneg_right g.width_nonneg

def layers : (gs : List Segment) → (R : ℝ) → 0 < R → List Layer
  | [], _, _ => []
  | g::gs, R, hR => layers gs (R+g.width) (add_pos_of_pos_of_nonneg hR g.width_nonneg) ++ [g.layer R hR]

theorem chain_append {outer inner : List Layer} {X A R : ℝ}
    (ho : Chain outer X A) (hi : Chain inner A R) : Chain (outer++inner) X R := by
  induction ho with
  | nil A => exact hi
  | cons g gs A h ih => exact Chain.cons g (gs++inner) R (ih hi)

theorem layers_chain (gs : List Segment) (R : ℝ) (hR : 0 < R) :
    Chain (layers gs R hR) (R+width gs) R := by
  induction gs generalizing R with
  | nil => simpa only [layers,width,add_zero] using Chain.nil R
  | cons g gs ih =>
    have hsingle : Chain [g.layer R hR] (R+g.width) R :=
      Chain.cons (g.layer R hR) [] R (Chain.nil R)
    have ht := chain_append (ih (R+g.width) (add_pos_of_pos_of_nonneg hR g.width_nonneg)) hsingle
    simpa only [layers,width,add_assoc] using ht

theorem segment_is_actual_transfer (l : ℕ) (g : Segment) (R : ℝ) (hR : 0 < R) (s : State) :
    state l g.q g.σ R s (R+g.width) =
      act (transfer l g.q g.σ R (R+g.width) g.q_pos.ne' g.σ_pos.ne'
        hR.ne' (add_pos_of_pos_of_nonneg hR g.width_nonneg).ne') s :=
  state_transfer l g.q g.σ R (R+g.width) s g.q_pos.ne' g.σ_pos.ne'
    hR.ne' (add_pos_of_pos_of_nonneg hR g.width_nonneg).ne'

theorem act_compose (m n : RealTransfer) (s : State) :
    act (compose m n) s = act m (act n s) := by
  apply Prod.ext <;> simp only [act,compose,Complex.ofReal_add,Complex.ofReal_mul] <;> ring

def high (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) : Segment where
  q := q
  σ := σ
  width := Real.pi/(2*q)
  q_pos := hq
  σ_pos := hσ
  width_nonneg := by positivity

def low : Segment where
  q := 1
  σ := 1
  width := Real.pi/2
  q_pos := zero_lt_one
  σ_pos := zero_lt_one
  width_nonneg := by positivity

def pairs (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) : ℕ → List Segment
  | 0 => []
  | n+1 => high q σ hq hσ :: low :: pairs q σ hq hσ n

theorem reference_pair (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (s : State) :
    RadialReference.solution 1 1 one_ne_zero one_ne_zero
      (RadialReference.solution q σ hq.ne' hσ.ne' s (Real.pi/(2*q))) (Real.pi/2) =
    act (RadialReference.pair q σ hq.ne' hσ.ne') s :=
  (act_compose _ _ s).symm

theorem reference_pairs (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (n : ℕ) (s : State) :
    reference (pairs q σ hq hσ n) s =
      ((((-q/σ : ℝ)^n : ℝ) : ℂ)*s.1,(((-σ/q : ℝ)^n : ℝ) : ℂ)*s.2) := by
  induction n generalizing s with
  | zero => simp [pairs,reference]
  | succ n ih =>
    simp only [pairs,reference,high,low]
    rw [reference_pair q σ hq hσ,ih]
    obtain ⟨ha,hb,hc,hd⟩ := RadialReference.pair_diagonal q σ hq.ne' hσ.ne'
    apply Prod.ext <;> simp only [act,ha,hb,hc,hd,Complex.ofReal_zero,zero_mul,add_zero,zero_add,
      pow_succ,Complex.ofReal_mul] <;> ring

theorem physical_pairs_limit (l n : ℕ) (q σ : ℝ) (hq : 0 < q) (hσ : 0 < σ) (s : State) :
    Tendsto (fun R : ℝ => propagate l (pairs q σ hq hσ n) R s) atTop
      (𝓝 ((((-q/σ : ℝ)^n : ℝ) : ℂ)*s.1,(((-σ/q : ℝ)^n : ℝ) : ℂ)*s.2)) := by
  simpa only [add_zero,reference_pairs] using
    finite_stack_limit l (pairs q σ hq hσ n) 0 (fun _ => s) s tendsto_const_nhds

end OQ14.RadialFiniteLimit

#print axioms OQ14.RadialFiniteLimit.width_nonnegative
#print axioms OQ14.RadialFiniteLimit.shifted_layer_limit
#print axioms OQ14.RadialFiniteLimit.finite_stack_limit
#print axioms OQ14.RadialFiniteLimit.chain_append
#print axioms OQ14.RadialFiniteLimit.layers_chain
#print axioms OQ14.RadialFiniteLimit.segment_is_actual_transfer
#print axioms OQ14.RadialFiniteLimit.act_compose
#print axioms OQ14.RadialFiniteLimit.reference_pair
#print axioms OQ14.RadialFiniteLimit.reference_pairs
#print axioms OQ14.RadialFiniteLimit.physical_pairs_limit
