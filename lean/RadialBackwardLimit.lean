import RadialFiniteLimit

/-! Actual inward propagation through the same finite physical stacks. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.RadialBackwardLimit
open Set Filter OQ14.RadialGreen OQ14.RadialLayer OQ14.RadialStack
  OQ14.RadialApproximation OQ14.RadialFiniteLimit
open scoped Topology

def reverseColumns (u v s : State) : State :=
  (v.2*s.1-v.1*s.2,-u.2*s.1+u.1*s.2)

theorem reverseColumns_act (m : RealTransfer) (s : State) :
    reverseColumns (act m (1,0)) (act m (0,1)) s = act (inverse m) s := by
  apply Prod.ext <;> simp [reverseColumns,act,inverse,sub_eq_add_neg]

theorem transfer_reverse (l : ℕ) (q σ a b : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    transfer l q σ b a hq hσ hb ha = inverse (transfer l q σ a b hq hσ ha hb) := by
  cases h : basis l q σ a hq hσ ha
  cases h' : basis l q σ b hq hσ hb
  simp only [transfer,h,h',compose,inverse]
  congr 1 <;> ring

theorem actual_reverse_columns (l : ℕ) (q σ R w : ℝ) (s : State)
    (hq : q ≠ 0) (hσ : σ ≠ 0) (hR : R ≠ 0) (hRw : R+w ≠ 0) :
    state l q σ (R+w) s R = reverseColumns
      (state l q σ R (1,0) (R+w)) (state l q σ R (0,1) (R+w)) s := by
  rw [state_transfer l q σ (R+w) R s hq hσ hRw hR,
    state_transfer l q σ R (R+w) (1,0) hq hσ hR hRw,
    state_transfer l q σ R (R+w) (0,1) hq hσ hR hRw,
    reverseColumns_act,transfer_reverse]

theorem reference_reverse_columns (q σ w : ℝ) (hq : q ≠ 0) (hσ : σ ≠ 0) (s : State) :
    reverseColumns (RadialReference.solution q σ hq hσ (1,0) w)
      (RadialReference.solution q σ hq hσ (0,1) w) s =
        RadialReference.solution q σ hq hσ s (-w) := by
  rw [RadialReference.solution,RadialReference.solution,reverseColumns_act]
  apply Prod.ext <;>
    simp [RadialReference.solution,RadialReference.matrix,act,inverse,Real.cos_neg,Real.sin_neg]

theorem reverseColumns_limit (u v s : ℝ → State) (u₀ v₀ s₀ : State)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R => reverseColumns (u R) (v R) (s R)) atTop (𝓝 (reverseColumns u₀ v₀ s₀)) :=
  ((hv.snd_nhds.mul hs.fst_nhds).sub (hv.fst_nhds.mul hs.snd_nhds)).prodMk_nhds
    ((hu.snd_nhds.neg.mul hs.fst_nhds).add (hu.fst_nhds.mul hs.snd_nhds))

theorem backward_layer_limit (l : ℕ) (g : Segment) (s : ℝ → State) (s₀ : State)
    (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R => state l g.q g.σ (R+g.width) (s R) R) atTop
      (𝓝 (RadialReference.solution g.q g.σ g.q_pos.ne' g.σ_pos.ne' s₀ (-g.width))) := by
  have h1 := actual_reference_limit l g.q g.σ g.width g.q_pos.ne' g.σ_pos g.width_nonneg
    (fun _ => (1,0)) (1,0) tendsto_const_nhds
  have h2 := actual_reference_limit l g.q g.σ g.width g.q_pos.ne' g.σ_pos g.width_nonneg
    (fun _ => (0,1)) (0,1) tendsto_const_nhds
  have h := reverseColumns_limit _ _ s _ _ s₀ h1 h2 hs
  rw [reference_reverse_columns] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (actual_reverse_columns l g.q g.σ R g.width (s R) g.q_pos.ne' g.σ_pos.ne'
    hR.ne' (add_pos_of_pos_of_nonneg hR g.width_nonneg).ne').symm

def retreat (l : ℕ) : List Segment → ℝ → State → State
  | [], _, s => s
  | g::gs, R, s => state l g.q g.σ (R+g.width) (retreat l gs (R+g.width) s) R

def reference : List Segment → State → State
  | [], s => s
  | g::gs, s => RadialReference.solution g.q g.σ g.q_pos.ne' g.σ_pos.ne' (reference gs s) (-g.width)

theorem shifted_backward_layer_limit (l : ℕ) (g : Segment) (c : ℝ) (s : ℝ → State)
    (s₀ : State) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R => state l g.q g.σ (R+c+g.width) (s R) (R+c)) atTop
      (𝓝 (RadialReference.solution g.q g.σ g.q_pos.ne' g.σ_pos.ne' s₀ (-g.width))) := by
  have hminus : Tendsto (fun R : ℝ => R-c) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c) tendsto_id
  have hplus : Tendsto (fun R : ℝ => R+c) atTop atTop :=
    tendsto_atTop_add_const_right atTop c tendsto_id
  have h := backward_layer_limit l g (fun R => s (R-c)) s₀ (hs.comp hminus)
  simpa only [Function.comp_def,add_sub_cancel_right] using h.comp hplus

theorem finite_stack_limit (l : ℕ) (gs : List Segment) (c : ℝ) (s : ℝ → State)
    (s₀ : State) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun R => retreat l gs (R+c) (s R)) atTop (𝓝 (reference gs s₀)) := by
  induction gs generalizing c with
  | nil => exact hs
  | cons g gs ih =>
    have ht := ih (c+g.width)
    have h := shifted_backward_layer_limit l g c
      (fun R => retreat l gs (R+(c+g.width)) (s R)) (reference gs s₀) ht
    simpa only [retreat,reference,add_assoc] using h

theorem traverse_append (l : ℕ) (gs hs : List Layer) (s : State) :
    traverse l (gs++hs) s = traverse l hs (traverse l gs s) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih => simpa only [List.cons_append,RadialStack.traverse] using ih (back l g s)

theorem retreat_is_traverse (l : ℕ) (gs : List Segment) (R : ℝ) (hR : 0 < R) (s : State) :
    retreat l gs R s = traverse l (layers gs R hR) s := by
  induction gs generalizing R s with
  | nil => rfl
  | cons g gs ih =>
    rw [retreat,layers,traverse_append]
    simp only [RadialStack.traverse]
    rw [ih]
    exact state_transfer l g.q g.σ (R+g.width) R _ g.q_pos.ne' g.σ_pos.ne'
      (add_pos_of_pos_of_nonneg hR g.width_nonneg).ne' hR.ne'

end OQ14.RadialBackwardLimit

#print axioms OQ14.RadialBackwardLimit.reverseColumns_act
#print axioms OQ14.RadialBackwardLimit.transfer_reverse
#print axioms OQ14.RadialBackwardLimit.actual_reverse_columns
#print axioms OQ14.RadialBackwardLimit.reference_reverse_columns
#print axioms OQ14.RadialBackwardLimit.reverseColumns_limit
#print axioms OQ14.RadialBackwardLimit.backward_layer_limit
#print axioms OQ14.RadialBackwardLimit.shifted_backward_layer_limit
#print axioms OQ14.RadialBackwardLimit.finite_stack_limit
#print axioms OQ14.RadialBackwardLimit.traverse_append
#print axioms OQ14.RadialBackwardLimit.retreat_is_traverse
