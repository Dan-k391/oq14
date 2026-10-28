import ModalDipoleOrigin

/-! The actual degree-one exponential quotient has a jointly regular scaled
limit at index one and inverse frequency zero. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace OQ14.ModalDipoleInfinity

open Complex Filter Set Metric OQ14.ModalAlgebra
open scoped Topology

def reducedPlus (n w : ℂ) : ℂ :=
  -I+(n+1)/n*w+I*(n+1)^2/n^2*w^2-(n+1)/n^2*w^3

def inverseMinus (n w : ℂ) : ℂ :=
  -I*(n+1)+(n-1)*(n+1)/n*w+I*(n-1)^2*(n+1)/n^2*w^2+(n-1)*(n+1)/n^2*w^3

def scaledQuotient (n w : ℂ) : ℂ := -inverseMinus n w/reducedPlus n w

theorem cPlus_factor (n z : ℂ) (hn : n ≠ 0) :
    cPlus 1 n z=(n-1)*reducedPlus n z⁻¹ := by
  unfold cPlus reducedPlus
  rw [p_one,p_one,pD_one,pD_one]
  norm_num
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow]
  generalize z⁻¹ = w
  field_simp [hn]
  ring_nf
  norm_num [I_sq]
  ring

theorem cMinus_inverse (n z : ℂ) (hn : n ≠ 0) :
    cMinus 1 n z=inverseMinus n z⁻¹ := by
  unfold cMinus inverseMinus
  rw [p_one,pMinus_one,pD_one,pMinusD_one]
  norm_num
  simp only [div_eq_mul_inv,mul_inv_rev,← inv_pow]
  generalize z⁻¹ = w
  field_simp [hn]
  ring_nf
  norm_num [I_sq]
  ring

theorem scaledQuotient_actual (n z : ℂ) (hn : n ≠ 0) (h1 : n ≠ 1) :
    (n-1)*rationalPole 1 n z=scaledQuotient n z⁻¹ := by
  unfold rationalPole scaledQuotient
  rw [cPlus_factor n z hn,cMinus_inverse n z hn,← mul_div_assoc,
    mul_div_mul_left _ _ (sub_ne_zero.mpr h1)]

theorem reducedPlus_one_zero : reducedPlus 1 0 = -I := by simp [reducedPlus]
theorem inverseMinus_one_zero : inverseMinus 1 0 = -2*I := by simp [inverseMinus]; ring
theorem scaledQuotient_one_zero : scaledQuotient 1 0 = -2 := by
  rw [scaledQuotient,inverseMinus_one_zero,reducedPlus_one_zero]
  field_simp

theorem reducedPlus_continuousAt :
    ContinuousAt (fun w : ℂ × ℂ => reducedPlus w.1 w.2) ((1 : ℂ),0) := by
  unfold reducedPlus
  fun_prop (disch := norm_num)

theorem inverseMinus_continuousAt :
    ContinuousAt (fun w : ℂ × ℂ => inverseMinus w.1 w.2) ((1 : ℂ),0) := by
  unfold inverseMinus
  fun_prop (disch := norm_num)

theorem scaledQuotient_continuousAt :
    ContinuousAt (fun w : ℂ × ℂ => scaledQuotient w.1 w.2) ((1 : ℂ),0) := by
  exact inverseMinus_continuousAt.neg.div reducedPlus_continuousAt
    (by rw [reducedPlus_one_zero]; exact neg_ne_zero.mpr I_ne_zero)

theorem reducedPlus_nonzero_near : ∃ δ : ℝ, 0 < δ ∧ ∀ n w : ℂ,
    ‖n-1‖ < δ → ‖w‖ < δ → reducedPlus n w ≠ 0 :=
  ModalDipoleOrigin.product_nonzero_near _ reducedPlus_continuousAt
    (by rw [reducedPlus_one_zero]; exact neg_ne_zero.mpr I_ne_zero)

theorem scaledQuotient_joint_limit {α : Type*} (f : Filter α) (n w : α → ℂ)
    (hn : Tendsto n f (𝓝 1)) (hw : Tendsto w f (𝓝 0)) :
    Tendsto (fun a => scaledQuotient (n a) (w a)) f (𝓝 (-2)) := by
  have hp : Tendsto (fun a => (n a,w a)) f (𝓝 ((1 : ℂ),0)) := hn.prodMk_nhds hw
  have h := scaledQuotient_continuousAt.tendsto.comp hp
  simpa only [scaledQuotient_one_zero] using h

theorem scaled_actual_joint_limit {α : Type*} (f : Filter α) (n z : α → ℂ)
    (hn : Tendsto n f (𝓝 1)) (hz : Tendsto (fun a => (z a)⁻¹) f (𝓝 0))
    (h0 : ∀ᶠ a in f, n a ≠ 0) (h1 : ∀ᶠ a in f, n a ≠ 1) :
    Tendsto (fun a => (n a-1)*rationalPole 1 (n a) (z a)) f (𝓝 (-2)) := by
  apply (scaledQuotient_joint_limit f n (fun a => (z a)⁻¹) hn hz).congr'
  filter_upwards [h0,h1] with a ha hb
  exact (scaledQuotient_actual (n a) (z a) ha hb).symm

theorem product_eventually (P : ℂ → ℂ → Prop)
    (h : ∀ᶠ a : ℂ × ℂ in 𝓝 ((1 : ℂ),0), P a.1 a.2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n w : ℂ, ‖n-1‖ < δ → ‖w‖ < δ → P n w := by
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨δ,hδ,?_⟩
  intro n w hn hw
  apply hball (y := (n,w))
  rw [Prod.dist_eq]
  exact max_lt (by simpa only [dist_eq_norm] using hn) (by simpa using hw)

theorem scaledQuotient_bounds_near : ∃ δ : ℝ, 0 < δ ∧ ∀ n w : ℂ,
    ‖n-1‖ < δ → ‖w‖ < δ → 1 ≤ ‖scaledQuotient n w‖ ∧ ‖scaledQuotient n w‖ ≤ 3 := by
  have hc : Tendsto (fun a : ℂ × ℂ => ‖scaledQuotient a.1 a.2‖)
      (𝓝 ((1 : ℂ),0)) (𝓝 (2 : ℝ)) := by
    simpa only [scaledQuotient_one_zero,norm_neg,norm_ofNat] using
      scaledQuotient_continuousAt.norm.tendsto
  apply product_eventually
  filter_upwards [hc.eventually (Ioo_mem_nhds (by norm_num : (1 : ℝ)<2) (by norm_num : (2 : ℝ)<3))]
    with a ha
  exact ⟨ha.1.le,ha.2.le⟩

theorem actual_bounds_near : ∃ δ : ℝ, 0 < δ ∧ ∀ n z : ℂ,
    n ≠ 0 → n ≠ 1 → ‖n-1‖ < δ → ‖z⁻¹‖ < δ →
      cPlus 1 n z ≠ 0 ∧ 1 ≤ ‖n-1‖*‖rationalPole 1 n z‖ ∧ ‖n-1‖*‖rationalPole 1 n z‖ ≤ 3 := by
  obtain ⟨δ₀,hδ₀,hq⟩ := scaledQuotient_bounds_near
  obtain ⟨δ₁,hδ₁,hp⟩ := reducedPlus_nonzero_near
  refine ⟨min δ₀ δ₁,lt_min hδ₀ hδ₁,?_⟩
  intro n z hn h1 hnd hzd
  have hnq := hnd.trans_le (min_le_left _ _)
  have hzq := hzd.trans_le (min_le_left _ _)
  have hnp := hnd.trans_le (min_le_right _ _)
  have hzp := hzd.trans_le (min_le_right _ _)
  refine ⟨?_,?_⟩
  · rw [cPlus_factor n z hn]
    exact mul_ne_zero (sub_ne_zero.mpr h1) (hp n z⁻¹ hnp hzp)
  · have he : ‖n-1‖*‖rationalPole 1 n z‖=‖scaledQuotient n z⁻¹‖ := by
      rw [← norm_mul,scaledQuotient_actual n z hn h1]
    rw [he]
    exact hq n z⁻¹ hnq hzq

theorem real_actual_bounds : ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℝ, ∀ z : ℂ,
    1 < n → n-1 < δ → ‖z⁻¹‖ < δ → cPlus 1 (n : ℂ) z ≠ 0 ∧
      1/(n-1) ≤ ‖rationalPole 1 (n : ℂ) z‖ ∧ ‖rationalPole 1 (n : ℂ) z‖ ≤ 3/(n-1) := by
  obtain ⟨δ,hδ,h⟩ := actual_bounds_near
  refine ⟨δ,hδ,?_⟩
  intro n z hn hnd hzd
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n ≠ 1 := ne_of_gt hn
  have hp : 0<n-1 := sub_pos.mpr hn
  have he : ‖(n : ℂ)-1‖=n-1 := by
    simp only [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  obtain ⟨hc,hl,hu⟩ := h n z (by exact_mod_cast hn0) (by exact_mod_cast hn1) (he ▸ hnd) hzd
  rw [he] at hl hu
  exact ⟨hc,(div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hl),
    (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hu)⟩

def unitPhase (z : ℂ) : ℂ := z/(‖z‖ : ℂ)

theorem unitPhase_neg_two : unitPhase (-2) = -1 := by norm_num [unitPhase]

theorem unitPhase_continuousAt (z : ℂ) (hz : z ≠ 0) : ContinuousAt unitPhase z := by
  unfold unitPhase
  exact continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp continuous_norm.continuousAt)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem unitPhase_pos_mul (t : ℝ) (ht : 0<t) (z : ℂ) : unitPhase ((t : ℂ)*z)=unitPhase z := by
  simp only [unitPhase,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht,Complex.ofReal_mul]
  exact mul_div_mul_left z (‖z‖ : ℂ) (Complex.ofReal_ne_zero.mpr ht.ne')

theorem real_actual_phase_limit {α : Type*} (f : Filter α) (n : α → ℝ) (z : α → ℂ)
    (hn : Tendsto n f (𝓝 1)) (hz : Tendsto (fun a => (z a)⁻¹) f (𝓝 0))
    (hindex : ∀ᶠ a in f, 1<n a) :
    Tendsto (fun a => unitPhase (rationalPole 1 (n a : ℂ) (z a))) f (𝓝 (-1)) := by
  have hn' : Tendsto (fun a => (n a : ℂ)) f (𝓝 (1 : ℂ)) := by
    simpa only [Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp hn
  have h0 : ∀ᶠ a in f, (n a : ℂ) ≠ 0 := by
    filter_upwards [hindex] with a ha
    exact_mod_cast (by linarith : n a ≠ 0)
  have h1 : ∀ᶠ a in f, (n a : ℂ) ≠ 1 := by
    filter_upwards [hindex] with a ha
    exact_mod_cast ne_of_gt ha
  have hq := scaled_actual_joint_limit f (fun a => (n a : ℂ)) z hn' hz h0 h1
  have hc := (unitPhase_continuousAt (-2) (by norm_num)).tendsto.comp hq
  rw [unitPhase_neg_two] at hc
  apply hc.congr'
  filter_upwards [hindex] with a ha
  have he : (n a : ℂ)-1=((n a-1 : ℝ) : ℂ) := by push_cast; rfl
  simp only [Function.comp_apply]
  rw [he,unitPhase_pos_mul (n a-1) (sub_pos.mpr ha)]

end OQ14.ModalDipoleInfinity

#print axioms OQ14.ModalDipoleInfinity.cPlus_factor
#print axioms OQ14.ModalDipoleInfinity.cMinus_inverse
#print axioms OQ14.ModalDipoleInfinity.scaledQuotient_actual
#print axioms OQ14.ModalDipoleInfinity.reducedPlus_one_zero
#print axioms OQ14.ModalDipoleInfinity.inverseMinus_one_zero
#print axioms OQ14.ModalDipoleInfinity.scaledQuotient_one_zero
#print axioms OQ14.ModalDipoleInfinity.reducedPlus_continuousAt
#print axioms OQ14.ModalDipoleInfinity.inverseMinus_continuousAt
#print axioms OQ14.ModalDipoleInfinity.scaledQuotient_continuousAt
#print axioms OQ14.ModalDipoleInfinity.reducedPlus_nonzero_near
#print axioms OQ14.ModalDipoleInfinity.scaledQuotient_joint_limit
#print axioms OQ14.ModalDipoleInfinity.scaled_actual_joint_limit
#print axioms OQ14.ModalDipoleInfinity.product_eventually
#print axioms OQ14.ModalDipoleInfinity.scaledQuotient_bounds_near
#print axioms OQ14.ModalDipoleInfinity.actual_bounds_near
#print axioms OQ14.ModalDipoleInfinity.real_actual_bounds
#print axioms OQ14.ModalDipoleInfinity.unitPhase_neg_two
#print axioms OQ14.ModalDipoleInfinity.unitPhase_continuousAt
#print axioms OQ14.ModalDipoleInfinity.unitPhase_pos_mul
#print axioms OQ14.ModalDipoleInfinity.real_actual_phase_limit
