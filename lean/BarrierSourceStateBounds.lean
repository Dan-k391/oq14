import RadialGluing
import RadialStackHighTail
import RadialHighOrderBound
import HankelPositive
import RiccatiGaussianBound
import RadialLowTail
import RadialIntermediateBound

/-! Degree-uniform endpoint bounds of the actual source state of a layered stack in the barrier
range: Wronskian cancellation with the radial load sign gives `|w(R)| <= 1/psi'(R)` and
`|p(R)| <= 1/psi(R)` for the core wave at the inner radius, and the exterior outgoing source state
is bounded by the same endpoint quantity at every exterior radius. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.BarrierSourceStateBounds
open Set OQ14.RadialGreen OQ14.RadialStack OQ14.RadialLayer OQ14.RadialPropagation
open OQ14.RadialSource OQ14.RadialGluing OQ14.HankelRealBasis OQ14.HankelEnergy OQ14.ModalAlgebra
open scoped ComplexConjugate

/-- Wronskian cancellation: a state with nonpositive radial load whose Wronskian with a positive
real pair equals one is bounded by that pair. -/
theorem wronskian_load_bound (reg regD : ℝ) (w p : ℂ) (hW : (reg : ℂ)*p-(regD : ℂ)*w=1)
    (hl : radialLoad w p ≤ 0) (h0 : 0 ≤ reg) (h1 : 0 ≤ regD) :
    reg^2*Complex.normSq p+regD^2*Complex.normSq w ≤ 1 := by
  have h := congrArg Complex.normSq hW
  rw [map_one] at h
  rw [radialLoad_components] at hl
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.mul_re,Complex.mul_im,
    Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero] at h
  have hm : 0 ≤ reg*regD := mul_nonneg h0 h1
  simp only [Complex.normSq_apply]
  nlinarith [mul_nonneg hm (neg_nonneg.mpr hl)]

theorem norm_le_of_sq_le {a b : ℝ} (hb : 0 < b) (h : b^2*a^2 ≤ 1) : a ≤ 1/b := by
  rw [le_div_iff₀ hb]
  nlinarith [sq_nonneg (a*b-1),sq_nonneg (a*b+1)]

theorem radialLoad_smul (c u p : ℂ) : radialLoad (c*u) (c*p)=Complex.normSq c*radialLoad u p := by
  unfold radialLoad
  have : (c*p)*(starRingEnd ℂ) (c*u)=((Complex.normSq c : ℝ) : ℂ)*(p*(starRingEnd ℂ) u) := by
    rw [map_mul,Complex.normSq_eq_conj_mul_self]
    ring
  rw [this,Complex.re_ofReal_mul]

/-- The normalized core wave has nonpositive radial load at the inner radius of a barrier stack. -/
theorem core_load_nonpos (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) :
    radialLoad (coreWave l gs R X hR R) (coreWaveD l gs R X hR R) ≤ 0 := by
  obtain ⟨h1,h2⟩ := coreWave_boundary l gs R X hR hX
  have hs := outgoing_traverse_load l gs X hX hbarrier
  set β := (coefficients l gs R X hR).2
  set s := traverse l gs (outgoing l X)
  have e1 : coreWave l gs R X hR R=β⁻¹*s.1 := by rw [h1,div_eq_inv_mul]
  have e2 : coreWaveD l gs R X hR R=β⁻¹*s.2 := by rw [h2,div_eq_inv_mul]
  rw [e1,e2,radialLoad_smul]
  exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hs

/-- Endpoint bound of the normalized core wave in the barrier range. -/
theorem endpoint_state_bound (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l) :
    ‖coreWave l gs R X hR R‖ ≤ 1/regularD l R ∧ ‖coreWaveD l gs R X hR R‖ ≤ 1/regular l R := by
  obtain ⟨hp,hpp⟩ := OQ14.RiccatiBarrier.barrier_positive l R hR hν R ⟨hR,le_rfl⟩
  have hW := coreWave_wronskian l gs R X hR R hR.ne'
  have hb := wronskian_load_bound (regular l R) (regularD l R) _ _ hW
    (core_load_nonpos l gs R X hR hX hbarrier) hp.le hpp.le
  have hn1 : Complex.normSq (coreWave l gs R X hR R) ≤ (1/regularD l R)^2 := by
    rw [div_pow,le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (regular l R)) (Complex.normSq_nonneg (coreWaveD l gs R X hR R))]
  have hn2 : Complex.normSq (coreWaveD l gs R X hR R) ≤ (1/regular l R)^2 := by
    rw [div_pow,le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg (regularD l R)) (Complex.normSq_nonneg (coreWave l gs R X hR R))]
  constructor
  · apply le_of_sq_le_sq _ (by positivity)
    rw [← Complex.normSq_eq_norm_sq]
    exact hn1
  · apply le_of_sq_le_sq _ (by positivity)
    rw [← Complex.normSq_eq_norm_sq]
    exact hn2

/-- One barrier layer does not decrease the squared modulus of the first component inward. -/
theorem back_normSq_ge (l : ℕ) (g : Layer) (s : State) (hbarrier : g.q^2*g.b^2 ≤ angular l)
    (hs : radialLoad s.1 s.2 ≤ 0) :
    Complex.normSq s.1 ≤ Complex.normSq (back l g s).1 := by
  have hout : radialLoad (wave l g s g.b) (waveMomentum l g s g.b) ≤ 0 := by
    rwa [(wave_outer l g s).1,(wave_outer l g s).2]
  have h := (actual_layer_barrier l g.q g.σ
    (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
    g.a g.b g.q_pos.ne' g.σ_pos g.a_pos g.ordered hbarrier hout).2.1
    ⟨le_rfl,g.ordered⟩ ⟨g.ordered,le_rfl⟩ g.ordered
  change Complex.normSq (wave l g s g.b) ≤ Complex.normSq (wave l g s g.a) at h
  rw [(wave_outer l g s).1,(wave_inner l g s).1] at h
  exact h

theorem traverse_normSq_ge (l : ℕ) (gs : List Layer) (s : State)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hs : radialLoad s.1 s.2 ≤ 0) :
    Complex.normSq s.1 ≤ Complex.normSq (traverse l gs s).1 := by
  induction gs generalizing s with
  | nil => exact le_rfl
  | cons g gs ih =>
    exact (back_normSq_ge l g s (hbarrier g List.mem_cons_self) hs).trans
      (ih (back l g s) (fun x hx => hbarrier x (List.mem_cons_of_mem _ hx))
        (back_load l g s (hbarrier g List.mem_cons_self) hs))

/-- The modulus of the outgoing function decreases outward. -/
theorem norm_xi_antitone (l : ℕ) {R r : ℝ} (hR : 0<R) (hr : R ≤ r) : ‖xi l r‖ ≤ ‖xi l R‖ := by
  have hanti : AntitoneOn (fun x : ℝ => Complex.normSq (xi l x)) (Ioi 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    · intro x hx
      exact (OQ14.HankelPositive.xi_normSq_hasDerivAt l x (ne_of_gt hx)).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      exact (OQ14.HankelPositive.xi_normSq_hasDerivAt l x (ne_of_gt hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ioi] at hx
      rw [(OQ14.HankelPositive.xi_normSq_hasDerivAt l x (ne_of_gt hx)).deriv]
      have hw : 0 ≤ x⁻¹ := inv_nonneg.mpr (le_of_lt hx)
      have := OQ14.HankelPositive.squarePoly_derivative_nonnegative l x⁻¹ hw
      have hx2 : 0 < x^2 := pow_pos hx 2
      rw [neg_div]
      exact neg_nonpos.mpr (div_nonneg this hx2.le)
  have h := hanti (show R ∈ Ioi (0 : ℝ) from hR) (show r ∈ Ioi (0 : ℝ) from lt_of_lt_of_le hR hr) hr
  simp only at h
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  exact h


/-- One barrier layer does not decrease the squared modulus of the momentum inward. -/
theorem back_normSq_ge_momentum (l : ℕ) (g : Layer) (s : State) (hbarrier : g.q^2*g.b^2 ≤ angular l)
    (hs : radialLoad s.1 s.2 ≤ 0) :
    Complex.normSq s.2 ≤ Complex.normSq (back l g s).2 := by
  have hout : radialLoad (wave l g s g.b) (waveMomentum l g s g.b) ≤ 0 := by
    rwa [(wave_outer l g s).1,(wave_outer l g s).2]
  have h := (actual_layer_barrier l g.q g.σ
    (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
    g.a g.b g.q_pos.ne' g.σ_pos g.a_pos g.ordered hbarrier hout).2.2
    ⟨le_rfl,g.ordered⟩ ⟨g.ordered,le_rfl⟩ g.ordered
  change Complex.normSq (waveMomentum l g s g.b) ≤ Complex.normSq (waveMomentum l g s g.a) at h
  rw [(wave_outer l g s).2,(wave_inner l g s).2] at h
  exact h

theorem traverse_normSq_ge_momentum (l : ℕ) (gs : List Layer) (s : State)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hs : radialLoad s.1 s.2 ≤ 0) :
    Complex.normSq s.2 ≤ Complex.normSq (traverse l gs s).2 := by
  induction gs generalizing s with
  | nil => exact le_rfl
  | cons g gs ih =>
    exact (back_normSq_ge_momentum l g s (hbarrier g List.mem_cons_self) hs).trans
      (ih (back l g s) (fun x hx => hbarrier x (List.mem_cons_of_mem _ hx))
        (back_load l g s (hbarrier g List.mem_cons_self) hs))

theorem normSq_xiD_hasDerivAt (l : ℕ) (x : ℝ) (hx : 0<x) :
    HasDerivAt (fun t : ℝ => Complex.normSq (xiD l t))
      (-2*weight l x*radialLoad (xi l x) (xiD l x)) x := by
  have h := normSq_hasDerivAt (OQ14.RadialGluing.outgoing_ode l x hx).2
  convert h using 1
  change -2*weight l x*radialLoad (xi l x) (xiD l x)=
    2*radialLoad (xiD l x) ((-(weight l x : ℂ))*xi l x)
  simp only [radialLoad_components,Complex.mul_re,Complex.mul_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im]
  ring

theorem weight_mono {l : ℕ} {s t : ℝ} (hs : 0<s) (hst : s ≤ t) : weight l s ≤ weight l t := by
  unfold weight
  have hA : 0 ≤ angular l := by unfold angular; positivity
  have : angular l/t^2 ≤ angular l/s^2 :=
    div_le_div_of_nonneg_left hA (by positivity) (pow_le_pow_left₀ hs.le hst 2)
  linarith

/-- The momentum modulus of the outgoing function never exceeds its endpoint value or one. -/
theorem normSq_xiD_le_max (l : ℕ) {X x : ℝ} (hX : 0<X) (hx : X ≤ x) :
    Complex.normSq (xiD l x) ≤ max (Complex.normSq (xiD l X)) 1 := by
  have hL (t : ℝ) (ht : 0<t) : radialLoad (xi l t) (xiD l t) ≤ 0 :=
    OQ14.HankelPositive.outgoing_radialLoad_nonpositive l t ht
  have hd (t : ℝ) (ht : 0<t) := normSq_xiD_hasDerivAt l t ht
  by_cases hw : weight l x ≤ 0
  · have hanti : AntitoneOn (fun t : ℝ => Complex.normSq (xiD l t)) (Icc X x) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc X x)
      · intro t ht
        exact (hd t (hX.trans_le ht.1)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hd t (hX.trans ht.1)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have ht0 := hX.trans ht.1
        rw [(hd t ht0).deriv]
        have hwt : weight l t ≤ 0 := (weight_mono ht0 ht.2.le).trans hw
        nlinarith [hL t ht0]
    exact (hanti ⟨le_rfl,hx⟩ ⟨hx,le_rfl⟩ hx).trans (le_max_left _ _)
  · push_neg at hw
    have hx0 : 0<x := hX.trans_le hx
    have hmono : MonotoneOn (fun t : ℝ => Complex.normSq (xiD l t)) (Ici x) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici x)
      · intro t ht
        exact (hd t (hx0.trans_le ht)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        exact (hd t (hx0.trans ht)).differentiableAt.differentiableWithinAt
      · intro t ht
        rw [interior_Ici] at ht
        have ht0 := hx0.trans ht
        rw [(hd t ht0).deriv]
        have hwt : 0 ≤ weight l t := (hw.trans_le (weight_mono hx0 ht.le)).le
        nlinarith [hL t ht0]
    have hlim := OQ14.HankelEnergy.xiD_normSq_tendsto l
    have : Complex.normSq (xiD l x) ≤ 1 := by
      apply ge_of_tendsto hlim
      filter_upwards [Filter.eventually_ge_atTop x] with t ht
      exact hmono Set.left_mem_Ici (show t ∈ Ici x from ht) ht
    exact this.trans (le_max_right _ _)

theorem norm_xiD_le_max (l : ℕ) {X x : ℝ} (hX : 0<X) (hx : X ≤ x) :
    ‖xiD l x‖ ≤ max ‖xiD l X‖ 1 := by
  have h := normSq_xiD_le_max l hX hx
  apply le_of_sq_le_sq _ (le_max_of_le_right zero_le_one)
  rw [← Complex.normSq_eq_norm_sq]
  refine h.trans ?_
  rw [Complex.normSq_eq_norm_sq]
  rcases le_total ‖xiD l X‖ 1 with h1 | h1
  · rw [max_eq_right h1]
    have : max (‖xiD l X‖^2) 1 ≤ 1 := max_le (by nlinarith [norm_nonneg (xiD l X)]) le_rfl
    simpa using this
  · rw [max_eq_left h1]
    have : max (‖xiD l X‖^2) 1 ≤ ‖xiD l X‖^2 := max_le le_rfl (by nlinarith [norm_nonneg (xiD l X)])
    simpa using this

/-- Exterior bound of the actual source state, in the barrier range, uniform in the exterior
radius and in the degree: the first component of the layered source state at every exterior radius is
bounded by `1/psi'(R)`. -/
theorem exterior_state_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l)
    (x : ℝ) (hx : X<x) : ‖(sourceState l gs R X hR x).1‖ ≤ 1/regularD l R := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  have hxX : 0<x := hX.trans hx
  rw [sourceState_exterior l h hR x hx]
  set β := (coefficients l gs R X hR).2
  set s := traverse l gs (outgoing l X)
  have hs0 : radialLoad (outgoing l X).1 (outgoing l X).2 ≤ 0 :=
    OQ14.HankelPositive.outgoing_radialLoad_nonpositive l X hX
  have hge := traverse_normSq_ge l gs (outgoing l X) hbarrier hs0
  have hxi : ‖xi l x‖ ≤ ‖xi l X‖ := norm_xi_antitone l hX hx.le
  have hXs : ‖(outgoing l X).1‖ ≤ ‖s.1‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    exact hge
  have hcw := (endpoint_state_bound l gs R X hR hX hbarrier hν).1
  have hb := (coreWave_boundary l gs R X hR hX).1
  have hcn : ‖coreWave l gs R X hR R‖=‖β‖⁻¹*‖s.1‖ := by
    rw [hb,norm_div,div_eq_inv_mul]
  simp only [Prod.smul_fst,smul_eq_mul,norm_mul,norm_inv]
  calc ‖β‖⁻¹*‖(outgoing l x).1‖=‖β‖⁻¹*‖xi l x‖ := rfl
    _ ≤ ‖β‖⁻¹*‖xi l X‖ := mul_le_mul_of_nonneg_left hxi (inv_nonneg.mpr (norm_nonneg _))
    _ ≤ ‖β‖⁻¹*‖s.1‖ := mul_le_mul_of_nonneg_left hXs (inv_nonneg.mpr (norm_nonneg _))
    _ =‖coreWave l gs R X hR R‖ := hcn.symm
    _ ≤ 1/regularD l R := hcw


/-- Endpoint norms of the exterior amplitude times the outgoing state at the outer radius. -/
theorem exterior_endpoint_norms (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l) :
    ‖(coefficients l gs R X hR).2‖⁻¹*‖xi l X‖ ≤ 1/regularD l R ∧
    ‖(coefficients l gs R X hR).2‖⁻¹*‖xiD l X‖ ≤ 1/regular l R := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  set β := (coefficients l gs R X hR).2
  set s := traverse l gs (outgoing l X)
  have hs0 : radialLoad (outgoing l X).1 (outgoing l X).2 ≤ 0 :=
    OQ14.HankelPositive.outgoing_radialLoad_nonpositive l X hX
  have hge1 := traverse_normSq_ge l gs (outgoing l X) hbarrier hs0
  have hge2 := traverse_normSq_ge_momentum l gs (outgoing l X) hbarrier hs0
  have hXs1 : ‖(outgoing l X).1‖ ≤ ‖s.1‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    exact hge1
  have hXs2 : ‖(outgoing l X).2‖ ≤ ‖s.2‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    exact hge2
  obtain ⟨hcw1,hcw2⟩ := endpoint_state_bound l gs R X hR hX hbarrier hν
  obtain ⟨hb1,hb2⟩ := coreWave_boundary l gs R X hR hX
  have hn1 : ‖coreWave l gs R X hR R‖=‖β‖⁻¹*‖s.1‖ := by
    rw [hb1,norm_div,div_eq_inv_mul]
  have hn2 : ‖coreWaveD l gs R X hR R‖=‖β‖⁻¹*‖s.2‖ := by
    rw [hb2,norm_div,div_eq_inv_mul]
  have hi : (0 : ℝ) ≤ ‖β‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  constructor
  · calc ‖β‖⁻¹*‖xi l X‖ ≤ ‖β‖⁻¹*‖s.1‖ := mul_le_mul_of_nonneg_left hXs1 hi
      _ =‖coreWave l gs R X hR R‖ := hn1.symm
      _ ≤ 1/regularD l R := hcw1
  · calc ‖β‖⁻¹*‖xiD l X‖ ≤ ‖β‖⁻¹*‖s.2‖ := mul_le_mul_of_nonneg_left hXs2 hi
      _ =‖coreWaveD l gs R X hR R‖ := hn2.symm
      _ ≤ 1/regular l R := hcw2

theorem beta_inv_sq_le (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l) :
    (‖(coefficients l gs R X hR).2‖⁻¹)^2 ≤ 1/(regular l R*regularD l R) := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  obtain ⟨hp,hpp⟩ := OQ14.RiccatiBarrier.barrier_positive l R hR hν R ⟨hR,le_rfl⟩
  obtain ⟨h1,h2⟩ := exterior_endpoint_norms l h hR hbarrier hν
  have hone : 1 ≤ ‖xiD l X‖*‖xi l X‖ := by
    have hl := Complex.abs_im_le_norm ((outgoing l X).2*(starRingEnd ℂ) (outgoing l X).1)
    have hI := outgoing_imaginaryLoad l X hX
    rw [← imaginaryLoad,hI,abs_one,norm_mul,Complex.norm_conj] at hl
    exact hl
  set b := ‖(coefficients l gs R X hR).2‖⁻¹ with hb
  have hb0 : 0 ≤ b := inv_nonneg.mpr (norm_nonneg _)
  have e1 : b*‖xi l X‖ ≤ 1/regularD l R := h1
  have e2 : b*‖xiD l X‖ ≤ 1/regular l R := h2
  calc b^2=b^2*1 := by ring
    _ ≤ b^2*(‖xiD l X‖*‖xi l X‖) := mul_le_mul_of_nonneg_left hone (sq_nonneg _)
    _ =(b*‖xiD l X‖)*(b*‖xi l X‖) := by ring
    _ ≤ (1/regular l R)*(1/regularD l R) :=
        mul_le_mul e2 e1 (mul_nonneg hb0 (norm_nonneg _)) (by positivity)
    _ =1/(regular l R*regularD l R) := by field_simp

/-- Exterior momentum bound of the layered source state in the barrier range, uniform in the
exterior radius. -/
theorem exterior_momentum_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l)
    (x : ℝ) (hx : X<x) :
    ‖(sourceState l gs R X hR x).2‖ ≤
      max (1/regular l R) (Real.sqrt (1/(regular l R*regularD l R))) := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  rw [sourceState_exterior l h hR x hx]
  obtain ⟨h1,h2⟩ := exterior_endpoint_norms l h hR hbarrier hν
  have hsq := beta_inv_sq_le l h hR hbarrier hν
  set b := ‖(coefficients l gs R X hR).2‖⁻¹ with hb
  have hb0 : 0 ≤ b := inv_nonneg.mpr (norm_nonneg _)
  have hbs : b ≤ Real.sqrt (1/(regular l R*regularD l R)) := Real.le_sqrt_of_sq_le hsq
  have hxD := norm_xiD_le_max l hX hx.le
  simp only [Prod.smul_snd,smul_eq_mul,norm_mul,norm_inv]
  change b*‖xiD l x‖ ≤ _
  calc b*‖xiD l x‖ ≤ b*max ‖xiD l X‖ 1 := mul_le_mul_of_nonneg_left hxD hb0
    _ =max (b*‖xiD l X‖) b := by rw [mul_max_of_nonneg _ _ hb0,mul_one]
    _ ≤ _ := max_le_max h2 hbs


/-- In the high-order range the regular derivative dominates `(l+1)/(2R)` times the regular value. -/
theorem regularD_lower (l : ℕ) (R : ℝ) (hR : 0<R) (hl : 2*R ≤ l) :
    ((l : ℝ)+1)/(2*R)*regular l R ≤ regularD l R := by
  have hν := OQ14.RadialHighOrderBound.high_order_barrier l R hR hl
  obtain ⟨hp,_⟩ := OQ14.RiccatiBarrier.barrier_positive l R hR hν R ⟨hR,le_rfl⟩
  have hdef := OQ14.RiccatiGaussianBound.deficit_bound l R hR hν R ⟨hR,le_rfl⟩
  have hg := OQ14.RadialHighOrderBound.gamma_ge_half_degree l R hR hl
  have hlr : (2*R : ℝ) ≤ l := hl
  have hl0 : (0 : ℝ) ≤ l := by positivity
  have hden : 0 < (l : ℝ)+OQ14.RiccatiLogDerivative.gamma l R+2 := by linarith
  have hfrac : R^2/((l : ℝ)+OQ14.RiccatiLogDerivative.gamma l R+2) ≤ ((l : ℝ)+1)/2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hR.le hl0]
  have hy : ((l : ℝ)+1)/2 ≤ OQ14.RiccatiBarrierNormalization.y l R := by linarith
  have hyeq := OQ14.RiccatiBarrierNormalization.y_eq l R hR.ne'
    (by rw [OQ14.RiccatiBarrier.u_eq_regular l R hR.ne']; exact hp.ne')
  rw [OQ14.RiccatiBarrier.u_eq_regular l R hR.ne',OQ14.RiccatiBarrier.du_eq_regularD l R hR.ne'] at hyeq
  rw [hyeq] at hy
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ)<2) hp] at hy
  have h2 : ((l : ℝ)+1)*regular l R ≤ 2*(R*regularD l R) := by nlinarith
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  nlinarith

theorem regular_at_lower (l : ℕ) (R : ℝ) (hR : 0<R) (hl : 2*R ≤ l) :
    OQ14.RiccatiSeriesCoefficients.amplitude l 0*R^(l+1)*Real.exp (-R/2) ≤ regular l R := by
  have hν := OQ14.RadialHighOrderBound.high_order_barrier l R hR hl
  have h := OQ14.RiccatiGaussianBound.regular_gaussian_lower l R hR hν R ⟨hR,le_rfl⟩
  have he := OQ14.RadialHighOrderBound.gaussian_exponent_le l R hR hl
  have hexp : Real.exp (-R/2) ≤
      Real.exp (-R^2/(2*((l : ℝ)+OQ14.RiccatiLogDerivative.gamma l R+2))) := by
    apply Real.exp_le_exp.mpr
    have : -R/2 ≤ -(R^2/(2*((l : ℝ)+OQ14.RiccatiLogDerivative.gamma l R+2))) := by linarith
    rw [neg_div] at this ⊢
    simpa [neg_div] using this
  refine le_trans ?_ h
  have hpos : 0 ≤ OQ14.RiccatiSeriesCoefficients.amplitude l 0*R^(l+1) :=
    mul_nonneg (OQ14.RiccatiSeriesCoefficients.amplitude_pos l 0).le (by positivity)
  exact mul_le_mul_of_nonneg_left hexp hpos

/-- Source-weighted exterior bound in the barrier range: the regular value at the source radius times
the exterior source state is `e^(R/2)` times a geometric factor in the degree, for every exterior
radius. -/
theorem source_weighted_exterior (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hl : 2*R ≤ l) (s : ℝ) (hs : 0<s) (hsR : s ≤ R)
    (x : ℝ) (hx : X<x) :
    regular l s*‖(sourceState l gs R X hR x).1‖ ≤
      2*R*Real.exp (R/2)/((l : ℝ)+1)*(s/R)^(l+1) ∧
    regular l s*‖(sourceState l gs R X hR x).2‖ ≤ Real.exp (R/2)*(s/R)^(l+1) := by
  have hν := OQ14.RadialHighOrderBound.high_order_barrier l R hR hl
  obtain ⟨hp,hpp⟩ := OQ14.RiccatiBarrier.barrier_positive l R hR hν R ⟨hR,le_rfl⟩
  have hsup := OQ14.RiccatiGaussianBound.regular_upper l R hR hν s ⟨hs,hsR⟩
  have hlow := regular_at_lower l R hR hl
  have hD := regularD_lower l R hR hl
  have hA := OQ14.RiccatiSeriesCoefficients.amplitude_pos l 0
  set A := OQ14.RiccatiSeriesCoefficients.amplitude l 0
  have hl1 : (0 : ℝ) < (l : ℝ)+1 := by positivity
  have hRl : (2*R : ℝ) ≤ (l : ℝ)+1 := by linarith
  have hDge : regular l R ≤ regularD l R := by
    have : 1 ≤ ((l : ℝ)+1)/(2*R) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    nlinarith
  have hexp : 0 < Real.exp (-R/2) := Real.exp_pos _
  have hRpow : 0 < R^(l+1) := by positivity
  have hrs : regular l R ≥ A*R^(l+1)*Real.exp (-R/2) := hlow
  have hsR' : (s/R)^(l+1) = s^(l+1)/R^(l+1) := div_pow _ _ _
  have hu := exterior_state_bound l h hR hbarrier hν x hx
  have hmom := exterior_momentum_bound l h hR hbarrier hν x hx
  have hpos0 : 0 < regular l R := hp
  have hmax : max (1/regular l R) (Real.sqrt (1/(regular l R*regularD l R))) ≤ 1/regular l R := by
    apply max_le le_rfl
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    rw [div_pow,one_pow]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsreg : regular l s ≤ A*s^(l+1) := hsup
  have hs0 : 0 ≤ regular l s := by
    have := OQ14.RiccatiGaussianBound.regular_gaussian_lower l R hR hν s ⟨hs,hsR⟩
    exact le_trans (by positivity) this
  -- common estimate for 1/regular l R
  have hinv : 1/regular l R ≤ Real.exp (R/2)/(A*R^(l+1)) := by
    rw [div_le_div_iff₀ hpos0 (by positivity)]
    have : Real.exp (R/2)*(A*R^(l+1)*Real.exp (-R/2)) = A*R^(l+1) := by
      rw [mul_comm (A*R^(l+1)) (Real.exp (-R/2)),← mul_assoc,← Real.exp_add]
      have : R/2+-R/2=0 := by ring
      rw [this,Real.exp_zero,one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hrs (Real.exp_pos (R/2)).le]
  have hfinal : regular l s*(1/regular l R) ≤ Real.exp (R/2)*(s/R)^(l+1) := by
    calc regular l s*(1/regular l R) ≤ (A*s^(l+1))*(Real.exp (R/2)/(A*R^(l+1))) :=
          mul_le_mul hsreg hinv (by positivity) (by positivity)
      _ =Real.exp (R/2)*(s/R)^(l+1) := by rw [hsR']; field_simp; ring
  constructor
  · have h1 : ‖(sourceState l gs R X hR x).1‖ ≤ (2*R/((l : ℝ)+1))*(1/regular l R) := by
      refine hu.trans ?_
      rw [div_le_iff₀ hpp]
      have hq : ((l : ℝ)+1)/(2*R) ≤ regularD l R/regular l R := by
        rw [le_div_iff₀ hpos0]; exact hD
      calc (1 : ℝ)=(2*R/((l : ℝ)+1))*(((l : ℝ)+1)/(2*R)) := by field_simp
        _ ≤ (2*R/((l : ℝ)+1))*(regularD l R/regular l R) :=
          mul_le_mul_of_nonneg_left hq (by positivity)
        _ =(2*R/((l : ℝ)+1))*(1/regular l R)*regularD l R := by field_simp
    calc regular l s*‖(sourceState l gs R X hR x).1‖
        ≤ regular l s*((2*R/((l : ℝ)+1))*(1/regular l R)) := mul_le_mul_of_nonneg_left h1 hs0
      _ =(2*R/((l : ℝ)+1))*(regular l s*(1/regular l R)) := by ring
      _ ≤ (2*R/((l : ℝ)+1))*(Real.exp (R/2)*(s/R)^(l+1)) :=
          mul_le_mul_of_nonneg_left hfinal (by positivity)
      _ =2*R*Real.exp (R/2)/((l : ℝ)+1)*(s/R)^(l+1) := by ring
  · calc regular l s*‖(sourceState l gs R X hR x).2‖ ≤ regular l s*(1/regular l R) :=
          mul_le_mul_of_nonneg_left (hmom.trans hmax) hs0
      _ ≤ _ := hfinal


theorem amplitude_sq_le_gamma (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0<R) (hX : 0<X) :
    (‖(coefficients l gs R X hR).2‖⁻¹)^2 ≤ ‖gamma l gs R X hR‖ := by
  have him := gamma_im l gs R X hR hX
  have hβ := coefficients_second_ne_zero l gs R X hR hX
  have hsq : (‖(coefficients l gs R X hR).2‖⁻¹)^2=-(gamma l gs R X hR).im := by
    rw [him,inv_pow,← Complex.normSq_eq_norm_sq]
    have : 0 < Complex.normSq (coefficients l gs R X hR).2 := Complex.normSq_pos.mpr hβ
    field_simp
  rw [hsq]
  have h := Complex.abs_im_le_norm (gamma l gs R X hR)
  exact (neg_le_abs _).trans h

/-- Exterior source-state bound in the low-degree (propagating) range, uniform in the shell radius,
the degree and the exterior radius. -/
theorem low_exterior_state_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (M d : ℝ)
    (hM : 0 ≤ M) (hR : 0<R) (hd : X-R ≤ d) (hl : 2*((l : ℝ)+1) ≤ R)
    (hp : ∀ g ∈ gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (x : ℝ) (hx : X<x) :
    ‖(sourceState l gs R X hR x).1‖^2 ≤ OQ14.RadialLowTail.bound M d*(2/(1-(1/2 : ℝ)^2)) ∧
    ‖(sourceState l gs R X hR x).2‖^2 ≤ OQ14.RadialLowTail.bound M d*2 := by
  have hRX := chain_ordered h
  have hX : 0<X := hR.trans_le hRX
  have hγ := OQ14.RadialLowTail.actual_gamma_low_bound l h M d hM hR hd hl hp
  have hA := (amplitude_sq_le_gamma l gs R X hR hX).trans hγ
  have hb := OQ14.HankelEnergy.low_range_normSq_bounds l (1/2) R x (by norm_num) hR
    (hRX.trans hx.le) (OQ14.RadialMiddleTail.low_degree_barrier l R hR.le hl)
  have hB0 : 0 ≤ OQ14.RadialLowTail.bound M d := by
    unfold OQ14.RadialLowTail.bound; positivity
  rw [sourceState_exterior l h hR x hx]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,norm_mul,norm_inv]
  change (‖(coefficients l gs R X hR).2‖⁻¹*‖xi l x‖)^2 ≤ _ ∧
    (‖(coefficients l gs R X hR).2‖⁻¹*‖xiD l x‖)^2 ≤ _
  rw [mul_pow,mul_pow,← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  constructor
  · exact mul_le_mul hA hb.2 (Complex.normSq_nonneg _) hB0
  · exact mul_le_mul hA hb.1 (Complex.normSq_nonneg _) hB0


/-- Exterior source-state bound in the intermediate degree window `l <= 2 q R`, for a stack of
bounded thickness and coefficients; the bound does not depend on the degree. -/
theorem middle_exterior_state_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (q M d : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 1 ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hl : (l : ℝ) ≤ 2*q*R) (hp : ∀ g ∈ gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (x : ℝ) (hx : X<x) :
    ‖(sourceState l gs R X (zero_lt_one.trans_le hR) x).1‖^2 ≤
      ((OQ14.RadialIntermediateBound.frameConstant q)^2*
        Real.exp (4*OQ14.HankelIntermediateBounds.exponent q*R+
          (2*M+OQ14.RadialIntermediateBound.angularBound q)*d))*
        (Real.exp (OQ14.HankelIntermediateBounds.exponent q*R))^2 ∧
    ‖(sourceState l gs R X (zero_lt_one.trans_le hR) x).2‖^2 ≤
      ((OQ14.RadialIntermediateBound.frameConstant q)^2*
        Real.exp (4*OQ14.HankelIntermediateBounds.exponent q*R+
          (2*M+OQ14.RadialIntermediateBound.angularBound q)*d))*
        ((1+2*q)*Real.exp (OQ14.HankelIntermediateBounds.exponent q*R))^2 := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hRX := chain_ordered h
  have hXp : 0<X := hRp.trans_le hRX
  have hγ := OQ14.RadialIntermediateBound.actual_gamma_window_bound l h q M d hq hM hR hX hd hl hp
  have hA := (amplitude_sq_le_gamma l gs R X hRp hXp).trans hγ
  have hxi : ‖xi l x‖ ≤ Real.exp (OQ14.HankelIntermediateBounds.exponent q*R) :=
    (norm_xi_antitone l hXp hx.le).trans
      (OQ14.HankelIntermediateBounds.xi_intermediate_bound l q R X hq hRp hRX hX hl)
  have hxiD : ‖xiD l x‖ ≤ (1+2*q)*Real.exp (OQ14.HankelIntermediateBounds.exponent q*R) := by
    refine (norm_xiD_le_max l hXp hx.le).trans (max_le ?_ ?_)
    · exact OQ14.HankelIntermediateBounds.xiD_intermediate_bound l q R X hq hRp hRX hX hl
    · have he : 1 ≤ Real.exp (OQ14.HankelIntermediateBounds.exponent q*R) := by
        apply Real.one_le_exp
        exact mul_nonneg (OQ14.RadialMiddleTail.exponent_nonnegative q hq) hRp.le
      nlinarith
  rw [sourceState_exterior l h hRp x hx]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,norm_mul,norm_inv]
  change (‖(coefficients l gs R X hRp).2‖⁻¹*‖xi l x‖)^2 ≤ _ ∧
    (‖(coefficients l gs R X hRp).2‖⁻¹*‖xiD l x‖)^2 ≤ _
  rw [mul_pow,mul_pow]
  have hG : 0 ≤ (OQ14.RadialIntermediateBound.frameConstant q)^2*
        Real.exp (4*OQ14.HankelIntermediateBounds.exponent q*R+
          (2*M+OQ14.RadialIntermediateBound.angularBound q)*d) := by positivity
  constructor
  · exact mul_le_mul hA (pow_le_pow_left₀ (norm_nonneg _) hxi 2) (sq_nonneg _) hG
  · exact mul_le_mul hA (pow_le_pow_left₀ (norm_nonneg _) hxiD 2) (sq_nonneg _) hG

/-- The same in terms of the cutoff `2 q R <= l` for a stack with parameters bounded by `q`. -/
theorem exterior_state_bound_high (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (hR : 0<R) (q : ℝ) (hq : 1 ≤ q) (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs,g.q ≤ q)
    (hl : 2*q*R ≤ l) (x : ℝ) (hx : X<x) :
    ‖(sourceState l gs R X hR x).1‖ ≤ 1/regularD l R :=
  exterior_state_bound l h hR
    (OQ14.RadialStackHighTail.common_stack_barrier l h q hq hR hX hparams hl)
    (OQ14.RadialHighOrderBound.high_order_barrier l R hR
      (OQ14.RadialStackHighTail.cutoff_covers_high_range q R hq hR.le l hl)) x hx


theorem exterior_momentum_bound_high (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (hR : 0<R) (q : ℝ) (hq : 1 ≤ q) (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs,g.q ≤ q)
    (hl : 2*q*R ≤ l) (x : ℝ) (hx : X<x) :
    ‖(sourceState l gs R X hR x).2‖ ≤
      max (1/regular l R) (Real.sqrt (1/(regular l R*regularD l R))) :=
  exterior_momentum_bound l h hR
    (OQ14.RadialStackHighTail.common_stack_barrier l h q hq hR hX hparams hl)
    (OQ14.RadialHighOrderBound.high_order_barrier l R hR
      (OQ14.RadialStackHighTail.cutoff_covers_high_range q R hq hR.le l hl)) x hx


theorem source_weighted_exterior_high (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (hR : 0<R) (q : ℝ) (hq : 1 ≤ q) (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs,g.q ≤ q)
    (hl : 2*q*R ≤ l) (s : ℝ) (hs : 0<s) (hsR : s ≤ R) (x : ℝ) (hx : X<x) :
    regular l s*‖(sourceState l gs R X hR x).1‖ ≤
      2*R*Real.exp (R/2)/((l : ℝ)+1)*(s/R)^(l+1) ∧
    regular l s*‖(sourceState l gs R X hR x).2‖ ≤ Real.exp (R/2)*(s/R)^(l+1) :=
  source_weighted_exterior l h hR
    (OQ14.RadialStackHighTail.common_stack_barrier l h q hq hR hX hparams hl)
    (OQ14.RadialStackHighTail.cutoff_covers_high_range q R hq hR.le l hl) s hs hsR x hx

end OQ14.BarrierSourceStateBounds
#print axioms OQ14.BarrierSourceStateBounds.wronskian_load_bound
#print axioms OQ14.BarrierSourceStateBounds.norm_le_of_sq_le
#print axioms OQ14.BarrierSourceStateBounds.radialLoad_smul
#print axioms OQ14.BarrierSourceStateBounds.core_load_nonpos
#print axioms OQ14.BarrierSourceStateBounds.endpoint_state_bound
#print axioms OQ14.BarrierSourceStateBounds.back_normSq_ge
#print axioms OQ14.BarrierSourceStateBounds.traverse_normSq_ge
#print axioms OQ14.BarrierSourceStateBounds.norm_xi_antitone
#print axioms OQ14.BarrierSourceStateBounds.back_normSq_ge_momentum
#print axioms OQ14.BarrierSourceStateBounds.traverse_normSq_ge_momentum
#print axioms OQ14.BarrierSourceStateBounds.normSq_xiD_hasDerivAt
#print axioms OQ14.BarrierSourceStateBounds.weight_mono
#print axioms OQ14.BarrierSourceStateBounds.normSq_xiD_le_max
#print axioms OQ14.BarrierSourceStateBounds.norm_xiD_le_max
#print axioms OQ14.BarrierSourceStateBounds.exterior_state_bound
#print axioms OQ14.BarrierSourceStateBounds.exterior_endpoint_norms
#print axioms OQ14.BarrierSourceStateBounds.beta_inv_sq_le
#print axioms OQ14.BarrierSourceStateBounds.exterior_momentum_bound
#print axioms OQ14.BarrierSourceStateBounds.regularD_lower
#print axioms OQ14.BarrierSourceStateBounds.regular_at_lower
#print axioms OQ14.BarrierSourceStateBounds.source_weighted_exterior
#print axioms OQ14.BarrierSourceStateBounds.amplitude_sq_le_gamma
#print axioms OQ14.BarrierSourceStateBounds.low_exterior_state_bound
#print axioms OQ14.BarrierSourceStateBounds.middle_exterior_state_bound
#print axioms OQ14.BarrierSourceStateBounds.exterior_state_bound_high
#print axioms OQ14.BarrierSourceStateBounds.exterior_momentum_bound_high
#print axioms OQ14.BarrierSourceStateBounds.source_weighted_exterior_high
