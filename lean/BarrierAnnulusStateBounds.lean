import BarrierSourceStateBounds

/-! Degree-uniform bounds of the actual source state inside the stack annulus `[R, X]`, by induction
over the layer list: in the barrier range the squared moduli of both components of the glued profile
are bounded by their values at the inner radius (so the geometric source-weighted bound of the
exterior carries over), and in the low and intermediate degree ranges the energy of the profile is
bounded layer by layer. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.BarrierAnnulusStateBounds
open Set OQ14.RadialGreen OQ14.RadialStack OQ14.RadialLayer OQ14.RadialPropagation
open OQ14.RadialSource OQ14.RadialGluing OQ14.HankelRealBasis OQ14.HankelEnergy OQ14.ModalAlgebra
open OQ14.BarrierSourceStateBounds

/-- On the annulus the source state is the amplitude times the glued profile of the outgoing state. -/
theorem sourceState_annulus (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (x : ℝ) (hx : x ∈ Icc R X) :
    sourceState l gs R X hR x=((coefficients l gs R X hR).2)⁻¹ • profile l gs (outgoing l X) x := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  rcases eq_or_lt_of_le hx.1 with hxR | hxR
  · rw [← hxR]
    rw [sourceState_core l gs R X hR R le_rfl,profile_inner l h]
    obtain ⟨h1,h2⟩ := coreWave_boundary l gs R X hR hX
    apply Prod.ext
    · simp only [Prod.smul_fst,smul_eq_mul]
      rw [h1,div_eq_inv_mul]
    · simp only [Prod.smul_snd,smul_eq_mul]
      rw [h2,div_eq_inv_mul]
  · unfold sourceState
    rw [if_neg (not_le.mpr hxR)]
    unfold outerMatched
    rw [if_pos hx.2]

/-- Barrier range: the glued profile has first and second components of no larger squared modulus
than the traversed state at the inner radius. -/
theorem profile_normSq_le_traverse (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (s : State) (hs : radialLoad s.1 s.2 ≤ 0)
    (x : ℝ) (hx : x ∈ Icc R X) :
    Complex.normSq (profile l gs s x).1 ≤ Complex.normSq (traverse l gs s).1 ∧
    Complex.normSq (profile l gs s x).2 ≤ Complex.normSq (traverse l gs s).2 := by
  induction h generalizing s x with
  | nil R =>
    exact ⟨le_rfl,le_rfl⟩
  | cons g gs R h ih =>
    have hg := hbarrier g List.mem_cons_self
    have hb' : ∀ y ∈ gs,y.q^2*y.b^2 ≤ angular l := fun y hy => hbarrier y (List.mem_cons_of_mem _ hy)
    have hback := back_load l g s hg hs
    by_cases hx1 : g.a<x
    · simp only [profile,if_pos hx1]
      have hout : radialLoad (wave l g s g.b) (waveMomentum l g s g.b) ≤ 0 := by
        rwa [(wave_outer l g s).1,(wave_outer l g s).2]
      obtain ⟨_,hu,hp⟩ := actual_layer_barrier l g.q g.σ
        (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
        g.a g.b g.q_pos.ne' g.σ_pos g.a_pos g.ordered hg hout
      have hxm : x ∈ Icc g.a g.b := ⟨hx1.le,hx.2⟩
      have ha : g.a ∈ Icc g.a g.b := ⟨le_rfl,g.ordered⟩
      have h1 : Complex.normSq (wave l g s x) ≤ Complex.normSq (wave l g s g.a) := hu ha hxm hx1.le
      have h2 : Complex.normSq (waveMomentum l g s x) ≤ Complex.normSq (waveMomentum l g s g.a) :=
        hp ha hxm hx1.le
      rw [(wave_inner l g s).1] at h1
      rw [(wave_inner l g s).2] at h2
      have t1 := traverse_normSq_ge l gs (back l g s) hb' hback
      have t2 := traverse_normSq_ge_momentum l gs (back l g s) hb' hback
      exact ⟨h1.trans t1,h2.trans t2⟩
    · simp only [profile,if_neg hx1]
      exact ih hb' (back l g s) hback x ⟨hx.1,not_lt.mp hx1⟩

/-- Annulus state bound in the barrier range, at every radius of the stack. -/
theorem annulus_state_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hν : R^2<OQ14.RiccatiBarrier.ν l)
    (x : ℝ) (hx : x ∈ Icc R X) :
    ‖(sourceState l gs R X hR x).1‖ ≤ 1/regularD l R ∧
      ‖(sourceState l gs R X hR x).2‖ ≤ 1/regular l R := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  have hs0 : radialLoad (outgoing l X).1 (outgoing l X).2 ≤ 0 :=
    OQ14.HankelPositive.outgoing_radialLoad_nonpositive l X hX
  obtain ⟨p1,p2⟩ := profile_normSq_le_traverse l h hbarrier (outgoing l X) hs0 x hx
  obtain ⟨hcw1,hcw2⟩ := endpoint_state_bound l gs R X hR hX hbarrier hν
  obtain ⟨hb1,hb2⟩ := coreWave_boundary l gs R X hR hX
  set β := (coefficients l gs R X hR).2
  set s := traverse l gs (outgoing l X)
  have hn1 : ‖coreWave l gs R X hR R‖=‖β‖⁻¹*‖s.1‖ := by rw [hb1,norm_div,div_eq_inv_mul]
  have hn2 : ‖coreWaveD l gs R X hR R‖=‖β‖⁻¹*‖s.2‖ := by rw [hb2,norm_div,div_eq_inv_mul]
  have hi : (0 : ℝ) ≤ ‖β‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have q1 : ‖(profile l gs (outgoing l X) x).1‖ ≤ ‖s.1‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    exact p1
  have q2 : ‖(profile l gs (outgoing l X) x).2‖ ≤ ‖s.2‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
    exact p2
  rw [sourceState_annulus l h hR x hx]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,norm_mul,norm_inv]
  constructor
  · calc ‖β‖⁻¹*‖(profile l gs (outgoing l X) x).1‖ ≤ ‖β‖⁻¹*‖s.1‖ :=
          mul_le_mul_of_nonneg_left q1 hi
      _ =‖coreWave l gs R X hR R‖ := hn1.symm
      _ ≤ 1/regularD l R := hcw1
  · calc ‖β‖⁻¹*‖(profile l gs (outgoing l X) x).2‖ ≤ ‖β‖⁻¹*‖s.2‖ :=
          mul_le_mul_of_nonneg_left q2 hi
      _ =‖coreWaveD l gs R X hR R‖ := hn2.symm
      _ ≤ 1/regular l R := hcw2

/-- Source-weighted geometric bound on the annulus in the barrier/high range. -/
theorem source_weighted_annulus (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (hbarrier : ∀ g ∈ gs,g.q^2*g.b^2 ≤ angular l) (hl : 2*R ≤ l) (s : ℝ) (hs : 0<s) (hsR : s ≤ R)
    (x : ℝ) (hx : x ∈ Icc R X) :
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
  have hl1 : (0 : ℝ)<(l : ℝ)+1 := by positivity
  have hpos0 : 0<regular l R := hp
  have hsR' : (s/R)^(l+1)=s^(l+1)/R^(l+1) := div_pow _ _ _
  obtain ⟨hu,hmom⟩ := annulus_state_bound l h hR hbarrier hν x hx
  have hs0 : 0 ≤ regular l s := by
    have := OQ14.RiccatiGaussianBound.regular_gaussian_lower l R hR hν s ⟨hs,hsR⟩
    exact le_trans (by positivity) this
  have hinv : 1/regular l R ≤ Real.exp (R/2)/(A*R^(l+1)) := by
    rw [div_le_div_iff₀ hpos0 (by positivity)]
    have : Real.exp (R/2)*(A*R^(l+1)*Real.exp (-R/2))=A*R^(l+1) := by
      rw [mul_comm (A*R^(l+1)) (Real.exp (-R/2)),← mul_assoc,← Real.exp_add]
      have : R/2+-R/2=0 := by ring
      rw [this,Real.exp_zero,one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hlow (Real.exp_pos (R/2)).le]
  have hfinal : regular l s*(1/regular l R) ≤ Real.exp (R/2)*(s/R)^(l+1) := by
    calc regular l s*(1/regular l R) ≤ (A*s^(l+1))*(Real.exp (R/2)/(A*R^(l+1))) :=
          mul_le_mul hsup hinv (by positivity) (by positivity)
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
          mul_le_mul_of_nonneg_left hmom hs0
      _ ≤ _ := hfinal

theorem source_weighted_annulus_high (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (hR : 0<R) (q : ℝ) (hq : 1 ≤ q) (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs,g.q ≤ q)
    (hl : 2*q*R ≤ l) (s : ℝ) (hs : 0<s) (hsR : s ≤ R) (x : ℝ) (hx : x ∈ Icc R X) :
    regular l s*‖(sourceState l gs R X hR x).1‖ ≤
      2*R*Real.exp (R/2)/((l : ℝ)+1)*(s/R)^(l+1) ∧
    regular l s*‖(sourceState l gs R X hR x).2‖ ≤ Real.exp (R/2)*(s/R)^(l+1) :=
  source_weighted_annulus l h hR
    (OQ14.RadialStackHighTail.common_stack_barrier l h q hq hR hX hparams hl)
    (OQ14.RadialStackHighTail.cutoff_covers_high_range q R hq hR.le l hl) s hs hsR x hx

/-- In the barrier/high range the source-weighted bound holds at every radius `x >= R`. -/
theorem source_weighted_all_high (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (hR : 0<R) (q : ℝ) (hq : 1 ≤ q) (hX : X ≤ 2*R) (hparams : ∀ g ∈ gs,g.q ≤ q)
    (hl : 2*q*R ≤ l) (s : ℝ) (hs : 0<s) (hsR : s ≤ R) (x : ℝ) (hx : R ≤ x) :
    regular l s*‖(sourceState l gs R X hR x).1‖ ≤
      2*R*Real.exp (R/2)/((l : ℝ)+1)*(s/R)^(l+1) ∧
    regular l s*‖(sourceState l gs R X hR x).2‖ ≤ Real.exp (R/2)*(s/R)^(l+1) := by
  by_cases hxX : x ≤ X
  · exact source_weighted_annulus_high l h hR q hq hX hparams hl s hs hsR x ⟨hx,hxX⟩
  · exact source_weighted_exterior_high l h hR q hq hX hparams hl s hs hsR x (not_le.mp hxX)

/-! ### Non-barrier degree ranges: layerwise energy propagation -/

theorem energy_smul (c u p : ℂ) :
    OQ14.RadialPropagation.energy (c*u) (c*p)=Complex.normSq c*OQ14.RadialPropagation.energy u p := by
  unfold OQ14.RadialPropagation.energy
  rw [map_mul,map_mul]
  ring

/-- Energy of the glued profile along the stack, layer by layer. -/
theorem profile_energy_le (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R) (M A : ℝ)
    (hR : 0<R) (hA : 0 ≤ A) (hν : angular l ≤ A*R^2)
    (hparams : ∀ g ∈ gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (s : State) (x : ℝ) (hx : x ∈ Icc R X) :
    energy (profile l gs s x).1 (profile l gs s x).2 ≤
      Real.exp ((2*M+A)*(X-x))*energy s.1 s.2 := by
  induction h generalizing s x with
  | nil R =>
    simp only [profile]
    have hx' : x=R := le_antisymm hx.2 hx.1
    subst hx'
    simp
  | cons g gs R h ih =>
    have hp := hparams g List.mem_cons_self
    have hp' : ∀ y ∈ gs,1 ≤ y.σ ∧ y.σ ≤ M ∧ y.q^2 ≤ M :=
      fun y hy => hparams y (List.mem_cons_of_mem _ hy)
    have hRa : R ≤ g.a := chain_ordered h
    by_cases hx1 : g.a<x
    · simp only [profile,if_pos hx1]
      have hx0 : 0<x := hR.trans_le hx.1
      have hbd := (actual_layer_energy_bound l g.q g.σ
        (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
        x g.b g.q_pos.ne' g.σ_pos hx0 hx.2).2
      have hgen := generator_uniform_bound l g.q g.σ R x M A hR hx.1 hp.1 hp.2.1 hp.2.2 hA hν
      change energy (wave l g s x) (waveMomentum l g s x) ≤
        Real.exp (generatorBound l g.q g.σ x*(g.b-x))*
          energy (wave l g s g.b) (waveMomentum l g s g.b) at hbd
      rw [(wave_outer l g s).1,(wave_outer l g s).2] at hbd
      refine hbd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (energy_nonnegative _ _))
      exact mul_le_mul_of_nonneg_right hgen (sub_nonneg.mpr hx.2)
    · simp only [profile,if_neg hx1]
      have hih := ih hR hν hp' (back l g s) x ⟨hx.1,not_lt.mp hx1⟩
      have hbk := back_energy l g s
      have hgen := generator_uniform_bound l g.q g.σ R g.a M A hR hRa hp.1 hp.2.1 hp.2.2 hA hν
      have hcost : cost l g ≤ (2*M+A)*(g.b-g.a) :=
        mul_le_mul_of_nonneg_right hgen (sub_nonneg.mpr g.ordered)
      have h1 : energy (back l g s).1 (back l g s).2 ≤
          Real.exp ((2*M+A)*(g.b-g.a))*energy s.1 s.2 :=
        hbk.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) (energy_nonnegative _ _))
      have hex : 0 ≤ Real.exp ((2*M+A)*(g.a-x)) := (Real.exp_pos _).le
      calc energy (profile l gs (back l g s) x).1 (profile l gs (back l g s) x).2
          ≤ Real.exp ((2*M+A)*(g.a-x))*energy (back l g s).1 (back l g s).2 := hih
        _ ≤ Real.exp ((2*M+A)*(g.a-x))*(Real.exp ((2*M+A)*(g.b-g.a))*energy s.1 s.2) :=
          mul_le_mul_of_nonneg_left h1 hex
        _ =Real.exp ((2*M+A)*(g.b-x))*energy s.1 s.2 := by
          rw [← mul_assoc,← Real.exp_add]
          congr 2
          ring

/-- Energy of the annulus source state in terms of `|gamma|` and the outer outgoing energy. -/
theorem annulus_energy_le (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (hR : 0<R)
    (M A d : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hd : X-R ≤ d) (hν : angular l ≤ A*R^2)
    (hparams : ∀ g ∈ gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (x : ℝ) (hx : x ∈ Icc R X) :
    ‖(sourceState l gs R X hR x).1‖^2+‖(sourceState l gs R X hR x).2‖^2 ≤
      ‖gamma l gs R X hR‖*(Real.exp ((2*M+A)*d)*(Complex.normSq (xi l X)+Complex.normSq (xiD l X))) := by
  have hX : 0<X := hR.trans_le (chain_ordered h)
  have hE := profile_energy_le l h M A hR hA hν hparams (outgoing l X) x hx
  have hγ := amplitude_sq_le_gamma l gs R X hR hX
  rw [sourceState_annulus l h hR x hx]
  simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  rw [← Complex.normSq_eq_norm_sq,← Complex.normSq_eq_norm_sq]
  have he := energy_smul ((coefficients l gs R X hR).2)⁻¹ (profile l gs (outgoing l X) x).1
    (profile l gs (outgoing l X) x).2
  unfold OQ14.RadialPropagation.energy at he
  rw [he]
  have hnorm : Complex.normSq ((coefficients l gs R X hR).2)⁻¹=
      (‖(coefficients l gs R X hR).2‖⁻¹)^2 := by
    rw [Complex.normSq_eq_norm_sq,norm_inv]
  rw [hnorm]
  have hexp : Real.exp ((2*M+A)*(X-x)) ≤ Real.exp ((2*M+A)*d) := by
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith [hx.1]
  have hout : energy (outgoing l X).1 (outgoing l X).2=Complex.normSq (xi l X)+Complex.normSq (xiD l X) := rfl
  have h1 : energy (profile l gs (outgoing l X) x).1 (profile l gs (outgoing l X) x).2 ≤
      Real.exp ((2*M+A)*d)*(Complex.normSq (xi l X)+Complex.normSq (xiD l X)) := by
    refine hE.trans ?_
    rw [hout]
    exact mul_le_mul_of_nonneg_right hexp (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
  unfold OQ14.RadialPropagation.energy at h1
  exact mul_le_mul hγ h1 (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (norm_nonneg _)

/-- Low-degree annulus bound. -/
theorem low_annulus_state_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R) (M d : ℝ)
    (hM : 0 ≤ M) (hR : 0<R) (hd : X-R ≤ d) (hl : 2*((l : ℝ)+1) ≤ R)
    (hp : ∀ g ∈ gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M) (x : ℝ) (hx : x ∈ Icc R X) :
    ‖(sourceState l gs R X hR x).1‖^2+‖(sourceState l gs R X hR x).2‖^2 ≤
      OQ14.RadialLowTail.bound M d*(Real.exp ((2*M+(1/2 : ℝ)^2)*d)*
        (2/(1-(1/2 : ℝ)^2)+2)) := by
  have hRX := chain_ordered h
  have hν := OQ14.RadialMiddleTail.low_degree_barrier l R hR.le hl
  have hA : 0 ≤ (1/2 : ℝ)^2 := by positivity
  have hγ := OQ14.RadialLowTail.actual_gamma_low_bound l h M d hM hR hd hl hp
  have hE := annulus_energy_le l h hR M ((1/2 : ℝ)^2) d hA hM hd hν hp x hx
  have hb := OQ14.HankelEnergy.low_range_normSq_bounds l (1/2) R X (by norm_num) hR hRX hν
  have hexp : 0 ≤ Real.exp ((2*M+(1/2 : ℝ)^2)*d) := (Real.exp_pos _).le
  refine hE.trans ?_
  have hsum : Complex.normSq (xi l X)+Complex.normSq (xiD l X) ≤ 2/(1-(1/2 : ℝ)^2)+2 := by
    linarith [hb.1,hb.2]
  have hnn : 0 ≤ Complex.normSq (xi l X)+Complex.normSq (xiD l X) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  exact mul_le_mul hγ (mul_le_mul_of_nonneg_left hsum hexp) (by positivity)
    (by unfold OQ14.RadialLowTail.bound; positivity)

/-- Intermediate-window annulus bound. -/
theorem middle_annulus_state_bound (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (q M d : ℝ) (hq : 1 ≤ q) (hM : 0 ≤ M) (hR : 1 ≤ R) (hX : X ≤ 2*R) (hd : X-R ≤ d)
    (hl : (l : ℝ) ≤ 2*q*R) (hp : ∀ g ∈ gs,1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q^2 ≤ M)
    (x : ℝ) (hx : x ∈ Icc R X) :
    ‖(sourceState l gs R X (zero_lt_one.trans_le hR) x).1‖^2+
      ‖(sourceState l gs R X (zero_lt_one.trans_le hR) x).2‖^2 ≤
      ((OQ14.RadialIntermediateBound.frameConstant q)^2*
        Real.exp (4*OQ14.HankelIntermediateBounds.exponent q*R+
          (2*M+OQ14.RadialIntermediateBound.angularBound q)*d))*
      (Real.exp ((2*M+OQ14.RadialIntermediateBound.angularBound q)*d)*
        ((Real.exp (OQ14.HankelIntermediateBounds.exponent q*R))^2+
          ((1+2*q)*Real.exp (OQ14.HankelIntermediateBounds.exponent q*R))^2)) := by
  have hRp : 0<R := zero_lt_one.trans_le hR
  have hRX := chain_ordered h
  have hXp : 0<X := hRp.trans_le hRX
  have hA : 0 ≤ OQ14.RadialIntermediateBound.angularBound q := by
    unfold OQ14.RadialIntermediateBound.angularBound; positivity
  have hν := OQ14.RadialIntermediateBound.window_angular_bound l q R hq hR hl
  have hγ := OQ14.RadialIntermediateBound.actual_gamma_window_bound l h q M d hq hM hR hX hd hl hp
  have hE := annulus_energy_le l h hRp M (OQ14.RadialIntermediateBound.angularBound q) d hA hM hd hν hp x hx
  have hxi := OQ14.HankelIntermediateBounds.xi_intermediate_bound l q R X hq hRp hRX hX hl
  have hxiD := OQ14.HankelIntermediateBounds.xiD_intermediate_bound l q R X hq hRp hRX hX hl
  have hexp : 0 ≤ Real.exp ((2*M+OQ14.RadialIntermediateBound.angularBound q)*d) := (Real.exp_pos _).le
  refine hE.trans ?_
  have h1 : Complex.normSq (xi l X) ≤ (Real.exp (OQ14.HankelIntermediateBounds.exponent q*R))^2 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hxi 2
  have h2 : Complex.normSq (xiD l X) ≤
      ((1+2*q)*Real.exp (OQ14.HankelIntermediateBounds.exponent q*R))^2 := by
    rw [Complex.normSq_eq_norm_sq]; exact pow_le_pow_left₀ (norm_nonneg _) hxiD 2
  have hsum := add_le_add h1 h2
  have hG : 0 ≤ (OQ14.RadialIntermediateBound.frameConstant q)^2*
        Real.exp (4*OQ14.HankelIntermediateBounds.exponent q*R+
          (2*M+OQ14.RadialIntermediateBound.angularBound q)*d) := by positivity
  exact mul_le_mul hγ (mul_le_mul_of_nonneg_left hsum hexp)
    (mul_nonneg hexp (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))) hG

end OQ14.BarrierAnnulusStateBounds
#print axioms OQ14.BarrierAnnulusStateBounds.sourceState_annulus
#print axioms OQ14.BarrierAnnulusStateBounds.profile_normSq_le_traverse
#print axioms OQ14.BarrierAnnulusStateBounds.annulus_state_bound
#print axioms OQ14.BarrierAnnulusStateBounds.source_weighted_annulus
#print axioms OQ14.BarrierAnnulusStateBounds.source_weighted_annulus_high
#print axioms OQ14.BarrierAnnulusStateBounds.source_weighted_all_high
#print axioms OQ14.BarrierAnnulusStateBounds.energy_smul
#print axioms OQ14.BarrierAnnulusStateBounds.profile_energy_le
#print axioms OQ14.BarrierAnnulusStateBounds.annulus_energy_le
#print axioms OQ14.BarrierAnnulusStateBounds.low_annulus_state_bound
#print axioms OQ14.BarrierAnnulusStateBounds.middle_annulus_state_bound
