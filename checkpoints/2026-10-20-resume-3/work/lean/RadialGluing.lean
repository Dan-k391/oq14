import RadialLoadBounds
import Mathlib.Topology.Piecewise

/-! A genuine continuous radial state through all interfaces of an explicit
finite chain. The auxiliary profile extends the endpoint layers; sourceState
attaches the normalized vacuum core and outgoing exterior with proved
continuity and actual radial equations. Spatial Maxwell reconstruction is
a separate result. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.RadialGluing

open Set Filter OQ14.RadialStack OQ14.RadialLayer OQ14.RadialPropagation
open scoped Topology

def profile (l : ℕ) : List Layer → State → ℝ → State
  | [], s, _ => s
  | g::gs, s, x => if g.a < x then (wave l g s x,waveMomentum l g s x)
      else profile l gs (back l g s) x

def sigmaAt : List Layer → ℝ → ℝ
  | [], _ => 0
  | g::gs, x => if g.a < x then g.σ else sigmaAt gs x

def potentialAt (l : ℕ) : List Layer → ℝ → ℝ
  | [], _ => 0
  | g::gs, x => if g.a < x then potential l g.q g.σ x else potentialAt l gs x

def cuts (gs : List Layer) : List ℝ := gs.map Layer.a

theorem wave_state_inner (l : ℕ) (g : Layer) (s : State) :
    (wave l g s g.a,waveMomentum l g s g.a) = back l g s :=
  Prod.ext (wave_inner l g s).1 (wave_inner l g s).2

theorem wave_state_outer (l : ℕ) (g : Layer) (s : State) :
    (wave l g s g.b,waveMomentum l g s g.b) = s :=
  Prod.ext (wave_outer l g s).1 (wave_outer l g s).2

theorem back_zero_width (l : ℕ) (g : Layer) (s : State) (hg : g.a=g.b) : back l g s = s := by
  rw [←wave_state_inner, hg, wave_state_outer]

theorem profile_outer (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R) (s : State) :
    profile l gs s X = s := by
  induction h generalizing s with
  | nil R => rfl
  | cons g gs R h ih =>
    by_cases hg : g.a < g.b
    · simpa only [profile,if_pos hg] using wave_state_outer l g s
    · have he : g.a=g.b := le_antisymm g.ordered (not_lt.mp hg)
      simp only [profile,if_neg hg]
      rw [←he,ih,back_zero_width l g s he]

theorem profile_inner (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R) (s : State) :
    profile l gs s R = traverse l gs s := by
  induction h generalizing s with
  | nil R => rfl
  | cons g gs R h ih =>
    simp only [profile,if_neg (not_lt.mpr (chain_ordered h)),RadialStack.traverse,ih]

theorem wave_state_continuousOn (l : ℕ) (g : Layer) (s : State) :
    ContinuousOn (fun x => (wave l g s x,waveMomentum l g s x)) (Ici g.a) := by
  intro x hx
  have hp : 0 < x := g.a_pos.trans_le hx
  obtain ⟨hu,hp⟩ := solution_ode l g.q g.σ
    (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
    x g.q_pos.ne' g.σ_pos.ne' hp.ne'
  exact (hu.continuousAt.prodMk hp.continuousAt).continuousWithinAt

theorem profile_continuous (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R) (s : State) :
    Continuous (profile l gs s) := by
  induction h generalizing s with
  | nil R => exact continuous_const
  | cons g gs R h ih =>
    apply continuous_if
    · intro x hx
      have hxg : x=g.a := by
        simpa only [show {x : ℝ | g.a < x}=Ioi g.a from rfl,frontier_Ioi,mem_singleton_iff] using hx
      subst x
      rw [profile_outer l h, wave_state_inner]
    · simpa only [show {x : ℝ | g.a < x}=Ioi g.a from rfl,closure_Ioi] using
        wave_state_continuousOn l g s
    · exact (ih (back l g s)).continuousOn

theorem profile_hasDerivAt (l : ℕ) (gs : List Layer) (s : State) (x : ℝ)
    (hx : x ∉ cuts gs) :
    HasDerivAt (fun t => (profile l gs s t).1) ((sigmaAt gs x : ℂ)*(profile l gs s x).2) x ∧
    HasDerivAt (fun t => (profile l gs s t).2) ((potentialAt l gs x : ℂ)*(profile l gs s x).1) x := by
  induction gs generalizing s with
  | nil => simpa [profile,sigmaAt,potentialAt] using
      And.intro (hasDerivAt_const x s.1) (hasDerivAt_const x s.2)
  | cons g gs ih =>
    have hne : x ≠ g.a := by
      intro he
      apply hx
      simp [cuts,he]
    have htail : x ∉ cuts gs := by
      intro hm
      exact hx (List.mem_cons_of_mem _ hm)
    rcases lt_or_gt_of_ne hne with hl|hr
    · have he : profile l (g::gs) s =ᶠ[𝓝 x] profile l gs (back l g s) := by
        filter_upwards [Iio_mem_nhds hl] with t ht
        exact if_neg (not_lt.mpr ht.le)
      obtain ⟨hu,hp⟩ := ih (back l g s) htail
      have he1 : (fun t => (profile l (g::gs) s t).1) =ᶠ[𝓝 x]
          (fun t => (profile l gs (back l g s) t).1) := he.mono (fun _ ht => congrArg Prod.fst ht)
      have he2 : (fun t => (profile l (g::gs) s t).2) =ᶠ[𝓝 x]
          (fun t => (profile l gs (back l g s) t).2) := he.mono (fun _ ht => congrArg Prod.snd ht)
      simpa only [profile,sigmaAt,potentialAt,if_neg (not_lt.mpr hl.le)] using
        And.intro (hu.congr_of_eventuallyEq he1) (hp.congr_of_eventuallyEq he2)
    · have he : profile l (g::gs) s =ᶠ[𝓝 x] fun t => (wave l g s t,waveMomentum l g s t) := by
        filter_upwards [Ioi_mem_nhds hr] with t ht
        exact if_pos ht
      obtain ⟨hu,hp⟩ := solution_ode l g.q g.σ
        (initialAlpha l g.q g.σ g.b s.1 s.2) (initialBeta l g.q g.σ g.b s.1 s.2)
        x g.q_pos.ne' g.σ_pos.ne' (ne_of_gt (g.a_pos.trans hr))
      have he1 : (fun t => (profile l (g::gs) s t).1) =ᶠ[𝓝 x] wave l g s :=
        he.mono (fun _ ht => congrArg Prod.fst ht)
      have he2 : (fun t => (profile l (g::gs) s t).2) =ᶠ[𝓝 x] waveMomentum l g s :=
        he.mono (fun _ ht => congrArg Prod.snd ht)
      simpa only [profile,sigmaAt,potentialAt,if_pos hr] using
        And.intro (hu.congr_of_eventuallyEq he1) (hp.congr_of_eventuallyEq he2)


open OQ14.RadialSource OQ14.ModalAlgebra OQ14.HankelEnergy

def outerMatched (l : ℕ) (gs : List Layer) (X x : ℝ) : State :=
  if x ≤ X then profile l gs (outgoing l X) x else outgoing l x

theorem outgoing_continuousOn (l : ℕ) : ContinuousOn (outgoing l) (Ioi 0) := by
  intro x hx
  have hu := (xi_hasDerivAt l (x : ℂ) (Complex.ofReal_ne_zero.mpr hx.ne')).comp_ofReal
  have hp := (OQ14.ModalWronskian.xiD_hasDerivAt l (x : ℂ) (Complex.ofReal_ne_zero.mpr hx.ne')).comp_ofReal
  exact (hu.continuousAt.prodMk hp.continuousAt).continuousWithinAt

theorem outerMatched_continuousOn (l : ℕ) {gs : List Layer} {X R : ℝ} (h : Chain gs X R) :
    ContinuousOn (outerMatched l gs X) (Ioi 0) := by
  apply ContinuousOn.if
  · intro x hx
    have he : x=X := by simpa only [show {x : ℝ | x≤X}=Iic X from rfl,
      frontier_Iic,mem_singleton_iff] using hx.2
    subst x
    exact profile_outer l h (outgoing l X)
  · exact (profile_continuous l h (outgoing l X)).continuousOn
  · exact (outgoing_continuousOn l).mono inter_subset_left

def sourceState (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) (x : ℝ) : State :=
  if x ≤ R then (coreWave l gs R X hR x,coreWaveD l gs R X hR x)
  else ((coefficients l gs R X hR).2)⁻¹ • outerMatched l gs X x

theorem core_state_continuousOn (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R) :
    ContinuousOn (fun x => (coreWave l gs R X hR x,coreWaveD l gs R X hR x)) (Ioi 0) := by
  intro x hx
  obtain ⟨hu,hp⟩ := coreWave_ode l gs R X hR x hx.ne'
  exact (hu.continuousAt.prodMk hp.continuousAt).continuousWithinAt

theorem sourceState_continuousOn (l : ℕ) {gs : List Layer} {X R : ℝ}
    (h : Chain gs X R) (hR : 0 < R) : ContinuousOn (sourceState l gs R X hR) (Ioi 0) := by
  have hX : 0 < X := hR.trans_le (chain_ordered h)
  apply ContinuousOn.if
  · intro x hx
    have he : x=R := by simpa only [show {x : ℝ | x≤R}=Iic R from rfl,
      frontier_Iic,mem_singleton_iff] using hx.2
    subst x
    rw [outerMatched,if_pos (chain_ordered h),profile_inner l h]
    apply Prod.ext
    · simpa only [Prod.smul_fst,smul_eq_mul,div_eq_mul_inv,mul_comm] using
        (coreWave_boundary l gs R X hR hX).1
    · simpa only [Prod.smul_snd,smul_eq_mul,div_eq_mul_inv,mul_comm] using
        (coreWave_boundary l gs R X hR hX).2
  · exact (core_state_continuousOn l gs R X hR).mono inter_subset_left
  · exact (continuousOn_const.smul (outerMatched_continuousOn l h)).mono inter_subset_left

theorem sourceState_core (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : x ≤ R) :
    sourceState l gs R X hR x = (coreWave l gs R X hR x,coreWaveD l gs R X hR x) := if_pos hx

theorem sourceState_exterior (l : ℕ) {gs : List Layer} {R X : ℝ} (h : Chain gs X R)
    (hR : 0 < R) (x : ℝ) (hx : X < x) :
    sourceState l gs R X hR x = ((coefficients l gs R X hR).2)⁻¹ • outgoing l x := by
  simp only [sourceState,outerMatched,if_neg (not_le.mpr hx),
    if_neg (not_le.mpr ((chain_ordered h).trans_lt hx))]

theorem sourceState_core_ode (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : x ∈ Ioo 0 R) :
    HasDerivAt (fun t => (sourceState l gs R X hR t).1) (sourceState l gs R X hR x).2 x ∧
    HasDerivAt (fun t => (sourceState l gs R X hR t).2)
      ((-weight l x : ℂ)*(sourceState l gs R X hR x).1) x := by
  have he : sourceState l gs R X hR =ᶠ[𝓝 x]
      fun t => (coreWave l gs R X hR t,coreWaveD l gs R X hR t) := by
    filter_upwards [Iio_mem_nhds hx.2] with t ht
    exact if_pos ht.le
  obtain ⟨hu,hp⟩ := coreWave_ode l gs R X hR x hx.1.ne'
  have he1 := he.mono (fun _ ht => congrArg Prod.fst ht)
  have he2 := he.mono (fun _ ht => congrArg Prod.snd ht)
  simpa only [sourceState,if_pos hx.2.le] using
    And.intro (hu.congr_of_eventuallyEq he1) (hp.congr_of_eventuallyEq he2)

theorem sourceState_stack_ode (l : ℕ) (gs : List Layer) (R X : ℝ) (hR : 0 < R)
    (x : ℝ) (hx : x ∈ Ioo R X) (hc : x ∉ cuts gs) :
    HasDerivAt (fun t => (sourceState l gs R X hR t).1)
      ((sigmaAt gs x : ℂ)*(sourceState l gs R X hR x).2) x ∧
    HasDerivAt (fun t => (sourceState l gs R X hR t).2)
      ((potentialAt l gs x : ℂ)*(sourceState l gs R X hR x).1) x := by
  let c := ((coefficients l gs R X hR).2)⁻¹
  have he : sourceState l gs R X hR =ᶠ[𝓝 x]
      fun t => c • profile l gs (outgoing l X) t := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with t ht
    simp only [sourceState,outerMatched,if_neg (not_le.mpr ht.1),if_pos ht.2.le,c]
  obtain ⟨hu,hp⟩ := profile_hasDerivAt l gs (outgoing l X) x hc
  have he1 := he.mono (fun _ ht => congrArg Prod.fst ht)
  have he2 := he.mono (fun _ ht => congrArg Prod.snd ht)
  have h1 := (hu.const_mul c).congr_of_eventuallyEq he1
  have h2 := (hp.const_mul c).congr_of_eventuallyEq he2
  constructor
  · convert h1 using 1
    simp only [sourceState,outerMatched,if_neg (not_le.mpr hx.1),if_pos hx.2.le,
      Prod.smul_snd,smul_eq_mul,c]
    ring
  · convert h2 using 1
    simp only [sourceState,outerMatched,if_neg (not_le.mpr hx.1),if_pos hx.2.le,
      Prod.smul_fst,smul_eq_mul,c]
    ring


theorem outgoing_ode (l : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => (outgoing l t).1) (outgoing l x).2 x ∧
    HasDerivAt (fun t => (outgoing l t).2) ((-weight l x : ℂ)*(outgoing l x).1) x := by
  constructor
  · exact (xi_hasDerivAt l (x : ℂ) (Complex.ofReal_ne_zero.mpr hx.ne')).comp_ofReal
  · convert (OQ14.ModalWronskian.xiD_hasDerivAt l (x : ℂ)
      (Complex.ofReal_ne_zero.mpr hx.ne')).comp_ofReal using 1
    simp only [outgoing,weight,angular,Complex.ofReal_sub,Complex.ofReal_div,
      Complex.ofReal_pow,Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_natCast,
      Complex.ofReal_one]
    ring

theorem sourceState_exterior_ode (l : ℕ) {gs : List Layer} {R X : ℝ}
    (h : Chain gs X R) (hR : 0 < R) (x : ℝ) (hx : X < x) :
    HasDerivAt (fun t => (sourceState l gs R X hR t).1) (sourceState l gs R X hR x).2 x ∧
    HasDerivAt (fun t => (sourceState l gs R X hR t).2)
      ((-weight l x : ℂ)*(sourceState l gs R X hR x).1) x := by
  let c := ((coefficients l gs R X hR).2)⁻¹
  have he : sourceState l gs R X hR =ᶠ[𝓝 x] fun t => c • outgoing l t := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact sourceState_exterior l h hR t ht
  obtain ⟨hu,hp⟩ := outgoing_ode l x (hR.trans_le (chain_ordered h) |>.trans hx)
  have he1 := he.mono (fun _ ht => congrArg Prod.fst ht)
  have he2 := he.mono (fun _ ht => congrArg Prod.snd ht)
  constructor
  · convert (hu.const_mul c).congr_of_eventuallyEq he1 using 1
    rw [sourceState_exterior l h hR x hx]
    rfl
  · convert (hp.const_mul c).congr_of_eventuallyEq he2 using 1
    rw [sourceState_exterior l h hR x hx]
    simp only [Prod.smul_fst,smul_eq_mul,c]
    ring

end OQ14.RadialGluing

#print axioms OQ14.RadialGluing.wave_state_inner
#print axioms OQ14.RadialGluing.wave_state_outer
#print axioms OQ14.RadialGluing.back_zero_width
#print axioms OQ14.RadialGluing.profile_outer
#print axioms OQ14.RadialGluing.profile_inner
#print axioms OQ14.RadialGluing.wave_state_continuousOn
#print axioms OQ14.RadialGluing.profile_continuous
#print axioms OQ14.RadialGluing.profile_hasDerivAt
#print axioms OQ14.RadialGluing.outgoing_continuousOn
#print axioms OQ14.RadialGluing.outerMatched_continuousOn
#print axioms OQ14.RadialGluing.core_state_continuousOn
#print axioms OQ14.RadialGluing.sourceState_continuousOn
#print axioms OQ14.RadialGluing.sourceState_core
#print axioms OQ14.RadialGluing.sourceState_exterior
#print axioms OQ14.RadialGluing.sourceState_core_ode
#print axioms OQ14.RadialGluing.sourceState_stack_ode
#print axioms OQ14.RadialGluing.outgoing_ode
#print axioms OQ14.RadialGluing.sourceState_exterior_ode
