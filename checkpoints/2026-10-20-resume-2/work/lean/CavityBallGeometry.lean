import DisjointBallCells

/-! # Actual connected cavities around separated inclusions -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000

namespace OQ14.CavityBallGeometry

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.MaterialCellGraph
open OQ14.DisjointBallGeometry
open scoped Topology

def clamp (b : ℝ) (x : Space) : Space := (max 1 (‖x‖/b))⁻¹ • x

theorem clamp_fixed (b : ℝ) (hb : 0 < b) (x : Space) (hx : ‖x‖ ≤ b) :
    clamp b x = x := by
  rw [clamp,max_eq_left ((div_le_one hb).mpr hx),inv_one,one_smul]

theorem clamp_continuous (b : ℝ) : Continuous (clamp b) := by
  have hm : Continuous (fun x : Space => max 1 (‖x‖/b)) :=
    continuous_const.max (continuous_norm.div_const b)
  exact (hm.inv₀ (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))).smul continuous_id

theorem clamp_norm_of_lt (b : ℝ) (hb : 0 < b) (x : Space) (hx : b < ‖x‖) :
    ‖clamp b x‖ = b := by
  have hn : 0 < ‖x‖ := hb.trans hx
  have hratio : 1 ≤ ‖x‖/b := (one_le_div hb).mpr hx.le
  rw [clamp,max_eq_right hratio,norm_smul,Real.norm_eq_abs,abs_inv,
    abs_of_pos (div_pos hn hb)]
  field_simp

theorem clamp_norm_le (b : ℝ) (hb : 0 < b) (x : Space) : ‖clamp b x‖ ≤ b := by
  by_cases hx : ‖x‖ ≤ b
  · rw [clamp_fixed b hb x hx]
    exact hx
  · exact (clamp_norm_of_lt b hb x (lt_of_not_ge hx)).le

theorem clamp_punctured {ι : Type*} (center : ι → Space) (b : ℝ) (hb : 0 < b)
    (hc : ∀ i, ‖center i‖ < b) (x : Space) (hx : x ∈ punctured center) :
    clamp b x ∈ punctured center := by
  by_cases hxb : ‖x‖ ≤ b
  · rwa [clamp_fixed b hb x hxb]
  · rintro ⟨i,hi⟩
    have hn := clamp_norm_of_lt b hb x (lt_of_not_ge hxb)
    rw [← hi] at hn
    linarith [hc i]

def puncturedCore {ι : Type*} (center : ι → Space) (L : ℝ) : Set Space :=
  ball 0 L ∩ punctured center

theorem exists_clamp_radius {ι : Type*} [Fintype ι] (center : ι → Space) (L : ℝ)
    (hL : 0 < L) (hc : ∀ i, ‖center i‖ < L) (x y : Space)
    (hx : x ∈ ball 0 L) (hy : y ∈ ball 0 L) :
    ∃ b : ℝ, 0 < b ∧ b < L ∧ (∀ i, ‖center i‖ < b) ∧ ‖x‖ < b ∧ ‖y‖ < b := by
  let g : Option (ι ⊕ Bool) → ℝ
    | none => L
    | some (.inl i) => L-‖center i‖
    | some (.inr false) => L-‖x‖
    | some (.inr true) => L-‖y‖
  have hx' : ‖x‖ < L := by simpa only [mem_ball,dist_zero_right] using hx
  have hy' : ‖y‖ < L := by simpa only [mem_ball,dist_zero_right] using hy
  have hg : ∀ j, 0 < g j := by
    intro j
    rcases j with _ | j
    · exact hL
    · rcases j with i | t
      · exact sub_pos.mpr (hc i)
      · cases t <;> simp only [g] <;> linarith
  obtain ⟨δ,hδ,hd⟩ := exists_positive_uniform_lt g hg
  refine ⟨L-δ,?_,by linarith,?_,?_,?_⟩
  · have := hd none
    dsimp [g] at this
    linarith
  · intro i
    have := hd (some (.inl i))
    dsimp [g] at this
    linarith
  · have := hd (some (.inr false))
    dsimp [g] at this
    linarith
  · have := hd (some (.inr true))
    dsimp [g] at this
    linarith

theorem puncturedCore_joined {ι : Type*} [Fintype ι] (center : ι → Space) (L : ℝ)
    (hL : 0 < L) (hc : ∀ i, ‖center i‖ < L) (x y : Space)
    (hx : x ∈ puncturedCore center L) (hy : y ∈ puncturedCore center L) :
    JoinedIn (puncturedCore center L) x y := by
  obtain ⟨b,hb,hbL,hcb,hxb,hyb⟩ := exists_clamp_radius center L hL hc x y hx.1 hy.1
  have hp := (punctured_isPathConnected center).joinedIn x hx.2 y hy.2
  have hm := hp.map_continuousOn (clamp_continuous b).continuousOn
  have hm' : JoinedIn (puncturedCore center L) (clamp b x) (clamp b y) := hm.mono (by
    rintro z ⟨v,hv,rfl⟩
    refine ⟨?_,clamp_punctured center b hb hcb v hv⟩
    exact (mem_ball_zero_iff).mpr ((clamp_norm_le b hb v).trans_lt hbL))
  simpa only [clamp_fixed b hb x hxb.le,clamp_fixed b hb y hyb.le] using hm'

def cavity {ι : Type*} (center : ι → Space) (radius : ι → ℝ) (L : ℝ) : Set Space :=
  ball 0 L ∩ exterior center radius

theorem familyPush_core {ι : Type*} [Fintype ι] (center : ι → Space) (a : ι → ℝ)
    (L : ℝ) (ha : ∀ i, 0 ≤ a i) (hcore : ∀ i, ‖center i‖+a i < L)
    (hsep : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j))
    (x : Space) (hx : x ∈ puncturedCore center L) : familyPush center a x ∈ ball 0 L := by
  classical
  by_cases hactive : ∃ i, dist x (center i) < a i
  · obtain ⟨i,hi⟩ := hactive
    have heq := familyPush_eq_one center a hsep x hx.2 i hi
    have hd : dist (familyPush center a x) (center i) = a i := by
      rw [heq,radialPush_dist _ _ _ (punctured_ne center hx.2 i) (ha i),max_eq_left hi.le]
    have ht := norm_add_le (familyPush center a x-center i) (center i)
    rw [sub_add_cancel,← dist_eq_norm,hd] at ht
    exact (mem_ball_zero_iff).mpr (by linarith [hcore i])
  · have hfixed := familyPush_fixed center a x hx.2
      (fun i => not_lt.mp (fun hi => hactive ⟨i,hi⟩))
    rw [hfixed]
    exact hx.1

theorem cavity_nonempty {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L : ℝ) (hL : 0 < L) (hcore : ∀ i, ‖center i‖+radius i < L) :
    (cavity center radius L).Nonempty := by
  let g : Option ι → ℝ
    | none => L
    | some i => L-(‖center i‖+radius i)
  have hg : ∀ j, 0 < g j := by
    intro j
    cases j with
    | none => exact hL
    | some i => exact sub_pos.mpr (hcore i)
  obtain ⟨δ,hδ,hd⟩ := exists_positive_uniform_lt g hg
  let b := L-δ
  have hb : 0 < b := by have := hd none; dsimp [g] at this; dsimp [b]; linarith
  have hn : ‖OQ14.RadialMaterialCells.axis b‖ = b := by
    rw [OQ14.RadialMaterialCells.axis_norm,abs_of_pos hb]
  refine ⟨OQ14.RadialMaterialCells.axis b,?_,fun i => ?_⟩
  · apply mem_ball_zero_iff.mpr
    rw [hn]
    dsimp [b]
    linarith
  · have hi := hd (some i)
    dsimp [g] at hi
    have ht := norm_add_le (OQ14.RadialMaterialCells.axis b-center i) (center i)
    rw [sub_add_cancel,hn,← dist_eq_norm] at ht
    dsimp [b] at ht
    linarith

theorem cavity_joined {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (L : ℝ) (hL : 0 < L) (hr : ∀ i, 0 ≤ radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (x y : Space) (hx : x ∈ cavity center radius L) (hy : y ∈ cavity center radius L) :
    JoinedIn (cavity center radius L) x y := by
  obtain ⟨δ₀,hδ₀,hends,hseparation⟩ := exists_inflation center radius hsep x y hx.2 hy.2
  obtain ⟨d,hd,hdcore⟩ := exists_positive_uniform_lt
    (fun i => L-(‖center i‖+radius i)) (fun i => sub_pos.mpr (hcore i))
  let δ := min δ₀ d/2
  have hδ : 0 < δ := half_pos (lt_min hδ₀ hd)
  have hδ₀' : δ < δ₀ := (half_lt_self (lt_min hδ₀ hd)).trans_le (min_le_left _ _)
  have hδd : δ < d := (half_lt_self (lt_min hδ₀ hd)).trans_le (min_le_right _ _)
  let a : ι → ℝ := fun i => radius i+δ
  have ha : ∀ i, 0 ≤ a i := fun i => by dsimp [a]; linarith [hr i]
  have hra : ∀ i, radius i < a i := fun i => by dsimp [a]; linarith
  have haCore : ∀ i, ‖center i‖+a i < L := fun i => by
    have := hdcore i
    dsimp [a]
    linarith
  have haSep : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j) := by
    intro i j hij
    have := hseparation i j hij
    dsimp [a]
    linarith
  have hxp : x ∈ puncturedCore center L := ⟨hx.1,exterior_punctured center radius hr hx.2⟩
  have hyp : y ∈ puncturedCore center L := ⟨hy.1,exterior_punctured center radius hr hy.2⟩
  have hc : ∀ i, ‖center i‖ < L := fun i => by linarith [hcore i,hr i]
  have hp := puncturedCore_joined center L hL hc x y hxp hyp
  have hm := hp.map_continuousOn ((familyPush_continuousOn center a).mono (fun _ hx => hx.2))
  have hm' : JoinedIn (cavity center radius L) (familyPush center a x) (familyPush center a y) :=
    hm.mono (by
      rintro z ⟨v,hv,rfl⟩
      exact ⟨familyPush_core center a L ha haCore haSep v hv,
        familyPush_exterior center radius a ha hra haSep v hv.2⟩)
  have hax : ∀ i, a i ≤ dist x (center i) := fun i => by
    have := (hends i).1
    dsimp [a]
    linarith
  have hay : ∀ i, a i ≤ dist y (center i) := fun i => by
    have := (hends i).2
    dsimp [a]
    linarith
  simpa only [familyPush_fixed center a x hxp.2 hax,
    familyPush_fixed center a y hyp.2 hay] using hm'

theorem cavity_isPathConnected {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (L : ℝ) (hL : 0 < L) (hr : ∀ i, 0 ≤ radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) :
    IsPathConnected (cavity center radius L) := by
  obtain ⟨x,hx⟩ := cavity_nonempty center radius L hL hcore
  exact ⟨x,hx,fun {y} hy => cavity_joined center radius L hL hr hcore hsep x y hx hy⟩

theorem cavity_isConnected {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (L : ℝ) (hL : 0 < L) (hr : ∀ i, 0 ≤ radius i)
    (hcore : ∀ i, ‖center i‖+radius i < L)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) :
    IsConnected (cavity center radius L) :=
  (cavity_isPathConnected center radius L hL hr hcore hsep).isConnected

theorem cavity_isOpen {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (L : ℝ) : IsOpen (cavity center radius L) :=
  isOpen_ball.inter (exterior_isOpen center radius)

end OQ14.CavityBallGeometry

#print axioms OQ14.CavityBallGeometry.clamp_fixed
#print axioms OQ14.CavityBallGeometry.clamp_continuous
#print axioms OQ14.CavityBallGeometry.clamp_norm_of_lt
#print axioms OQ14.CavityBallGeometry.clamp_norm_le
#print axioms OQ14.CavityBallGeometry.clamp_punctured
#print axioms OQ14.CavityBallGeometry.exists_clamp_radius
#print axioms OQ14.CavityBallGeometry.puncturedCore_joined
#print axioms OQ14.CavityBallGeometry.familyPush_core
#print axioms OQ14.CavityBallGeometry.cavity_nonempty
#print axioms OQ14.CavityBallGeometry.cavity_joined
#print axioms OQ14.CavityBallGeometry.cavity_isPathConnected
#print axioms OQ14.CavityBallGeometry.cavity_isConnected
#print axioms OQ14.CavityBallGeometry.cavity_isOpen
