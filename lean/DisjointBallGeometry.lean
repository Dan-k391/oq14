import RadialMaterialCells
import Mathlib.Order.Filter.Finite

/-! # Actual exterior connectivity for finitely many separated balls -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.DisjointBallGeometry

open MeasureTheory Filter Metric Set OQ14.Maxwell OQ14.RadialMaterialCells
open scoped Topology

theorem exists_positive_uniform_lt {α : Type*} [Finite α] (g : α → ℝ)
    (hg : ∀ i, 0 < g i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ < g i := by
  have hb : ∀ᶠ δ : ℝ in 𝓝 0, ∀ i, δ < g i :=
    eventually_all.mpr (fun i => gt_mem_nhds (hg i))
  have hb' : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ i, δ < g i := nhdsWithin_le_nhds hb
  have hp : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  exact (hp.and hb').exists

def radialPush (c : Space) (a : ℝ) (x : Space) : Space :=
  c+(max 1 (a/‖x-c‖)) • (x-c)

theorem radialPush_fixed (c x : Space) (a : ℝ) (hx : x ≠ c) (ha : a ≤ ‖x-c‖) :
    radialPush c a x = x := by
  have hd : 0 < ‖x-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [radialPush,max_eq_left ((div_le_one hd).mpr ha),one_smul,add_sub_cancel]

theorem radialPush_dist (c x : Space) (a : ℝ) (hx : x ≠ c) (ha : 0 ≤ a) :
    dist (radialPush c a x) c = max a (dist x c) := by
  have hd : 0 < ‖x-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  by_cases hax : a ≤ ‖x-c‖
  · rw [radialPush_fixed c x a hx hax,max_eq_right]
    simpa only [dist_eq_norm] using hax
  · have hxa : ‖x-c‖ ≤ a := (lt_of_not_ge hax).le
    have hratio : 1 ≤ a/‖x-c‖ := (one_le_div hd).mpr hxa
    rw [radialPush,dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,
      max_eq_right hratio,abs_of_nonneg (div_nonneg ha hd.le),div_mul_cancel₀ _ hd.ne']
    exact (max_eq_left (by simpa only [dist_eq_norm] using hxa)).symm

theorem radialPush_continuousOn (c : Space) (a : ℝ) :
    ContinuousOn (radialPush c a) ({c}ᶜ) := by
  intro x hx
  have hn : ‖x-c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hx)
  exact (continuousAt_const.add
    ((continuousAt_const.max (continuousAt_const.div
      (continuousAt_id.sub continuousAt_const).norm hn)).smul
      (continuousAt_id.sub continuousAt_const))).continuousWithinAt

def exterior {ι : Type*} (center : ι → Space) (radius : ι → ℝ) : Set Space :=
  {x | ∀ i, radius i < dist x (center i)}

def punctured {ι : Type*} (center : ι → Space) : Set Space := (range center)ᶜ

theorem punctured_ne {ι : Type*} (center : ι → Space) {x : Space} (hx : x ∈ punctured center)
    (i : ι) : x ≠ center i := fun h => hx ⟨i,h.symm⟩

def familyPush {ι : Type*} [Fintype ι] (center : ι → Space) (a : ι → ℝ) (x : Space) : Space :=
  x+∑ i : ι, (radialPush (center i) (a i) x-x)

theorem familyPush_fixed {ι : Type*} [Fintype ι] (center : ι → Space) (a : ι → ℝ)
    (x : Space) (hx : x ∈ punctured center) (ha : ∀ i, a i ≤ dist x (center i)) :
    familyPush center a x = x := by
  have hf (i : ι) : radialPush (center i) (a i) x = x :=
    radialPush_fixed _ _ _ (punctured_ne center hx i) (by simpa only [dist_eq_norm] using ha i)
  simp only [familyPush,hf,sub_self,Finset.sum_const_zero,add_zero]

theorem familyPush_continuousOn {ι : Type*} [Fintype ι] (center : ι → Space) (a : ι → ℝ) :
    ContinuousOn (familyPush center a) (punctured center) := by
  apply continuousOn_id.add
  apply continuousOn_finset_sum
  intro i _
  exact ((radialPush_continuousOn (center i) (a i)).mono
    (fun x hx => punctured_ne center hx i)).sub continuousOn_id

theorem exists_inflation {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (x y : Space) (hx : x ∈ exterior center radius) (hy : y ∈ exterior center radius) :
    ∃ δ : ℝ, 0 < δ ∧ (∀ i, radius i+δ < dist x (center i) ∧ radius i+δ < dist y (center i)) ∧
      ∀ i j, i ≠ j → (radius i+δ)+(radius j+δ) < dist (center i) (center j) := by
  classical
  let g : ι ⊕ (ι ⊕ (ι × ι)) → ℝ
    | .inl i => dist x (center i)-radius i
    | .inr (.inl i) => dist y (center i)-radius i
    | .inr (.inr (i,j)) => if i = j then 1 else (dist (center i) (center j)-radius i-radius j)/2
  have hg : ∀ t, 0 < g t := by
    intro t
    rcases t with i | t
    · exact sub_pos.mpr (hx i)
    · rcases t with i | ⟨i,j⟩
      · exact sub_pos.mpr (hy i)
      · by_cases hij : i = j
        · simp only [g,if_pos hij]; norm_num
        · simp only [g,if_neg hij]
          linarith [hsep i j hij]
  obtain ⟨δ,hδ,hgδ⟩ := exists_positive_uniform_lt g hg
  refine ⟨δ,hδ,?_,?_⟩
  · intro i
    have hxi := hgδ (.inl i)
    have hyi := hgδ (.inr (.inl i))
    dsimp [g] at hxi hyi
    constructor <;> linarith
  · intro i j hij
    have h := hgδ (.inr (.inr (i,j)))
    simp only [g,if_neg hij] at h
    linarith

theorem familyPush_eq_one {ι : Type*} [Fintype ι] (center : ι → Space) (a : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j))
    (x : Space) (hx : x ∈ punctured center) (i : ι) (hi : dist x (center i) < a i) :
    familyPush center a x = radialPush (center i) (a i) x := by
  classical
  have hf (j : ι) (hji : j ≠ i) : radialPush (center j) (a j) x = x := by
    apply radialPush_fixed _ _ _ (punctured_ne center hx j)
    have ht := dist_triangle (center i) x (center j)
    rw [dist_comm (center i) x] at ht
    have hs := hsep i j (Ne.symm hji)
    rw [← dist_eq_norm]
    linarith
  have hsum : (∑ j : ι, (radialPush (center j) (a j) x-x)) = radialPush (center i) (a i) x-x := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hf j hji,sub_self]
    · simp
  rw [familyPush,hsum]
  abel

theorem familyPush_exterior {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hra : ∀ i, radius i < a i)
    (hsep : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j))
    (x : Space) (hx : x ∈ punctured center) : familyPush center a x ∈ exterior center radius := by
  classical
  by_cases hactive : ∃ i, dist x (center i) < a i
  · obtain ⟨i,hi⟩ := hactive
    have heq := familyPush_eq_one center a hsep x hx i hi
    have hdist : dist (familyPush center a x) (center i) = a i := by
      rw [heq,radialPush_dist _ _ _ (punctured_ne center hx i) (ha i),max_eq_left hi.le]
    intro j
    by_cases hji : j = i
    · subst j
      rw [hdist]
      exact hra i
    · have ht := dist_triangle (center i) (familyPush center a x) (center j)
      rw [dist_comm (center i) (familyPush center a x),hdist] at ht
      have hs := hsep i j (Ne.symm hji)
      linarith [hra j]
  · have hout : ∀ i, a i ≤ dist x (center i) :=
      fun i => not_lt.mp (fun hi => hactive ⟨i,hi⟩)
    rw [familyPush_fixed center a x hx hout]
    exact fun i => lt_of_lt_of_le (hra i) (hout i)

theorem exterior_nonempty {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ) :
    (exterior center radius).Nonempty := by
  obtain ⟨M,hM⟩ := (Set.finite_range (fun i => ‖center i‖+radius i)).bddAbove
  let x := axis (|M|+1)
  have hn : ‖x‖ = |M|+1 := by rw [axis_norm,abs_of_pos (by positivity)]
  refine ⟨x,fun i => ?_⟩
  have hb : ‖center i‖+radius i ≤ M := hM (mem_range_self i)
  have ht := norm_add_le (x-center i) (center i)
  rw [sub_add_cancel,hn] at ht
  rw [dist_eq_norm]
  linarith [le_abs_self M]

theorem exterior_punctured {ι : Type*} (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i) : exterior center radius ⊆ punctured center := by
  intro x hx
  rintro ⟨i,rfl⟩
  have hi := hx i
  simp only [dist_self] at hi
  exact (not_lt_of_ge (hr i)) hi

theorem punctured_isPathConnected {ι : Type*} [Fintype ι] (center : ι → Space) :
    IsPathConnected (punctured center) :=
  (Set.finite_range center).countable.isPathConnected_compl_of_one_lt_rank
    (by rw [rank_three]; norm_num)

theorem exterior_joined {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j))
    (x y : Space) (hx : x ∈ exterior center radius) (hy : y ∈ exterior center radius) :
    JoinedIn (exterior center radius) x y := by
  obtain ⟨δ,hδ,hends,hseparation⟩ := exists_inflation center radius hsep x y hx hy
  let a : ι → ℝ := fun i => radius i+δ
  have ha : ∀ i, 0 ≤ a i := fun i => le_of_lt (by dsimp [a]; linarith [hr i])
  have hra : ∀ i, radius i < a i := fun i => by dsimp [a]; linarith
  have hxp := exterior_punctured center radius hr hx
  have hyp := exterior_punctured center radius hr hy
  have hj := (punctured_isPathConnected center).joinedIn x hxp y hyp
  have hm := hj.map_continuousOn (familyPush_continuousOn center a)
  have hm' : JoinedIn (exterior center radius) (familyPush center a x) (familyPush center a y) :=
    hm.mono (by
      rintro z ⟨v,hv,rfl⟩
      exact familyPush_exterior center radius a ha hra hseparation v hv)
  simpa only [familyPush_fixed center a x hxp (fun i => (hends i).1.le),
    familyPush_fixed center a y hyp (fun i => (hends i).2.le)] using hm'

theorem exterior_isPathConnected {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) :
    IsPathConnected (exterior center radius) := by
  obtain ⟨x,hx⟩ := exterior_nonempty center radius
  exact ⟨x,hx,fun {y} hy => exterior_joined center radius hr hsep x y hx hy⟩

theorem exterior_isConnected {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ)
    (hr : ∀ i, 0 ≤ radius i)
    (hsep : ∀ i j, i ≠ j → radius i+radius j < dist (center i) (center j)) :
    IsConnected (exterior center radius) :=
  (exterior_isPathConnected center radius hr hsep).isConnected

theorem exterior_isOpen {ι : Type*} [Fintype ι] (center : ι → Space) (radius : ι → ℝ) :
    IsOpen (exterior center radius) := by
  have heq : exterior center radius = ⋂ i, {x : Space | radius i < dist x (center i)} := by
    ext x
    simp only [exterior,mem_setOf_eq,mem_iInter]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const
    (continuous_id.dist continuous_const))

theorem exists_exterior_outside {ι : Type*} [Fintype ι] (center : ι → Space)
    (radius : ι → ℝ) (R : ℝ) : ∃ x ∈ exterior center radius, R < ‖x‖ := by
  obtain ⟨M,hM⟩ := (Set.finite_range (fun i => ‖center i‖+radius i)).bddAbove
  let x := axis (|M|+|R|+1)
  have hn : ‖x‖ = |M|+|R|+1 := by rw [axis_norm,abs_of_pos (by positivity)]
  refine ⟨x,fun i => ?_,?_⟩
  · have hb : ‖center i‖+radius i ≤ M := hM (mem_range_self i)
    have ht := norm_add_le (x-center i) (center i)
    rw [sub_add_cancel,hn] at ht
    rw [dist_eq_norm]
    linarith [le_abs_self M,abs_nonneg R]
  · rw [hn]
    linarith [le_abs_self R,abs_nonneg M]

end OQ14.DisjointBallGeometry

#print axioms OQ14.DisjointBallGeometry.exists_positive_uniform_lt
#print axioms OQ14.DisjointBallGeometry.radialPush_fixed
#print axioms OQ14.DisjointBallGeometry.radialPush_dist
#print axioms OQ14.DisjointBallGeometry.radialPush_continuousOn
#print axioms OQ14.DisjointBallGeometry.punctured_ne
#print axioms OQ14.DisjointBallGeometry.familyPush_fixed
#print axioms OQ14.DisjointBallGeometry.familyPush_continuousOn
#print axioms OQ14.DisjointBallGeometry.exists_inflation
#print axioms OQ14.DisjointBallGeometry.familyPush_eq_one
#print axioms OQ14.DisjointBallGeometry.familyPush_exterior
#print axioms OQ14.DisjointBallGeometry.exterior_nonempty
#print axioms OQ14.DisjointBallGeometry.exterior_punctured
#print axioms OQ14.DisjointBallGeometry.punctured_isPathConnected
#print axioms OQ14.DisjointBallGeometry.exterior_joined
#print axioms OQ14.DisjointBallGeometry.exterior_isPathConnected
#print axioms OQ14.DisjointBallGeometry.exterior_isConnected
#print axioms OQ14.DisjointBallGeometry.exterior_isOpen
#print axioms OQ14.DisjointBallGeometry.exists_exterior_outside
