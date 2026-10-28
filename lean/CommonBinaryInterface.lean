import CommonBinaryCollar
import ConicalPhysicalInterface

/-! Smooth local boundary certificates for the finite disjoint binary union. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.CommonBinaryInterface
open Set Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)

def component (n : ℕ) (i : ι) : Set Space :=
  {x | x-center i ∈ ConicalJunctionPhysical.inclusion n (ConicalJunctionPhysical.slope (p i).threshold) (a i)}

def body (n : ℕ) : Set Space := ⋃ i, component p a center n i

omit [Fintype ι] [DecidableEq ι] in
theorem component_open (n : ℕ) (i : ι) : IsOpen (component p a center n i) :=
  (ConicalJunctionPhysical.inclusion_open n _ _
    (ConicalJunctionPhysical.slope_properties _ (p i).threshold_pos (p i).threshold_lt_one).1).preimage
      (continuous_id.sub continuous_const)

omit [Fintype ι] [DecidableEq ι] in
theorem body_open (n : ℕ) : IsOpen (body p a center n) := isOpen_iUnion (component_open p a center n)

omit [Fintype ι] [DecidableEq ι] in
theorem body_support (ha0 : ∀ i, 0 < a i) (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (R : ℝ) (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (n : ℕ) : body p a center n ⊆ closedBall (0 : Space) R := by
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  apply hR i
  change ‖x-center i‖ ≤ (p i).cutoff.rOut
  exact (ConicalJunctionPhysical.inclusion_norm_bound n _ _ (ha0 i) (x-center i) hi).le.trans (ha i)

omit [Fintype ι] [DecidableEq ι] in
theorem closure_component_subset (ha0 : ∀ i, 0 < a i)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut) (n : ℕ) (i : ι) :
    closure (component p a center n i) ⊆ ConicalCommonMaterial.outer p center i := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  change ‖x-center i‖ ≤ (p i).cutoff.rOut
  have h := ConicalJunctionPhysical.inclusion_norm_bound n _ _ (ha0 i) (x-center i) hx
  exact h.le.trans (ha i)

omit [Fintype ι] [DecidableEq ι] in
theorem frontier_component (n : ℕ) (i : ι) (x : Space)
    (hx : x ∈ frontier (component p a center n i)) :
    x-center i ∈ frontier (ConicalJunctionPhysical.inclusion n (ConicalJunctionPhysical.slope (p i).threshold) (a i)) := by
  let e : Space ≃ₜ Space := Homeomorph.addRight (-center i)
  have h := e.image_frontier (component p a center n i)
  have hx' : e x ∈ e '' frontier (component p a center n i) := ⟨x,hx,rfl⟩
  rw [h] at hx'
  have he : e '' component p a center n i = ConicalJunctionPhysical.inclusion n (ConicalJunctionPhysical.slope (p i).threshold) (a i) := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      simpa [e, component, sub_eq_add_neg] using hz
    · intro hy
      refine ⟨y+center i, ?_, ?_⟩
      · simpa [component] using hy
      · simp [e]
  rw [he] at hx'
  simpa [e,sub_eq_add_neg] using hx'

omit [DecidableEq ι] in
theorem frontier_body_component (n : ℕ) (x : Space) (hx : x ∈ frontier (body p a center n)) :
    ∃ i, x ∈ frontier (component p a center n i) := by
  have hc : x ∈ closure (body p a center n) := frontier_subset_closure hx
  rw [body, closure_iUnion_of_finite] at hc
  obtain ⟨i, hi⟩ := mem_iUnion.mp hc
  refine ⟨i, ?_⟩
  have hn : x ∉ body p a center n := by
    intro h
    have hOpen := body_open p a center n
    exact (Set.disjoint_left.mp disjoint_interior_frontier) (hOpen.interior_eq.symm ▸ h) hx
  rw [frontier]
  refine ⟨hi, ?_⟩
  intro hint
  apply hn
  exact mem_iUnion.mpr ⟨i, interior_subset hint⟩

theorem body_frontier_certificate (ha0 : ∀ i, 0 < a i)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j))
    (n : ℕ) (hsmall : ∀ i,
      (4 + (2*ConicalJunctionPhysical.slope (p i).threshold+2)^2) * (ConicalTipRounding.radius n)^2 +
        ConicalTipRounding.radius n < (a i)^2)
    (x : Space) (hx : x ∈ frontier (body p a center n)) :
    ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
      ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ body p a center n ↔ 0 < F y) := by
  classical
  obtain ⟨i, hi⟩ := frontier_body_component p a center n x hx
  have houter : x ∈ ConicalCommonMaterial.outer p center i :=
    closure_component_subset p a center ha0 ha n i (frontier_subset_closure hi)
  have hphysical := frontier_component p a center n i x hi
  obtain ⟨hsm,hzero,hder,V,hV,hxV,hlevel⟩ := ConicalPhysicalInterface.physical_local_certificate
    n (ConicalJunctionPhysical.slope (p i).threshold) (a i)
    (ConicalJunctionPhysical.slope_properties _ (p i).threshold_pos (p i).threshold_lt_one).1
    (x-center i) hphysical (hsmall i)
  let F : Space → ℝ := fun y => ConicalPhysicalInterface.physicalDef n
    (ConicalJunctionPhysical.slope (p i).threshold) (a i) (y-center i)
  let W : Set Space := ⋂ j : ι, if j = i then univ else (ConicalCommonMaterial.outer p center j)ᶜ
  have hWopen : IsOpen W := by
    apply isOpen_iInter_of_finite
    intro j
    split_ifs <;> simp [ConicalCommonMaterial.outer, isOpen_compl_iff, isClosed_closedBall]
  have hxW : x ∈ W := by
    apply mem_iInter.mpr
    intro j
    by_cases hji : j = i
    · simp [hji]
    · simp only [hji, ↓reduceIte, mem_compl_iff]
      exact fun hj => (Set.disjoint_left.mp (hsep i j (Ne.symm hji))) houter hj
  have hlocal : ∀ y ∈ W, (y ∈ body p a center n ↔ y ∈ component p a center n i) := by
    intro y hy
    constructor
    · intro hybody
      obtain ⟨j,hj⟩ := mem_iUnion.mp hybody
      by_cases hji : j = i
      · simpa [hji] using hj
      · have hw := mem_iInter.mp hy j
        simp only [hji, ↓reduceIte, mem_compl_iff] at hw
        exact False.elim (hw (closure_component_subset p a center ha0 ha n j (subset_closure hj)))
    · intro hyi
      exact mem_iUnion.mpr ⟨i,hyi⟩
  have hFsmooth : ContDiffAt ℝ (⊤ : ℕ∞) F x := by
    have hsub : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Space => y-center i) x :=
      (contDiff_id.sub contDiff_const).contDiffAt
    exact ContDiffAt.comp (f := fun y : Space => y-center i) x hsm hsub
  refine ⟨F, hFsmooth, hzero, ?_, ?_⟩
  · simpa only [F, fderiv_comp_sub] using hder
  · refine ⟨W ∩ ((fun y : Space => y-center i) ⁻¹' V), hWopen.inter (hV.preimage (continuous_id.sub continuous_const)), ⟨hxW,hxV⟩, ?_⟩
    intro y hy
    rw [hlocal y hy.1]
    exact hlevel (y-center i) hy.2

theorem eventually_body_smooth (ha0 : ∀ i, 0 < a i)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j)) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ frontier (body p a center n),
      ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
        ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ body p a center n ↔ 0 < F y) := by
  have he : ∀ᶠ n : ℕ in atTop, ∀ i,
      (4 + (2*ConicalJunctionPhysical.slope (p i).threshold+2)^2) * (ConicalTipRounding.radius n)^2 +
        ConicalTipRounding.radius n < (a i)^2 :=
    Filter.eventually_all.mpr (fun i => ConicalJunctionRadial.eventually_separated
      (ConicalJunctionPhysical.slope (p i).threshold) (a i) (ha0 i).ne')
  filter_upwards [he] with n hn x hx
  exact body_frontier_certificate p a center ha0 ha hsep n hn x hx

omit [DecidableEq ι] in
theorem coefficient_body (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (ha0 : ∀ i, 0 < a i) (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
      (ConicalCommonMaterial.outer p center j))
    (d : ℝ) (hd : ∀ i, (p i).contrast = d) (n : ℕ) (x : Space) :
    (CommonBinaryRounding.coefficient p a center B hB hcontrast ha hsep ha0 n).value
      (VectorFourier.coordinateMap x) = (by classical exact if x ∈ body p a center n then d else 0) := by
  classical
  by_cases hx : x ∈ body p a center n
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have ho := closure_component_subset p a center ha0 ha n i (subset_closure hi)
    rw [CommonBinaryCollar.common_local p a center B hB hcontrast ha hsep ha0 n i x ho]
    change x-center i ∈ ConicalJunctionPhysical.inclusion n (ConicalJunctionPhysical.slope (p i).threshold) (a i) at hi
    simp [hx, CommonBinaryRounding.localValue, ConicalJunctionPhysical.binaryMaterial, hi, hd i]
  · have hz : ∀ i, x ∉ component p a center n i := by
      intro i hi
      exact hx (mem_iUnion.mpr ⟨i,hi⟩)
    simp only [hx, ↓reduceIte, CommonBinaryRounding.coefficient, MeasurableEquiv.symm_apply_apply]
    apply Finset.sum_eq_zero
    intro i _
    have hni := hz i
    change x-center i ∉ ConicalJunctionPhysical.inclusion n (ConicalJunctionPhysical.slope (p i).threshold) (a i) at hni
    simp [CommonBinaryRounding.localValue, ConicalJunctionPhysical.binaryMaterial, hni]

end OQ14.CommonBinaryInterface
#print axioms OQ14.CommonBinaryInterface.frontier_component
#print axioms OQ14.CommonBinaryInterface.body_frontier_certificate
#print axioms OQ14.CommonBinaryInterface.eventually_body_smooth
#print axioms OQ14.CommonBinaryInterface.coefficient_body
#print axioms OQ14.CommonBinaryInterface.body_support
