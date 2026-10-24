import HalfTurnVectorAction
import FiniteSphereStatic
import RestrictedTEDipoleProfile

/-! The finite-ball coefficient of the parity device together with the half-turn images of its balls.

Doubling.  The partner-ball coefficient has twice as many balls as the original device: every ball
`ball (p l) (r l)` is joined by its half-turn image `ball (rot (p l)) (r l)`.  The index type of the doubled
family is `ι ⊕ ι` (`Fintype.card_sum`), so the dipole count doubles. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEPartnerBalls
open MeasureTheory Metric Set
abbrev Space := FourierL2.Space
abbrev Coefficient := StaticCoefficient.Coefficient
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Centres of the doubled family: the original centres and their half-turn images. -/
def partnerCentre (p : ι → Space) : ι ⊕ ι → Space :=
  Sum.elim p (fun l => HalfTurnVectorAction.rot (p l))

/-- Radii of the doubled family: each image ball has the radius of its original. -/
def partnerRadius (r : ι → ℝ) : ι ⊕ ι → ℝ := Sum.elim r r

/-- The finite-ball coefficient (contrast `χ`) of the original balls together with their half-turn images. -/
def partnerCoefficient (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) : Coefficient :=
  FiniteSphereStatic.coefficient (partnerCentre p) (partnerRadius r) χ hχ

theorem card_partner : Fintype.card (ι ⊕ ι)=2*Fintype.card ι := by
  rw [Fintype.card_sum]
  ring

theorem rot_mem_ball (x c : Space) (r : ℝ) :
    HalfTurnVectorAction.rot x∈ball c r ↔ x∈ball (HalfTurnVectorAction.rot c) r := by
  simp only [mem_ball]
  have h := HalfTurnVectorAction.rot.dist_map (HalfTurnVectorAction.rot x) c
  have h2 : dist x (HalfTurnVectorAction.rot c)=dist (HalfTurnVectorAction.rot x) c := by
    have := HalfTurnVectorAction.rot.dist_map x (HalfTurnVectorAction.rot c)
    rw [HalfTurnVectorAction.rot_rot] at this
    exact this.symm
  rw [h2]

theorem partner_union_rot (p : ι → Space) (r : ι → ℝ) (x : Space)
    (hx : x∈⋃ j, ball (partnerCentre p j) (partnerRadius r j)) :
    HalfTurnVectorAction.rot x∈⋃ j, ball (partnerCentre p j) (partnerRadius r j) := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  rcases j with l | l
  · refine mem_iUnion.mpr ⟨Sum.inr l, ?_⟩
    simp only [partnerCentre, partnerRadius, Sum.elim_inl, Sum.elim_inr] at hj ⊢
    rw [rot_mem_ball, HalfTurnVectorAction.rot_rot]
    exact hj
  · refine mem_iUnion.mpr ⟨Sum.inl l, ?_⟩
    simp only [partnerCentre, partnerRadius, Sum.elim_inl, Sum.elim_inr] at hj ⊢
    exact (rot_mem_ball x (p l) (r l)).mpr hj

theorem partner_union_invariant (p : ι → Space) (r : ι → ℝ) (x : Space) :
    HalfTurnVectorAction.rot x∈⋃ j, ball (partnerCentre p j) (partnerRadius r j) ↔
      x∈⋃ j, ball (partnerCentre p j) (partnerRadius r j) := by
  constructor
  · intro h
    have := partner_union_rot p r _ h
    rwa [HalfTurnVectorAction.rot_rot] at this
  · exact partner_union_rot p r x

/-- The partner-ball coefficient is half-turn symmetric. -/
theorem partner_symmetric (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) :
    HalfTurnVectorAction.Symmetric (partnerCoefficient p r χ hχ) := by
  intro x
  unfold partnerCoefficient
  rw [FiniteSphereStatic.coefficient_value, FiniteSphereStatic.coefficient_value]
  by_cases h : x∈⋃ j, ball (partnerCentre p j) (partnerRadius r j)
  · rw [if_pos h, if_pos ((partner_union_invariant p r x).mpr h)]
  · rw [if_neg h, if_neg (fun h' => h ((partner_union_invariant p r x).mp h'))]

/-- The partner-ball coefficient has the same bound `χ` as the original finite-ball coefficient. -/
theorem partner_bound (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) :
    (partnerCoefficient p r χ hχ).bound=χ := rfl

theorem partner_bound_eq (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) :
    (partnerCoefficient p r χ hχ).bound=(FiniteSphereStatic.coefficient p r χ hχ).bound := rfl

theorem partner_inside (p : ι → Space) (r : ι → ℝ) (R : ℝ) (hinside : ∀ l, ‖p l‖+r l≤R) :
    ∀ j, ‖partnerCentre p j‖+partnerRadius r j≤R := by
  intro j
  rcases j with l | l
  · simpa [partnerCentre, partnerRadius] using hinside l
  · simpa [partnerCentre, partnerRadius, HalfTurnVectorAction.rot.norm_map] using hinside l

/-- Support data of the partner-ball coefficient in the ball of radius `R`. -/
def partnerSupport (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (R : ℝ)
    (hinside : ∀ l, ‖p l‖+r l≤R) :
    BoundedMaterialKernel.SupportData (partnerCoefficient p r χ hχ) :=
  FiniteSphereStatic.supportData (partnerCentre p) (partnerRadius r) χ hχ R (partner_inside p r R hinside)

theorem partnerSupport_radius (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (R : ℝ)
    (hinside : ∀ l, ‖p l‖+r l≤R) : (partnerSupport p r χ hχ R hinside).radius=R := rfl

theorem partnerSupport_carrier (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (R : ℝ)
    (hinside : ∀ l, ‖p l‖+r l≤R) :
    (partnerSupport p r χ hχ R hinside).carrier=⋃ j, ball (partnerCentre p j) (partnerRadius r j) := rfl

/-- The partner-ball coefficient vanishes outside the closed ball of radius `R`. -/
theorem partner_zero_outside (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (R : ℝ)
    (hinside : ∀ l, ‖p l‖+r l≤R) (x : Space) (hx : x∉closedBall (0 : Space) R) :
    (partnerCoefficient p r χ hχ).value (VectorFourier.coordinateMap x)=0 :=
  (partnerSupport p r χ hχ R hinside).ballZero x hx

/-- Carrier points lie in the ball of radius `R` (for the symmetric shell closure `hcar` hypothesis). -/
theorem partner_carrier_norm (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (R : ℝ)
    (hinside : ∀ l, ‖p l‖+r l≤R) (x : Space)
    (hx : x∈(partnerSupport p r χ hχ R hinside).carrier) : ‖x‖≤R := by
  rw [partnerSupport_carrier] at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  have h1 := partner_inside p r R hinside j
  have h2 : ‖x-partnerCentre p j‖<partnerRadius r j := by
    simpa only [mem_ball, dist_eq_norm] using hj
  have h3 := norm_add_le (x-partnerCentre p j) (partnerCentre p j)
  rw [sub_add_cancel] at h3
  linarith

/-- Value of the partner coefficient on an original ball. -/
theorem partner_value_original (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (l : ι) (x : Space)
    (hx : x∈ball (p l) (r l)) :
    (partnerCoefficient p r χ hχ).value (VectorFourier.coordinateMap x)=χ := by
  unfold partnerCoefficient
  rw [FiniteSphereStatic.coefficient_value, if_pos]
  exact mem_iUnion.mpr ⟨Sum.inl l, hx⟩

/-- Value of the partner coefficient on a partner ball. -/
theorem partner_value_partner (p : ι → Space) (r : ι → ℝ) (χ : ℝ) (hχ : 0≤χ) (l : ι) (x : Space)
    (hx : x∈ball (HalfTurnVectorAction.rot (p l)) (r l)) :
    (partnerCoefficient p r χ hχ).value (VectorFourier.coordinateMap x)=χ := by
  unfold partnerCoefficient
  rw [FiniteSphereStatic.coefficient_value, if_pos]
  exact mem_iUnion.mpr ⟨Sum.inr l, hx⟩

/-! ### Geometry of the doubled device -/

theorem rot_apply_zero (x : Space) : HalfTurnVectorAction.rot x 0=-x 0 := by
  rw [HalfTurnVectorAction.rot_coordinate]
  simp [HalfTurnVectorAction.o, SphereReactionKernel.sign]

theorem rot_apply_one (x : Space) : HalfTurnVectorAction.rot x 1=-x 1 := by
  rw [HalfTurnVectorAction.rot_coordinate]
  simp [HalfTurnVectorAction.o, SphereReactionKernel.sign]

theorem rot_apply_two (x : Space) : HalfTurnVectorAction.rot x 2=x 2 := by
  rw [HalfTurnVectorAction.rot_coordinate]
  simp [HalfTurnVectorAction.o, SphereReactionKernel.sign]

/-- The half-turn image of a point above the plane position `c` is the point above `-c` at the same height. -/
theorem rot_abovePoint (c : PlaneInverseCube.Plane) (t : ℝ) :
    HalfTurnVectorAction.rot (OQ14.RestrictedTEDipoleProfile.abovePoint c t)=
      OQ14.RestrictedTEDipoleProfile.abovePoint (-c) t := by
  ext i
  fin_cases i
  · simp [rot_apply_zero, OQ14.RestrictedTEDipoleProfile.abovePoint]
  · simp [rot_apply_one, OQ14.RestrictedTEDipoleProfile.abovePoint]
  · simp [rot_apply_two, OQ14.RestrictedTEDipoleProfile.abovePoint]

/-- A device on the line `x = r` and its half-turn image on the line `x = -r` are `2|r|` apart. -/
theorem partner_gap (r : ℝ) (c : ι → PlaneInverseCube.Plane) (hc : ∀ l, c l 0=r) (t : ℝ) (l k : ι) :
    2*|r|≤dist (OQ14.RestrictedTEDipoleProfile.abovePoint (c l) t)
      (HalfTurnVectorAction.rot (OQ14.RestrictedTEDipoleProfile.abovePoint (c k) t)) := by
  have h := PiLp.norm_apply_le (OQ14.RestrictedTEDipoleProfile.abovePoint (c l) t-
    HalfTurnVectorAction.rot (OQ14.RestrictedTEDipoleProfile.abovePoint (c k) t)) 0
  rw [dist_eq_norm]
  have h0 : (OQ14.RestrictedTEDipoleProfile.abovePoint (c l) t-
      HalfTurnVectorAction.rot (OQ14.RestrictedTEDipoleProfile.abovePoint (c k) t)) 0=2*r := by
    simp [rot_apply_zero, OQ14.RestrictedTEDipoleProfile.abovePoint, hc]
    ring
  rw [h0, Real.norm_eq_abs, abs_mul, abs_two] at h
  exact h

/-- Separation of the doubled centres: original separation `δ` and the line gap `2|r|`. -/
theorem partner_separation (r δ t : ℝ) (c : ι → PlaneInverseCube.Plane) (hc : ∀ l, c l 0=r)
    (hsep : ∀ i j : ι, i≠j → δ≤dist (OQ14.RestrictedTEDipoleProfile.abovePoint (c i) t)
      (OQ14.RestrictedTEDipoleProfile.abovePoint (c j) t)) :
    ∀ i j : ι ⊕ ι, i≠j → min δ (2*|r|)≤dist
      (partnerCentre (fun l => OQ14.RestrictedTEDipoleProfile.abovePoint (c l) t) i)
      (partnerCentre (fun l => OQ14.RestrictedTEDipoleProfile.abovePoint (c l) t) j) := by
  intro i j hij
  rcases i with a | a <;> rcases j with b | b
  · have hab : a≠b := fun h => hij (by rw [h])
    exact (min_le_left _ _).trans (hsep a b hab)
  · exact (min_le_right _ _).trans (partner_gap r c hc t a b)
  · rw [dist_comm]
    exact (min_le_right _ _).trans (partner_gap r c hc t b a)
  · have hab : a≠b := fun h => hij (by rw [h])
    simp only [partnerCentre, Sum.elim_inr]
    rw [HalfTurnVectorAction.rot.dist_map]
    exact (min_le_left _ _).trans (hsep a b hab)

/-- Heights are preserved by the half-turn. -/
theorem partner_height (p : ι → Space) (j : ι ⊕ ι) :
    ∃ l : ι, partnerCentre p j 2=p l 2 := by
  rcases j with l | l
  · exact ⟨l, rfl⟩
  · exact ⟨l, by simp [partnerCentre, rot_apply_two]⟩

/-- Support data of the scaled partner-ball coefficient (balls of radius `ρ a`) under the hypotheses used by
`FiniteSphereActualSources.data`. -/
def partnerData (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    BoundedMaterialKernel.SupportData (partnerCoefficient (p a) (fun _ => ρ*a) χ hχ) :=
  partnerSupport (p a) (fun _ => ρ*a) χ hχ R
    (fun l => (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hi a ha ha1 l))

end OQ14.RestrictedTEPartnerBalls
#print axioms OQ14.RestrictedTEPartnerBalls.card_partner
#print axioms OQ14.RestrictedTEPartnerBalls.rot_mem_ball
#print axioms OQ14.RestrictedTEPartnerBalls.partner_union_rot
#print axioms OQ14.RestrictedTEPartnerBalls.partner_union_invariant
#print axioms OQ14.RestrictedTEPartnerBalls.partner_symmetric
#print axioms OQ14.RestrictedTEPartnerBalls.partner_bound
#print axioms OQ14.RestrictedTEPartnerBalls.partner_bound_eq
#print axioms OQ14.RestrictedTEPartnerBalls.partner_inside
#print axioms OQ14.RestrictedTEPartnerBalls.partnerSupport_radius
#print axioms OQ14.RestrictedTEPartnerBalls.partnerSupport_carrier
#print axioms OQ14.RestrictedTEPartnerBalls.partner_zero_outside
#print axioms OQ14.RestrictedTEPartnerBalls.partner_carrier_norm
#print axioms OQ14.RestrictedTEPartnerBalls.partner_value_original
#print axioms OQ14.RestrictedTEPartnerBalls.partner_value_partner
#print axioms OQ14.RestrictedTEPartnerBalls.rot_apply_zero
#print axioms OQ14.RestrictedTEPartnerBalls.rot_apply_one
#print axioms OQ14.RestrictedTEPartnerBalls.rot_apply_two
#print axioms OQ14.RestrictedTEPartnerBalls.rot_abovePoint
#print axioms OQ14.RestrictedTEPartnerBalls.partner_gap
#print axioms OQ14.RestrictedTEPartnerBalls.partner_separation
#print axioms OQ14.RestrictedTEPartnerBalls.partner_height
