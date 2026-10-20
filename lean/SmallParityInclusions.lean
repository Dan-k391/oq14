import ParityReactionVolume

/-! # Derived small-ball self-consistent inverse for the explicit parity kernel

The gain is b/a and the actual material is supported in finitely many balls
of radii rho*a inside a fixed enclosing ball. Numeric smallness is proved
from that geometry and a common coefficient bound.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.SmallParityInclusions

open MeasureTheory Metric DynamicConvolution ParityReactionVolume
open scoped Topology BigOperators

theorem abs_square_sub_one (x : ℝ) : |x^2-1| ≤ x^2+1 := by
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg x]

def explicitBound (C V k R b a : ℝ) : ℝ :=
  C * Real.sqrt (V*a^3) * DynamicSupportVolume.kernelSize k R +
    (9*C*V*SphereReactionKernel.entryBound k) *
      (b^2*a + 2*a^3 + a^5/b^2)

theorem scaled_perturbation_bound {c : Coefficient} (d : SupportData c)
    (k b a C V : ℝ) (ha : 0 < a) (hb : b ≠ 0) (hC : 0 ≤ C)
    (hc : c.bound ≤ C) (hv : volume.real d.carrier ≤ V*a^3) :
    perturbationBound d k (b/a) ≤ explicitBound C V k d.radius b a := by
  have hdy : DynamicSupportVolume.volumeBound c k d.radius d.carrier ≤
      C * Real.sqrt (V*a^3) * DynamicSupportVolume.kernelSize k d.radius := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hc (Real.sqrt_le_sqrt hv) (Real.sqrt_nonneg _) hC)
      (DynamicSupportVolume.kernelSize_nonnegative k d.radius)
  have hr : reactionBound d k ≤ 9*C*(V*a^3)*SphereReactionKernel.entryBound k := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) hv measureReal_nonneg
        (mul_nonneg (by norm_num) hC)) (SphereReactionKernel.entryBound_nonnegative k)
  have hf : |(b/a)^2-1| + |(b/a)⁻¹^2-1| ≤ (b/a)^2 + (b/a)⁻¹^2 + 2 := by
    linarith [abs_square_sub_one (b/a), abs_square_sub_one (b/a)⁻¹]
  unfold perturbationBound explicitBound
  apply (add_le_add hdy (mul_le_mul hf hr (reactionBound_nonnegative d k)
    (by positivity))).trans_eq
  congr 1
  rw [inv_div]
  field_simp [ha.ne', hb]
  ring

theorem explicitBound_continuous (C V k R b : ℝ) :
    Continuous (explicitBound C V k R b) := by
  unfold explicitBound
  fun_prop

theorem smallness_radius (C V k R b : ℝ) :
    ∃ δ > 0, ∀ a : ℝ, |a| < δ → explicitBound C V k R b a < 1/2 := by
  have hzero : explicitBound C V k R b 0 = 0 := by simp [explicitBound]
  have h := (explicitBound_continuous C V k R b).continuousAt.eventually
    (gt_mem_nhds (by rw [hzero]; norm_num : explicitBound C V k R b 0 < 1/2))
  obtain ⟨δ, hδ, hh⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun a ha => hh (by simpa only [dist_zero_right, Real.norm_eq_abs] using ha)⟩

/-- Uniform invertibility for the actual explicit-kernel block is derived
for all sufficiently small actual balls, rather than assumed through an
operator-norm or Green-convergence hypothesis. -/
theorem finite_small_balls_inverse {ι : Type*} [Fintype ι]
    (p : ι → Space) (ρ R k b C : ℝ) (hρ : 0 ≤ ρ) (hb : 0 < b) (hC : 0 ≤ C)
    (hinside : ∀ i, ‖p i‖ + ρ ≤ R) :
    ∃ δ > 0, ∀ a : ℝ, 0 < a → a < δ →
      ∀ (c : Coefficient), c.bound ≤ C →
      (∀ x : Space, x ∉ ⋃ i, ball (p i) (ρ*a) →
        c.value (VectorFourier.coordinateMap x) = 0) →
      ∃ d : SupportData c, d.radius = R ∧ d.carrier = (⋃ i, ball (p i) (ρ*a)) ∧
        IsUnit (StaticCoefficient.weightedBlock c - perturbation d k (b/a)) ∧
        ‖Ring.inverse (StaticCoefficient.weightedBlock c - perturbation d k (b/a))‖ ≤ 2 := by
  let V : ℝ := (Fintype.card ι : ℝ) * ρ^3 * (Real.pi*4/3)
  obtain ⟨δ, hδ, hh⟩ := smallness_radius C V k R b
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro a ha had c hc hcs
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  have hi : ∀ i, ‖p i‖ + ρ*a ≤ R := by
    intro i
    linarith [hinside i, mul_le_mul_of_nonneg_left ha1 hρ]
  let d : SupportData c := BoundedMaterialKernel.ofFiniteBalls c R p (fun _ => ρ*a) hi hcs
  have hv : volume.real d.carrier ≤ V*a^3 := by
    apply (DynamicSupportVolume.finite_ball_volume p (fun _ => ρ*a)
      (fun _ => mul_nonneg hρ ha.le)).trans_eq
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    unfold V
    ring
  have hbound : perturbationBound d k (b/a) < 1/2 :=
    (scaled_perturbation_bound d k b a C V ha hb.ne' hC hc hv).trans_lt
      (hh a (by rw [abs_of_pos ha]; exact had.trans_le (min_le_left _ _)))
  exact ⟨d, rfl, rfl, explicitBlock_isUnit d k (b/a) (by linarith),
    explicitBlock_inverse_le_two d k (b/a) hbound.le⟩

end OQ14.SmallParityInclusions

#print axioms OQ14.SmallParityInclusions.abs_square_sub_one
#print axioms OQ14.SmallParityInclusions.scaled_perturbation_bound
#print axioms OQ14.SmallParityInclusions.explicitBound_continuous
#print axioms OQ14.SmallParityInclusions.smallness_radius
#print axioms OQ14.SmallParityInclusions.finite_small_balls_inverse
