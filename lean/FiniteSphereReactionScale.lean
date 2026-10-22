import FiniteSphereReaction

/-! Actual small-sphere parity reaction fields and dipole asymptotics. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.FiniteSphereReactionScale

open MeasureTheory Metric SphereReactionKernel StaticSphereScale
open scoped Topology BigOperators

abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pointField (electric : Bool) (k : ℝ) (p : ι → Space) (r : ι → ℝ)
    (P : ι → Vector) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∑ l : ι, reaction electric k x (p l) i j*
    ((volume.real (ball (p l) (r l)) : ℂ)*P l j)

def errorConstant (χ ρ δ k R b A M : ℝ) : ℝ :=
  3*(entryBound k*(Real.sqrt χ*FiniteSphereSmallError.errorConstant (ι := ι) χ ρ δ k R b A M*
    Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))+
    SphereReactionLipschitz.bound k*((Fintype.card ι : ℝ)*ρ*volumeConstant ρ*χ*A))

omit [DecidableEq ι] in
theorem moment_scaled (p : ι → Space) (ρ a χ A : ℝ) (hρ : 0 ≤ ρ)
    (ha : 0 < a) (hχ : 0 ≤ χ) (E : ι → Vector) (hE : ∀ l j, ‖E l j‖ ≤ A/a)
    (j : Fin 3) :
    (∑ l : ι, (ρ*a)*(volume.real (ball (p l) (ρ*a))*
      ‖StaticSpherePolarization.polarization χ (E l) j‖)) ≤
      ((Fintype.card ι : ℝ)*ρ*volumeConstant ρ*χ*A)*a^3 := by
  have hb (l : ι) : ‖StaticSpherePolarization.polarization χ (E l) j‖ ≤ χ*(A/a) :=
    (FiniteSphereScale.polarization_component_bound χ hχ (E l) j).trans
      (mul_le_mul_of_nonneg_left (hE l j) hχ)
  simp_rw [← mul_assoc]
  apply (Finset.sum_le_sum (fun l (_ : l ∈ (Finset.univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (hb l)
      (mul_nonneg (mul_nonneg hρ ha.le) measureReal_nonneg))).trans_eq
  simp only [scaled_ball_volume _ ρ a hρ ha.le, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

theorem reaction_from_estimates (p : ι → Space) (ρ a χ δ R k b A M : ℝ)
    (hρ : 0 ≤ ρ) (ha : 0 < a) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector) (hE : ∀ l j, ‖E l j‖ ≤ A/a)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E)
    (electric : Bool) (x : Space) (i : Fin 3) :
    ‖ParityMaterialField.reaction (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
      electric k (ParityMaterialField.solution d k (b/a) f) x i-
      pointField electric k p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) x i‖ ≤
      errorConstant (ι := ι) χ ρ δ k R b A M*a^3 := by
  let c := FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ
  let u := ParityMaterialField.solution d k (b/a) f
  have hb (j : Fin 3) :
      ‖(∫ y, reaction electric k x y i j*DynamicVolume.source c u j y)-
        ∑ l : ι, reaction electric k x (p l) i j*
          ((volume.real (ball (p l) (ρ*a)) : ℂ)*StaticSpherePolarization.polarization χ (E l) j)‖ ≤
        (entryBound k*(Real.sqrt χ*FiniteSphereSmallError.errorConstant (ι := ι) χ ρ δ k R b A M*
          Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))+
          SphereReactionLipschitz.bound k*((Fintype.card ι : ℝ)*ρ*volumeConstant ρ*χ*A))*a^3 := by
    have hf : Integrable (DynamicVolume.source c u j) :=
      (StaticNewton.material_source_integrable c u (closedBall 0 d.radius)
        (isCompact_closedBall 0 d.radius) d.ballZero j).congr (StaticNewton.material_source_ae c u j)
    have hi := FiniteSphereReaction.source_moment_error electric k x i j p (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (E l)) (DynamicVolume.source c u j) hf
    have hl : (∫ y, ‖DynamicVolume.source c u j y-
        FiniteSphereStatic.sumSource p (fun _ => ρ*a)
          (fun l => StaticSpherePolarization.polarization χ (E l)) (VectorFourier.coordinateMap y) j‖) ≤
        (Real.sqrt χ*FiniteSphereSmallError.errorConstant (ι := ι) χ ρ δ k R b A M*
          Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))*a^3 := by
      convert he.2.2 j using 1
      apply integral_congr_ae
      filter_upwards [FiniteSphereStatic.sumSource_ae p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) j] with y hy
      rw [hy]
    apply hi.trans
    have hm := moment_scaled p ρ a χ A hρ ha hχ E hE j
    have hh := add_le_add (mul_le_mul_of_nonneg_left hl (entryBound_nonnegative k))
      (mul_le_mul_of_nonneg_left hm (SphereReactionLipschitz.bound_nonnegative k))
    exact hh.trans_eq (by ring)
  unfold ParityMaterialField.reaction pointField
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) => hb j)).trans_eq
  simp only [Fin.sum_univ_three, errorConstant]
  ring

theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b A M : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hinside : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (f : ℝ → VectorL2) (incident : ℝ → Maxwell.Field) (E : ℝ → ι → Vector)
    (hE : ∀ a, 0 < a → a ≤ 1 → ∀ l j, E a l j = incident a (p a l) j)
    (hcenter : ∀ a, 0 < a → a ≤ 1 → ∀ l j, ‖E a l j‖ ≤ A/a)
    (hincident : ∀ a, 0 < a → a ≤ 1 → ∀ j : Fin 3,
      (fun x => f a (VectorFourier.coordinateMap x) j) =ᵐ[volume]
        fun x => (Real.sqrt ((FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ).value
          (VectorFourier.coordinateMap x)) : ℂ)*incident a x j)
    (hdiff : ∀ a, 0 < a → a ≤ 1 → ∀ l j, ∀ x ∈ ball (p a l) (ρ*a),
      DifferentiableAt ℝ (fun y => incident a y j) x)
    (hder : ∀ a, 0 < a → a ≤ 1 → ∀ l j, ∀ x ∈ ball (p a l) (ρ*a),
      ‖fderiv ℝ (fun y => incident a y j) x‖ ≤ M/a) :
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      ∃ d : BoundedMaterialKernel.SupportData
          (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ),
        d.radius = R ∧ d.carrier = (⋃ l, ball (p a l) (ρ*a)) ∧
          FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R k b A M hχ d (f a) (E a) ∧
          ∀ (electric : Bool) (x : Space) (i : Fin 3),
            ‖ParityMaterialField.reaction
              (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ) electric k
                (ParityMaterialField.solution d k (b/a) (f a)) x i-
              pointField electric k (p a) (fun _ => ρ*a)
                (fun l => StaticSpherePolarization.polarization χ (E a l)) x i‖ ≤
              errorConstant (ι := ι) χ ρ δ k R b A M*a^3 := by
  obtain ⟨η, hη, hh⟩ := FiniteSphereAsymptotics.finite_sphere_family p ρ χ δ R k b A M
    hρ hχ hδ hb hA hM hsep hinside f incident E hE hcenter hincident hdiff hder
  refine ⟨min η 1, lt_min hη zero_lt_one, ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d, hdr, hdc, he⟩ := hh a ha (had.trans_le (min_le_left _ _))
  refine ⟨d, hdr, hdc, he, ?_⟩
  intro electric x i
  exact reaction_from_estimates (p a) ρ a χ δ R k b A M hρ.le ha hχ d (f a) (E a)
    (hcenter a ha ha1) he electric x i

end OQ14.FiniteSphereReactionScale

#print axioms OQ14.FiniteSphereReactionScale.moment_scaled
#print axioms OQ14.FiniteSphereReactionScale.reaction_from_estimates
#print axioms OQ14.FiniteSphereReactionScale.finite_sphere_family
