import StaticPlaneError
import FiniteSphereReaction

/-! Actual finite-ball geometry supplies the moving plane gap for physical sources. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.StaticPlaneInclusions

open MeasureTheory Metric StaticPlaneKernel PlaneInverseCube
open scoped Topology BigOperators

abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2

theorem ball_gap (c : Space) (r d : ℝ) (hc : d+r ≤ |c 2|)
    (x : Space) (hx : x ∈ ball c r) : d ≤ |x 2| := by
  have hn : ‖x-c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hx
  have hi : |x 2-c 2| ≤ ‖x-c‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-c) 2
  have ha := abs_sub_abs_le_abs_sub (c 2) (x 2)
  rw [abs_sub_comm] at ha
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem material_gap (p : ι → Space) (r : ι → ℝ) (χ d : ℝ) (hχ : 0 ≤ χ)
    (hh : ∀ l, d+r l ≤ |p l 2|) (u : VectorL2) (j : Fin 3) :
    ∀ x : Space, DynamicVolume.source (FiniteSphereStatic.coefficient p r χ hχ) u j x ≠ 0 →
      d ≤ |x 2| := by
  intro x hx
  have hu : x ∈ ⋃ l, ball (p l) (r l) := by
    by_contra hout
    apply hx
    unfold DynamicVolume.source
    rw [FiniteSphereStatic.coefficient_value, if_neg hout]
    simp
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu
  exact ball_gap (p l) (r l) d (hh l) x hl

theorem trial_gap (p : ι → Space) (r : ι → ℝ) (P : ι → Vector) (d : ℝ)
    (hh : ∀ l, d+r l ≤ |p l 2|) (j : Fin 3) :
    ∀ᵐ x : Space, FiniteSphereStatic.sumSource p r P (VectorFourier.coordinateMap x) j ≠ 0 →
      d ≤ |x 2| := by
  filter_upwards [FiniteSphereStatic.sumSource_ae p r P j] with x hx hn
  have hu : x ∈ ⋃ l, ball (p l) (r l) := by
    by_contra hout
    apply hn
    rw [hx]
    apply Finset.sum_eq_zero
    intro l _
    apply Set.indicator_of_not_mem
    intro hl
    exact hout (Set.mem_iUnion.mpr ⟨l,hl⟩)
  obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hu
  exact ball_gap (p l) (r l) d (hh l) x hl

theorem material_trial_plane_error (p : ι → Space) (ρ a χ γ C : ℝ)
    (ha : 0 < a) (hχ : 0 ≤ χ) (hγ : 0 < γ)
    (hh : ∀ l, (γ+ρ)*a ≤ |p l 2|) (E : ι → Vector)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (u : VectorL2) (j : Fin 3)
    (he : (∫ y, ‖DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ) u j y-
      ∑ l : ι, (ball (p l) (ρ*a)).indicator
        (fun _ => StaticSpherePolarization.polarization χ (E l) j) y‖) ≤ C*a^3)
    (i : Fin 3) :
    (∫ q : Plane, ‖StaticPlaneSource.field
        (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ) u j) i j q-
      StaticPlaneSource.field
        (fun y => FiniteSphereStatic.sumSource p (fun _ => ρ*a)
          (fun l => StaticSpherePolarization.polarization χ (E l)) (VectorFourier.coordinateMap y) j) i j q‖) ≤
      (3*C/γ)*a^2 := by
  have hh' : ∀ l, γ*a+ρ*a ≤ |p l 2| := by intro l; simpa only [add_mul] using hh l
  apply StaticPlaneError.moving_gap_mass γ a C hγ ha _ _
    (DynamicVolume.source_integrable _ u d.radius d.ballZero j)
    (FiniteSphereReaction.source_integrable p (fun _ => ρ*a)
      (fun l => StaticSpherePolarization.polarization χ (E l)) j)
    (Filter.Eventually.of_forall (material_gap p (fun _ => ρ*a) χ (γ*a) hχ hh' u j))
    (trial_gap p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l)) (γ*a) hh' j) _ i j
  convert he using 1
  apply integral_congr_ae
  filter_upwards [FiniteSphereStatic.sumSource_ae p (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ (E l)) j] with y hy
  rw [hy]

def errorConstant (χ ρ δ k R b A M γ : ℝ) : ℝ :=
  3*(Real.sqrt χ*FiniteSphereSmallError.errorConstant (ι := ι) χ ρ δ k R b A M*
    Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))/γ

theorem inverse_from_estimates (p : ι → Space) (ρ a χ δ R k b A M γ : ℝ)
    (ha : 0 < a) (hχ : 0 ≤ χ) (hγ : 0 < γ) (hh : ∀ l, (γ+ρ)*a ≤ |p l 2|)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E)
    (i j : Fin 3) :
    (∫ q : Plane, ‖StaticPlaneSource.field
        (DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
          (ParityMaterialField.solution d k (b/a) f) j) i j q-
      StaticPlaneSource.field
        (fun y => FiniteSphereStatic.sumSource p (fun _ => ρ*a)
          (fun l => StaticSpherePolarization.polarization χ (E l)) (VectorFourier.coordinateMap y) j) i j q‖) ≤
      errorConstant (ι := ι) χ ρ δ k R b A M γ*a^2 :=
  material_trial_plane_error p ρ a χ γ _ ha hχ hγ hh E d
    (ParityMaterialField.solution d k (b/a) f) j (he.2.2 j) i

theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b A M γ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hγ : 0 < γ)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hinside : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hheight : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
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
          ∀ i j : Fin 3,
            (∫ q : Plane, ‖StaticPlaneSource.field
                (DynamicVolume.source (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
                  (ParityMaterialField.solution d k (b/a) (f a)) j) i j q-
              StaticPlaneSource.field
                (fun y => FiniteSphereStatic.sumSource (p a) (fun _ => ρ*a)
                  (fun l => StaticSpherePolarization.polarization χ (E a l))
                    (VectorFourier.coordinateMap y) j) i j q‖) ≤
              errorConstant (ι := ι) χ ρ δ k R b A M γ*a^2 := by
  obtain ⟨η, hη, hh⟩ := FiniteSphereAsymptotics.finite_sphere_family p ρ χ δ R k b A M
    hρ hχ hδ hb hA hM hsep hinside f incident E hE hcenter hincident hdiff hder
  refine ⟨min η 1, lt_min hη zero_lt_one, ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d, hdr, hdc, he⟩ := hh a ha (had.trans_le (min_le_left _ _))
  refine ⟨d, hdr, hdc, he, ?_⟩
  intro i j
  exact inverse_from_estimates (p a) ρ a χ δ R k b A M γ ha hχ hγ (hheight a ha ha1)
    d (f a) (E a) he i j

end OQ14.StaticPlaneInclusions

#print axioms OQ14.StaticPlaneInclusions.ball_gap
#print axioms OQ14.StaticPlaneInclusions.material_gap
#print axioms OQ14.StaticPlaneInclusions.trial_gap
#print axioms OQ14.StaticPlaneInclusions.material_trial_plane_error
#print axioms OQ14.StaticPlaneInclusions.inverse_from_estimates
#print axioms OQ14.StaticPlaneInclusions.finite_sphere_family
