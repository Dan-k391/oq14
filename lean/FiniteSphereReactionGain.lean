import ReactionGainError

/-! Actual gain-amplified parity reaction fields compared with finite dipoles. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.FiniteSphereReactionGain

open MeasureTheory Metric SphereReactionKernel
open scoped Topology

abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def gainedPointField (k B : ℝ) (p : ι → Space) (r : ι → ℝ) (P : ι → Vector)
    (x : Space) (i : Fin 3) : ℂ :=
  ((B^2-1 : ℝ) : ℂ)*FiniteSphereReactionScale.pointField true k p r P x i+
    ((B⁻¹^2-1 : ℝ) : ℂ)*FiniteSphereReactionScale.pointField false k p r P x i

def gainedReaction (c : StaticCoefficient.Coefficient) (k B : ℝ) (u : VectorL2)
    (x : Space) (i : Fin 3) : ℂ :=
  ((B^2-1 : ℝ) : ℂ)*ParityMaterialField.reaction c true k u x i+
    ((B⁻¹^2-1 : ℝ) : ℂ)*ParityMaterialField.reaction c false k u x i

theorem gained_from_estimates (p : ι → Space) (ρ a χ δ R k b A M : ℝ)
    (hρ : 0 ≤ ρ) (ha : 0 < a) (ha1 : a ≤ 1) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector) (hE : ∀ l j, ‖E l j‖ ≤ A/a)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E)
    (x : Space) (i : Fin 3) :
    ‖gainedReaction (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ) k (b/a)
      (ParityMaterialField.solution d k (b/a) f) x i-
      gainedPointField k (b/a) p (fun _ => ρ*a)
        (fun l => StaticSpherePolarization.polarization χ (E l)) x i‖ ≤
      (b^2+2+1/b^2)*FiniteSphereReactionScale.errorConstant (ι := ι) χ ρ δ k R b A M*a := by
  have htrue := FiniteSphereReactionScale.reaction_from_estimates p ρ a χ δ R k b A M
    hρ ha hχ d f E hE he true x i
  have hfalse := FiniteSphereReactionScale.reaction_from_estimates p ρ a χ δ R k b A M
    hρ ha hχ d f E hE he false x i
  have hh := ReactionGainError.combined_error b a _ ha ha1 _ _ htrue hfalse
  convert hh using 1
  unfold gainedReaction gainedPointField
  congr 1
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
          ∀ (x : Space) (i : Fin 3),
            ‖gainedReaction (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
                k (b/a) (ParityMaterialField.solution d k (b/a) (f a)) x i-
              gainedPointField k (b/a) (p a) (fun _ => ρ*a)
                (fun l => StaticSpherePolarization.polarization χ (E a l)) x i‖ ≤
              (b^2+2+1/b^2)*FiniteSphereReactionScale.errorConstant (ι := ι) χ ρ δ k R b A M*a := by
  obtain ⟨η, hη, hh⟩ := FiniteSphereAsymptotics.finite_sphere_family p ρ χ δ R k b A M
    hρ hχ hδ hb hA hM hsep hinside f incident E hE hcenter hincident hdiff hder
  refine ⟨min η 1, lt_min hη zero_lt_one, ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d, hdr, hdc, he⟩ := hh a ha (had.trans_le (min_le_left _ _))
  refine ⟨d, hdr, hdc, he, ?_⟩
  intro x i
  exact gained_from_estimates (p a) ρ a χ δ R k b A M hρ.le ha ha1 hχ d (f a) (E a)
    (hcenter a ha ha1) he x i

end OQ14.FiniteSphereReactionGain

#print axioms OQ14.FiniteSphereReactionGain.gained_from_estimates
#print axioms OQ14.FiniteSphereReactionGain.finite_sphere_family
