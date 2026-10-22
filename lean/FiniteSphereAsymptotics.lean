import FiniteSphereSmallError

/-! # Constructed actual finite small-sphere source-error family

Actual center separation and enclosing geometry yield the support data and
all smallness conditions. Incident hypotheses concern actual local derivatives
and amplitudes; no source-response or Green convergence is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.FiniteSphereAsymptotics

open MeasureTheory Metric Set StaticBallNewton FiniteSphereStatic StaticSphereScale
  FiniteSphereSmallError ParityReactionVolume
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Estimates (p : ι → Space) (ρ a χ δ R k b A M : ℝ) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector) : Prop :=
  ‖ParityMaterialField.solution d k (b/a) f-trial p (fun _ => ρ*a) χ E‖ ≤
      errorConstant (ι := ι) χ ρ δ k R b A M*a*Real.sqrt a ∧
  ‖StaticCoefficient.sqrtMultiplier (coefficient p (fun _ => ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f)-
    sumSource p (fun _ => ρ*a) (fun j => StaticSpherePolarization.polarization χ (E j))‖ ≤
      Real.sqrt χ*errorConstant (ι := ι) χ ρ δ k R b A M*a*Real.sqrt a ∧
  ∀ m : Fin 3, (∫ x, ‖DynamicVolume.source (coefficient p (fun _ => ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f) m x-
    ∑ j : ι, (ball (p j) (ρ*a)).indicator
      (fun _ => StaticSpherePolarization.polarization χ (E j) m) x‖) ≤
      (Real.sqrt χ*errorConstant (ι := ι) χ ρ δ k R b A M*
        Real.sqrt (FiniteSphereScale.totalVolume (ι := ι) ρ))*a^3

theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b A M : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ i j, i ≠ j → δ ≤ dist (p a i) (p a j))
    (hinside : ∀ a, 0 < a → a ≤ 1 → ∀ j, ‖p a j‖+ρ ≤ R)
    (f : ℝ → VectorL2) (incident : ℝ → Maxwell.Field) (E : ℝ → ι → Vector)
    (hE : ∀ a, 0 < a → a ≤ 1 → ∀ j m, E a j m = incident a (p a j) m)
    (hcenter : ∀ a, 0 < a → a ≤ 1 → ∀ j m, ‖E a j m‖ ≤ A/a)
    (hincident : ∀ a, 0 < a → a ≤ 1 → ∀ m : Fin 3,
      (fun x => f a (VectorFourier.coordinateMap x) m) =ᵐ[volume]
        fun x => (Real.sqrt ((coefficient (p a) (fun _ => ρ*a) χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
          incident a x m)
    (hdiff : ∀ a, 0 < a → a ≤ 1 → ∀ j m, ∀ x ∈ ball (p a j) (ρ*a),
      DifferentiableAt ℝ (fun y => incident a y m) x)
    (hder : ∀ a, 0 < a → a ≤ 1 → ∀ j m, ∀ x ∈ ball (p a j) (ρ*a),
      ‖fderiv ℝ (fun y => incident a y m) x‖ ≤ M/a) :
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      ∃ d : BoundedMaterialKernel.SupportData (coefficient (p a) (fun _ => ρ*a) χ hχ),
        d.radius = R ∧ d.carrier = (⋃ j, ball (p a j) (ρ*a)) ∧
          Estimates (p a) ρ a χ δ R k b A M hχ d (f a) (E a) := by
  let V := FiniteSphereScale.totalVolume (ι := ι) ρ
  let K := linearBound χ V k R b
  have hK : 0 ≤ K := linearBound_nonnegative χ V k R b hχ
    (FiniteSphereScale.totalVolume_nonnegative ρ hρ.le)
  obtain ⟨η, hη, hh⟩ := linear_smallness K hK
  refine ⟨min η (min 1 (δ/(4*ρ))), lt_min hη (lt_min zero_lt_one (by positivity)), ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hgeom : a < δ/(4*ρ) := had.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hrad : ρ*a ≤ δ/4 := by
    have he := (lt_div_iff₀ (by positivity : 0 < 4*ρ)).mp hgeom
    linarith
  have hi : ∀ j, ‖p a j‖+ρ*a ≤ R := fun j =>
    (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hinside a ha ha1 j)
  have hs : K*a ≤ 1/2 := (hh a ha.le (had.trans_le (min_le_left _ _))).le
  let d := FiniteSphereStatic.supportData (p a) (fun _ => ρ*a) χ hχ R hi
  have he := weighted_error_scaled (p a) ρ a χ δ R k b A M hρ ha ha1 hχ hδ hb hA hM hrad
    (hsep a ha ha1) hi d rfl rfl hs (f a) (incident a) (E a) (hE a ha ha1) (hcenter a ha ha1)
    (hincident a ha ha1) (hdiff a ha ha1) (hder a ha ha1)
  have hp := physical_errors_of_weighted (p a) (fun _ => ρ*a) χ hχ (E a) d
    (ParityMaterialField.solution d k (b/a) (f a))
    (errorConstant (ι := ι) χ ρ δ k R b A M*a*Real.sqrt a) he
  refine ⟨d, rfl, rfl, he, ?_, ?_⟩
  · exact hp.1.trans_eq (by ring)
  · intro m
    apply (hp.2 m).trans
    have hpos : 0 ≤ errorConstant (ι := ι) χ ρ δ k R b A M*a*Real.sqrt a :=
      (norm_nonneg _).trans he
    apply (mul_le_mul_of_nonneg_left (FiniteSphereScale.sqrt_union_volume_bound (p a) ρ a hρ.le ha.le)
      (mul_nonneg (Real.sqrt_nonneg _) hpos)).trans_eq
    change (Real.sqrt χ*(errorConstant (ι := ι) χ ρ δ k R b A M*a*Real.sqrt a))*
      (Real.sqrt V*a*Real.sqrt a) = (Real.sqrt χ*errorConstant (ι := ι) χ ρ δ k R b A M*Real.sqrt V)*a^3
    linear_combination (Real.sqrt χ*errorConstant (ι := ι) χ ρ δ k R b A M*Real.sqrt V*a^2)*
      (Real.sq_sqrt ha.le)

end OQ14.FiniteSphereAsymptotics

#print axioms OQ14.FiniteSphereAsymptotics.finite_sphere_family
