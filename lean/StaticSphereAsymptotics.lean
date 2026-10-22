import StaticSphereSmallError

/-! # Constructed small-sphere family for the literal parity-kernel inverse

The material, its geometric support data, and eventual perturbation smallness
are constructed. The remaining incident assumptions describe actual local
derivatives and center amplitudes, not the desired source convergence.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2500000

namespace OQ14.StaticSphereAsymptotics

open MeasureTheory Metric Set StaticBallNewton StaticSphereMaterial StaticSphereScale
  StaticSphereResidual StaticSphereSmallError ParityReactionVolume
open scoped Topology

def supportData (p : Space) (r χ : ℝ) (hχ : 0 ≤ χ) (R : ℝ)
    (hinside : ‖p‖+r ≤ R) : SupportData (coefficient p r χ hχ) := by
  classical
  refine ⟨R, ball p r, measurableSet_ball, measure_ball_lt_top.ne, ?_, ?_⟩
  · intro x hx
    rw [coefficient_value]
    apply if_neg
    intro hm
    apply hx
    simp only [mem_closedBall, dist_zero_right]
    have hh : ‖x-p‖ < r := by simpa only [mem_ball, dist_eq_norm] using hm
    have ht := norm_add_le (x-p) p
    rw [sub_add_cancel] at ht
    linarith
  · intro x hx
    rw [coefficient_value, if_neg hx]

def Estimates (p : Space) (ρ a χ R k b A M : ℝ) (hχ : 0 ≤ χ)
    (d : SupportData (coefficient p (ρ*a) χ hχ)) (f : VectorL2) (E : Vector) : Prop :=
  ‖ParityMaterialField.solution d k (b/a) f-trial p (ρ*a) χ E‖ ≤
      errorConstant χ ρ k R b A M*a*Real.sqrt a ∧
  ‖StaticCoefficient.sqrtMultiplier (coefficient p (ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f)-
    StaticBallCentered.source p (ρ*a) (StaticSpherePolarization.polarization χ E)‖ ≤
      Real.sqrt χ*errorConstant χ ρ k R b A M*a*Real.sqrt a ∧
  ∀ i : Fin 3, (∫ x, ‖DynamicVolume.source (coefficient p (ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f) i x -
    (ball p (ρ*a)).indicator (fun _ => StaticSpherePolarization.polarization χ E i) x‖) ≤
      (Real.sqrt χ*errorConstant χ ρ k R b A M*Real.sqrt (volumeConstant ρ))*a^3

/-- Actual small-sphere source errors, with geometric data and inverse
smallness derived for all sufficiently small radii. -/
theorem single_sphere_family (p : Space) (ρ χ R k b A M : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hb : b ≠ 0) (hM : 0 ≤ M) (hinside : ‖p‖+ρ ≤ R)
    (f : ℝ → VectorL2) (incident : ℝ → Maxwell.Field) (E : ℝ → Vector)
    (hE : ∀ a, 0 < a → a ≤ 1 → ∀ i, E a i = incident a p i)
    (hcenter : ∀ a, 0 < a → a ≤ 1 → ∀ i : Fin 3, ‖E a i‖ ≤ A/a)
    (hincident : ∀ a, 0 < a → a ≤ 1 → ∀ i : Fin 3,
      (fun x => f a (VectorFourier.coordinateMap x) i) =ᵐ[volume]
        fun x => (Real.sqrt ((coefficient p (ρ*a) χ hχ).value (VectorFourier.coordinateMap x)) : ℂ)*
          incident a x i)
    (hdiff : ∀ a, 0 < a → a ≤ 1 → ∀ i : Fin 3, ∀ x ∈ ball p (ρ*a),
      DifferentiableAt ℝ (fun y => incident a y i) x)
    (hder : ∀ a, 0 < a → a ≤ 1 → ∀ i : Fin 3, ∀ x ∈ ball p (ρ*a),
      ‖fderiv ℝ (fun y => incident a y i) x‖ ≤ M/a) :
    ∃ δ > 0, ∀ a : ℝ, 0 < a → a < δ →
      ∃ d : SupportData (coefficient p (ρ*a) χ hχ),
        d.radius = R ∧ d.carrier = ball p (ρ*a) ∧ Estimates p ρ a χ R k b A M hχ d (f a) (E a) := by
  let K := linearBound χ (volumeConstant ρ) k R b
  have hK : 0 ≤ K := linearBound_nonnegative χ (volumeConstant ρ) k R b hχ
    (volumeConstant_nonnegative ρ hρ.le)
  obtain ⟨δ, hδ, hh⟩ := linear_smallness K hK
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  have hs : K*a ≤ 1/2 := (hh a ha.le (had.trans_le (min_le_left _ _))).le
  have hi : ‖p‖+ρ*a ≤ R :=
    (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans hinside
  let d := supportData p (ρ*a) χ hχ R hi
  refine ⟨d, rfl, rfl, ?_⟩
  exact source_errors_scaled p ρ a χ R k b A M hρ ha ha1 hχ hb hM d rfl rfl hs
    (f a) (incident a) (E a) (hE a ha ha1) (hcenter a ha ha1) (hincident a ha ha1)
    (hdiff a ha ha1) (hder a ha ha1)

end OQ14.StaticSphereAsymptotics

#print axioms OQ14.StaticSphereAsymptotics.supportData
#print axioms OQ14.StaticSphereAsymptotics.single_sphere_family
