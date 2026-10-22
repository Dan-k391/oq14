import FiniteSphereIllumination
import FiniteSphereSourceMass
import PlaneQuadraticMoving

/-! Actual finite-ball inverse quadratic flux error, with literal finite parity illumination. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereQuadratic
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open FiniteSpherePlaneSources (trialSource)
open SphereReactionKernel (entryBound)
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def massConstant (χ ρ δ k R b A M : ℝ) : ℝ :=
  FiniteSphereSourceMass.trialConstant (ι := ι) χ ρ A+
    |FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M|

def QuadraticEstimates (p : ι → Space) (ρ a χ δ R k b A M γ T : ℝ) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector) : Prop :=
  let physical := DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f)
  let trial := trialSource p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l))
  (∫ q : Plane, ‖MaxwellPlaneL1.flux k physical physical q-MaxwellPlaneL1.flux k trial trial q‖) ≤
    (2*|FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M| *
      massConstant (ι := ι) χ ρ δ k R b A M)*(PlaneQuadraticFlux.wholeConstant k R T (γ*a)*a^5)

theorem inverse_from_estimates (p : ι → Space) (ρ a χ δ R k b A M γ T : ℝ)
    (hρ : 0 ≤ ρ) (ha : 0 < a) (ha1 : a ≤ 1) (hχ : 0 ≤ χ) (hA : 0 ≤ A)
    (hR : 0 ≤ R) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T)
    (hinside : ∀ l, ‖p l‖+ρ*a ≤ R) (hheight : ∀ l, γ*a+ρ*a ≤ |p l 2|)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (hdr : d.radius=R) (f : VectorL2) (E : ι → Vector) (hE : ∀ l j, ‖E l j‖ ≤ A/a)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E) :
    QuadraticEstimates p ρ a χ δ R k b A M γ T hχ d f E := by
  have hp := FiniteSpherePlaneSources.material_admissible p (fun _ => ρ*a) χ R (γ*a) hχ d hdr hheight
    (ParityMaterialField.solution d k (b/a) f)
  have ht := FiniteSpherePlaneSources.trial_admissible p (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ (E l)) R (γ*a) hinside hheight
  have hmρ := FiniteSphereSourceMass.inverse_mass p ρ a χ δ R k b A M hρ ha ha1 hχ d f E hE he
  have hmσ := FiniteSphereSourceMass.trial_mass p ρ a χ A hρ ha hχ E hE
  have htrial : 0 ≤ FiniteSphereSourceMass.trialConstant (ι := ι) χ ρ A := by
    have hV := FiniteSphereScale.totalVolume_nonnegative (ι := ι) ρ hρ
    unfold FiniteSphereSourceMass.trialConstant
    positivity
  have hmass : 0 ≤ massConstant (ι := ι) χ ρ δ k R b A M := add_nonneg htrial (abs_nonneg _)
  have hmσ' := hmσ.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (abs_nonneg (FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M))) (sq_nonneg a))
  have herr := (FiniteSpherePlaneSources.inverse_source_mass p ρ a χ δ R k b A M hχ d f E he).trans
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  exact PlaneQuadraticMoving.self_difference_bound k R T γ _ _ a hR hγ ha hT hTR (abs_nonneg _) hmass
    _ _ hp ht hmρ hmσ' herr

theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hinside : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hheight : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (e : ℝ → κ → Bool) (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (hA : ∀ a, 0 < a → a ≤ 1 → (∑ s, ‖A a s‖) ≤ A₀/a) :
    let f := FiniteSphereIllumination.datum p ρ χ R k hρ hχ hinside e q j A
    let E := fun a l i => FiniteHerglotzFlux.electric k (e a) (q a) (j a) (A a) (p a l) i
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      ∃ d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ),
        d.radius=R ∧ d.carrier=(⋃ l, ball (p a l) (ρ*a)) ∧
          FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R k b
            (entryBound k*A₀) (2*entryBound k*|k| * A₀) hχ d (f a) (E a) ∧
          FiniteSphereCoherentError.CoherentEstimates (κ := κ) (p a) ρ a χ δ R k b
            (entryBound k*A₀) (2*entryBound k*|k| * A₀) γ T A₀ hχ d (f a) (E a) ∧
          QuadraticEstimates (p a) ρ a χ δ R k b
            (entryBound k*A₀) (2*entryBound k*|k| * A₀) γ T hχ d (f a) (E a) := by
  obtain ⟨η,hη,hh⟩ := FiniteSphereIllumination.finite_sphere_family p ρ χ δ R k b γ T A₀
    hρ hχ hδ hb hR hk hγ hT hTR hA₀ hsep hinside hheight e q j A hA
  refine ⟨min η 1,lt_min hη zero_lt_one,?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d,hdr,hdc,he,hcoh⟩ := hh a ha (had.trans_le (min_le_left _ _))
  refine ⟨d,hdr,hdc,he,hcoh,?_⟩
  apply inverse_from_estimates (p a) ρ a χ δ R k b _ _ γ T hρ.le ha ha1 hχ
    (mul_nonneg (SphereReactionKernel.entryBound_nonnegative k) hA₀) hR hγ hT hTR
    (fun l => ?_) (fun l => ?_) d hdr _ _ (fun l i => ?_) he
  · exact (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hinside a ha ha1 l)
  · simpa only [add_mul] using hheight a ha ha1 l
  · exact (FiniteSphereIncident.electric_scaled_bounds k a A₀ (e a) (q a) (j a) (A a) (hA a ha ha1) (p a l) i).1

end OQ14.FiniteSphereQuadratic
#print axioms OQ14.FiniteSphereQuadratic.inverse_from_estimates
#print axioms OQ14.FiniteSphereQuadratic.finite_sphere_family
