import FiniteSpherePlaneSources
import SourceHerglotzFiniteMoving

/-! Actual finite-ball inverse sources satisfy the derived whole-plane coherent error bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereCoherentError
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation SourceHerglotzLocal
open FiniteSpherePlaneSources (trialSource)
open scoped ComplexConjugate Topology
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

def CoherentEstimates (p : ι → Space) (ρ a χ δ R k b A M γ T A₀ : ℝ) (hχ : 0 ≤ χ)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (f : VectorL2) (E : ι → Vector) : Prop :=
  let physical := DynamicVolume.source (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ)
    (ParityMaterialField.solution d k (b/a) f)
  let trial := trialSource p (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ (E l))
  ∀ (e : κ → Bool) (q : κ → Space) (j : κ → Fin 3) (B : κ → ℂ),
    (∀ s, q s ∈ closedBall (0 : Space) R) → (∑ s, ‖B s‖) ≤ A₀/a →
    (∫ u : Plane, ‖SourceHerglotzFinite.electricMixed k physical e q j B u-
      SourceHerglotzFinite.electricMixed k trial e q j B u‖) ≤
      (FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M*A₀)*
        (SourceHerglotzWhole.electricConstant k R T (γ*a)*a^2) ∧
    (∫ u : Plane, ‖SourceHerglotzFinite.magneticMixed k physical e q j B u-
      SourceHerglotzFinite.magneticMixed k trial e q j B u‖) ≤
      (FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b A M*A₀)*
        (SourceHerglotzWhole.magneticConstant k R T (γ*a)*a^2)
theorem inverse_from_estimates (p : ι → Space) (ρ a χ δ R k b A M γ T A₀ : ℝ)
    (ha : 0 < a) (hχ : 0 ≤ χ) (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hdM : γ*a ≤ T+R) (hA₀ : 0 ≤ A₀)
    (hinside : ∀ l, ‖p l‖+ρ*a ≤ R) (hheight : ∀ l, γ*a+ρ*a ≤ |p l 2|)
    (d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient p (fun _ => ρ*a) χ hχ))
    (hdr : d.radius=R) (f : VectorL2) (E : ι → Vector)
    (he : FiniteSphereAsymptotics.Estimates p ρ a χ δ R k b A M hχ d f E) :
    CoherentEstimates (κ := κ) p ρ a χ δ R k b A M γ T A₀ hχ d f E := by
  have hp := FiniteSpherePlaneSources.material_admissible p (fun _ => ρ*a) χ R (γ*a) hχ d hdr hheight
    (ParityMaterialField.solution d k (b/a) f)
  have ht := FiniteSpherePlaneSources.trial_admissible p (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ (E l)) R (γ*a) hinside hheight
  have hm := FiniteSpherePlaneSources.inverse_source_mass p ρ a χ δ R k b A M hχ d f E he
  intro e q j B hq hB
  constructor
  · exact SourceHerglotzFiniteMoving.electric_bound k R T γ _ A₀ a hR hγ ha hk hT hTR hA₀ _ _ hp ht e q j B hq hB hm
  · exact SourceHerglotzFiniteMoving.magnetic_bound k R T γ _ A₀ a hR hγ ha hk hT hTR hA₀ hdM _ _ hp ht e q j B hq hB hm
theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b A M γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0) (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
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
      ∃ d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ),
        d.radius=R ∧ d.carrier=(⋃ l, ball (p a l) (ρ*a)) ∧
          FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R k b A M hχ d (f a) (E a) ∧
          CoherentEstimates (κ := κ) (p a) ρ a χ δ R k b A M γ T A₀ hχ d (f a) (E a) := by
  obtain ⟨η,hη,hbase⟩ := FiniteSphereAsymptotics.finite_sphere_family p ρ χ δ R k b A M
    hρ hχ hδ hb hA hM hsep hinside f incident E hE hcenter hincident hdiff hder
  have hMpos : 0 < T+R := by linarith
  refine ⟨min (min η 1) ((T+R)/γ), lt_min (lt_min hη zero_lt_one) (div_pos hMpos hγ), ?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le ((min_le_left _ _).trans (min_le_right η 1))).le
  have haη : a < η := had.trans_le ((min_le_left _ _).trans (min_le_left η 1))
  have haM : a < (T+R)/γ := had.trans_le (min_le_right _ _)
  have hdM : γ*a ≤ T+R := by have hh := (lt_div_iff₀ hγ).mp haM; nlinarith
  obtain ⟨d,hdr,hdc,he⟩ := hbase a ha haη
  refine ⟨d,hdr,hdc,he,?_⟩
  apply inverse_from_estimates (p a) ρ a χ δ R k b A M γ T A₀ ha hχ hR hk hγ hT hTR hdM hA₀
    (fun l => ?_) (fun l => ?_) d hdr (f a) (E a) he
  · have hh := hinside a ha ha1 l
    have hr : ρ*a ≤ ρ := mul_le_of_le_one_right hρ.le ha1
    linarith
  · simpa only [add_mul] using hheight a ha ha1 l

end OQ14.FiniteSphereCoherentError
#print axioms OQ14.FiniteSphereCoherentError.inverse_from_estimates
#print axioms OQ14.FiniteSphereCoherentError.finite_sphere_family
