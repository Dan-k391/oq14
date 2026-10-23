import FiniteSphereIncident
import FiniteSphereCoherentError

/-! Actual finite Herglotz fields supply the small-sphere incident datum and all local bounds. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereIllumination
open MeasureTheory Metric Set
open FiniteHerglotzFlux (electric)
open SphereReactionKernel (entryBound entryBound_nonnegative)
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] in
private theorem inside_scaled (p : ℝ → ι → Space) (ρ R : ℝ) (hρ : 0 < ρ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : ∀ l, ‖p a l‖+ρ*a ≤ R :=
  fun l => (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hi a ha ha1 l)

def datum (p : ℝ → ι → Space) (ρ χ R k : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (e : ℝ → κ → Bool) (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (a : ℝ) : VectorL2 :=
  if ha : 0 < a ∧ a ≤ 1 then
    FiniteSphereIncident.datum (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
      k R (e a) (q a) (j a) (A a)
      (FiniteSphereStatic.supportData (p a) (fun _ => ρ*a) χ hχ R
        (inside_scaled p ρ R hρ hi a ha.1 ha.2)).ballZero
  else 0

omit [DecidableEq ι] in
theorem datum_actual (p : ℝ → ι → Space) (ρ χ R k : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (e : ℝ → κ → Bool) (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (i : Fin 3) :
    (fun x => datum p ρ χ R k hρ hχ hi e q j A a (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ).value
        (VectorFourier.coordinateMap x)) : ℂ)*electric k (e a) (q a) (j a) (A a) x i := by
  unfold datum
  rw [dif_pos ⟨ha,ha1⟩]
  exact FiniteSphereIncident.datum_actual _ k R (e a) (q a) (j a) (A a) _ i

theorem finite_sphere_family (p : ℝ → ι → Space) (ρ χ δ R k b γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hinside : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hheight : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (e : ℝ → κ → Bool) (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (hA : ∀ a, 0 < a → a ≤ 1 → (∑ s, ‖A a s‖) ≤ A₀/a) :
    let f := datum p ρ χ R k hρ hχ hinside e q j A
    let E := fun a l i => electric k (e a) (q a) (j a) (A a) (p a l) i
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      ∃ d : BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ),
        d.radius=R ∧ d.carrier=(⋃ l, ball (p a l) (ρ*a)) ∧
          FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R k b
            (entryBound k*A₀) (2*entryBound k*|k| * A₀) hχ d (f a) (E a) ∧
          FiniteSphereCoherentError.CoherentEstimates (κ := κ) (p a) ρ a χ δ R k b
            (entryBound k*A₀) (2*entryBound k*|k| * A₀) γ T A₀ hχ d (f a) (E a) := by
  dsimp only
  apply FiniteSphereCoherentError.finite_sphere_family p ρ χ δ R k b
    (entryBound k*A₀) (2*entryBound k*|k| * A₀) γ T A₀ hρ hχ hδ hb
    (mul_nonneg (entryBound_nonnegative k) hA₀)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (entryBound_nonnegative k)) (abs_nonneg k)) hA₀)
    hR hk hγ hT hTR hA₀ hsep hinside hheight
    (datum p ρ χ R k hρ hχ hinside e q j A)
    (fun a => electric k (e a) (q a) (j a) (A a)) _
  · intro a ha ha1 l i
    rfl
  · intro a ha ha1 l i
    exact (FiniteSphereIncident.electric_scaled_bounds k a A₀ (e a) (q a) (j a) (A a)
      (hA a ha ha1) (p a l) i).1
  · intro a ha ha1 i
    exact datum_actual p ρ χ R k hρ hχ hinside e q j A a ha ha1 i
  · intro a ha ha1 l i x hx
    exact FiniteSphereMaxwell.electric_differentiable k (e a) (q a) (j a) (A a) x i
  · intro a ha ha1 l i x hx
    exact (FiniteSphereIncident.electric_scaled_bounds k a A₀ (e a) (q a) (j a) (A a)
      (hA a ha ha1) x i).2

end OQ14.FiniteSphereIllumination
#print axioms OQ14.FiniteSphereIllumination.datum_actual
#print axioms OQ14.FiniteSphereIllumination.finite_sphere_family
