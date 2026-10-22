import FiniteSphereIllumination
import FiniteSphereQuadratic

/-! Literal inverse source families on actual shrinking finite balls. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereActualSources
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation
open SphereReactionKernel (entryBound)
abbrev Space := FourierL2.Space
abbrev Vector := StaticBallNewton.Vector
abbrev VectorL2 := VectorFourier.VectorL2

theorem support_ext {c : StaticCoefficient.Coefficient} (d d' : BoundedMaterialKernel.SupportData c)
    (hr : d.radius=d'.radius) (hc : d.carrier=d'.carrier) : d=d' := by
  rcases d with ⟨r,s,hs,hf,hb,hz⟩
  rcases d' with ⟨r',s',hs',hf',hb',hz'⟩
  dsimp only at hr hc
  subst r'
  subst s'
  rfl

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [Fintype ι] [DecidableEq ι] in
private theorem inside_scaled (p : ℝ → ι → Space) (ρ R : ℝ) (hρ : 0 < ρ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) : ∀ l, ‖p a l‖+ρ*a ≤ R :=
  fun l => (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hi a ha ha1 l)

def data (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    BoundedMaterialKernel.SupportData (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ) :=
  FiniteSphereStatic.supportData (p a) (fun _ => ρ*a) χ hχ R (inside_scaled p ρ R hρ hi a ha ha1)

def solution (p : ℝ → ι → Space) (ρ χ R k b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ) (a : ℝ) : VectorL2 :=
  if ha : 0 < a ∧ a ≤ 1 then
    ParityMaterialField.solution (data p ρ χ R hρ hχ hi a ha.1 ha.2) k (b/a)
      (FiniteSphereIllumination.datum p ρ χ R k hρ hχ hi (fun _ _ => true) q j A a)
  else 0

def source (p : ℝ → ι → Space) (ρ χ R k b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ) (a : ℝ) : Source :=
  DynamicVolume.source (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
    (solution p ρ χ R k b hρ hχ hi q j A a)

def trial (p : ℝ → ι → Space) (ρ χ k : ℝ)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ) (a : ℝ) : Source :=
  FiniteSpherePlaneSources.trialSource (p a) (fun _ => ρ*a) (fun l => StaticSpherePolarization.polarization χ
    (fun i => FiniteHerglotzFlux.electric k (fun _ => true) (q a) (j a) (A a) (p a l) i))

omit [DecidableEq ι] in
theorem source_actual (p : ℝ → ι → Space) (ρ χ R k b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    source p ρ χ R k b hρ hχ hi q j A a=
      DynamicVolume.source (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution (data p ρ χ R hρ hχ hi a ha ha1) k (b/a)
          (FiniteSphereIllumination.datum p ρ χ R k hρ hχ hi (fun _ _ => true) q j A a)) := by
  unfold source solution
  rw [dif_pos ⟨ha,ha1⟩]

theorem eventual_estimates (p : ℝ → ι → Space) (ρ χ δ R k b γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hh : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (hA : ∀ a, 0 < a → a ≤ 1 → (∑ s, ‖A a s‖) ≤ A₀/a) :
    ∃ η > 0, ∀ a : ℝ, ∀ ha : 0 < a, a < η → ∃ ha1 : a ≤ 1,
      FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R k b (entryBound k*A₀) (2*entryBound k*|k| * A₀)
        hχ (data p ρ χ R hρ hχ hi a ha ha1)
        (FiniteSphereIllumination.datum p ρ χ R k hρ hχ hi (fun _ _ => true) q j A a)
        (fun l i => FiniteHerglotzFlux.electric k (fun _ => true) (q a) (j a) (A a) (p a l) i) := by
  obtain ⟨η,hη,he⟩ := FiniteSphereIllumination.finite_sphere_family p ρ χ δ R k b γ T A₀
    hρ hχ hδ hb hR hk hγ hT hTR hA₀ hsep hi hh (fun _ _ => true) q j A hA
  refine ⟨min η 1,lt_min hη zero_lt_one,?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d,hdr,hdc,hest,_⟩ := he a ha (had.trans_le (min_le_left _ _))
  have hd : d=data p ρ χ R hρ hχ hi a ha ha1 := support_ext d _ hdr hdc
  rw [hd] at hest
  exact ⟨ha1,hest⟩

theorem mass_and_gap (p : ℝ → ι → Space) (ρ χ δ R k b γ T A₀ : ℝ)
    (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hδ : 0 < δ) (hb : b ≠ 0)
    (hR : 0 ≤ R) (hk : k ≠ 0) (hγ : 0 < γ) (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hA₀ : 0 ≤ A₀)
    (hsep : ∀ a, 0 < a → a ≤ 1 → ∀ l n, l ≠ n → δ ≤ dist (p a l) (p a n))
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (hh : ∀ a, 0 < a → a ≤ 1 → ∀ l, (γ+ρ)*a ≤ |p a l 2|)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ)
    (hA : ∀ a, 0 < a → a ≤ 1 → (∑ s, ‖A a s‖) ≤ A₀/a) :
    let S := source p ρ χ R k b hρ hχ hi q j A
    let U := trial p ρ χ k q j A
    let C := |FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b (entryBound k*A₀) (2*entryBound k*|k| * A₀)|
    let M := FiniteSphereQuadratic.massConstant (ι := ι) χ ρ δ k R b (entryBound k*A₀) (2*entryBound k*|k| * A₀)
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      Admissible R (γ*a) (S a) ∧ Admissible R (γ*a) (U a) ∧
      sourceMass (S a) ≤ M*a^2 ∧ sourceMass (U a) ≤ M*a^2 ∧ sourceMass (S a-U a) ≤ C*a^3 := by
  obtain ⟨η,hη,he⟩ := eventual_estimates p ρ χ δ R k b γ T A₀ hρ hχ hδ hb hR hk hγ hT hTR hA₀ hsep hi hh q j A hA
  refine ⟨η,hη,?_⟩
  intro a ha had
  obtain ⟨ha1,hest⟩ := he a ha had
  rw [source_actual p ρ χ R k b hρ hχ hi q j A a ha ha1]
  have hcent (l : ι) (i : Fin 3) := (FiniteSphereIncident.electric_scaled_bounds k a A₀
    (fun _ => true) (q a) (j a) (A a) (hA a ha ha1) (p a l) i).1
  have hheight (l : ι) : γ*a+ρ*a ≤ |p a l 2| := by simpa only [add_mul] using hh a ha ha1 l
  have hinside := inside_scaled p ρ R hρ hi a ha ha1
  have hp := FiniteSpherePlaneSources.material_admissible (p a) (fun _ => ρ*a) χ R (γ*a) hχ
    (data p ρ χ R hρ hχ hi a ha ha1) rfl hheight
    (ParityMaterialField.solution (data p ρ χ R hρ hχ hi a ha ha1) k (b/a)
      (FiniteSphereIllumination.datum p ρ χ R k hρ hχ hi (fun _ _ => true) q j A a))
  have ht := FiniteSpherePlaneSources.trial_admissible (p a) (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ
      (fun i => FiniteHerglotzFlux.electric k (fun _ => true) (q a) (j a) (A a) (p a l) i)) R (γ*a) hinside hheight
  have hmS := FiniteSphereSourceMass.inverse_mass (p a) ρ a χ δ R k b _ _ hρ.le ha ha1 hχ _ _ _ hcent hest
  have hmU := FiniteSphereSourceMass.trial_mass (p a) ρ a χ _ hρ.le ha hχ _ hcent
  have hmU' := hmU.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg (FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ k R b
      (entryBound k*A₀) (2*entryBound k*|k| * A₀)))) (sq_nonneg a))
  have herr := (FiniteSpherePlaneSources.inverse_source_mass (p a) ρ a χ δ R k b _ _ hχ _ _ _ hest).trans
    (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  exact ⟨hp,ht,hmS,hmU',herr⟩

end OQ14.FiniteSphereActualSources
#print axioms OQ14.FiniteSphereActualSources.support_ext
#print axioms OQ14.FiniteSphereActualSources.source_actual
#print axioms OQ14.FiniteSphereActualSources.eventual_estimates
#print axioms OQ14.FiniteSphereActualSources.mass_and_gap
