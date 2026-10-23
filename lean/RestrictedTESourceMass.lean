import RestrictedTEAsymptotics
import FiniteSphereSourceMass

/-! Actual source masses and plane gaps for the harmonic TE finite-ball inverse. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTESourceMass
open MeasureTheory Metric Set Maxwell PlaneSourceKernel MaxwellRadiation
open SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def source (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : Index →₀ ℂ) (a : ℝ) : Source :=
  DynamicVolume.source (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
    (RestrictedTEFiniteBalls.solution p ρ χ R b hρ hχ hi (fun a => (a : ℂ)⁻¹ • A) a)

def trial (p : ℝ → ι → Space) (ρ χ : ℝ) (A : Index →₀ ℂ) (a : ℝ) : Source :=
  FiniteSpherePlaneSources.trialSource (p a) (fun _ => ρ*a)
    (fun l => StaticSpherePolarization.polarization χ (electric ((a : ℂ)⁻¹ • A) (p a l)))

omit [DecidableEq ι] in
theorem source_actual (p : ℝ → ι → Space) (ρ χ R b : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : Index →₀ ℂ)
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) :
    source p ρ χ R b hρ hχ hi A a=
      DynamicVolume.source (FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ)
        (ParityMaterialField.solution (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1) 1 (b/a)
          (RestrictedTEAsymptotics.forcing p ρ χ R hρ hχ hi A a)) := by
  unfold source RestrictedTEFiniteBalls.solution RestrictedTEAsymptotics.forcing
  simp only [dif_pos (show 0<a ∧ a≤1 from ⟨ha,ha1⟩)]

theorem mass_and_gap (p : ℝ → ι → Space) (ρ χ δ R b γ : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hb : b≠0)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R)
    (hh : ∀ a, 0<a → a≤1 → ∀ l, (γ+ρ)*a≤|p a l 2|) (A : Index →₀ ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∃ M : ℝ, 0≤M ∧ ∃ η>0, ∀ a : ℝ, 0<a → a<η →
      Admissible R (γ*a) (source p ρ χ R b hρ hχ hi A a) ∧
      Admissible R (γ*a) (trial p ρ χ A a) ∧
      sourceMass (source p ρ χ R b hρ hχ hi A a)≤M*a^2 ∧
      sourceMass (trial p ρ χ A a)≤M*a^2 ∧
      sourceMass (source p ρ χ R b hρ hχ hi A a-trial p ρ χ A a)≤C*a^3 := by
  obtain ⟨C₀,hC₀,η,hη,hest⟩ := RestrictedTEAsymptotics.eventual_estimates p ρ χ δ R b hρ hχ hδ hb hsep hi A
  obtain ⟨L,hL,hbound⟩ := RestrictedTEScale.scaled_bounds A R
  let C := |FiniteSpherePlaneSources.errorConstant (ι := ι) χ ρ δ 1 R b C₀ C₀|
  let V := FiniteSphereSourceMass.trialConstant (ι := ι) χ ρ L
  have hC : 0≤C := abs_nonneg _
  have hV : 0≤V := by
    have hv := FiniteSphereScale.totalVolume_nonnegative (ι := ι) ρ hρ.le
    dsimp [V,FiniteSphereSourceMass.trialConstant]
    positivity
  refine ⟨C,hC,V+C,add_nonneg hV hC,η,hη,?_⟩
  intro a ha had
  obtain ⟨ha1,he⟩ := hest a ha had
  have hheight (l : ι) : γ*a+ρ*a≤|p a l 2| := by simpa only [add_mul] using hh a ha ha1 l
  have hinside (l : ι) : ‖p a l‖+ρ*a≤R :=
    (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hi a ha ha1 l)
  have hp (l : ι) : p a l∈closedBall (0 : Space) R := by
    simp only [mem_closedBall,dist_zero_right]
    linarith [hi a ha ha1 l]
  have hcenter (l : ι) (i : Fin 3) := (hbound a ha (p a l) (hp l) i).1
  have hs : Admissible R (γ*a) (source p ρ χ R b hρ hχ hi A a) :=
    RestrictedTEFiniteBalls.source_admissible p ρ χ R b (γ*a) a hρ hχ hi _ ha ha1 hheight
  have ht : Admissible R (γ*a) (trial p ρ χ A a) :=
    FiniteSpherePlaneSources.trial_admissible (p a) (fun _ => ρ*a) _ R (γ*a) hinside hheight
  have he' := FiniteSpherePlaneSources.inverse_source_mass (p a) ρ a χ δ R 1 b C₀ C₀ hχ
    (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1)
    (RestrictedTEAsymptotics.forcing p ρ χ R hρ hχ hi A a)
    (fun l => electric ((a : ℂ)⁻¹ • A) (p a l)) he
  rw [← source_actual p ρ χ R b hρ hχ hi A a ha ha1] at he'
  have herr : sourceMass (source p ρ χ R b hρ hχ hi A a-trial p ρ χ A a)≤C*a^3 :=
    he'.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hmU : sourceMass (trial p ρ χ A a)≤V*a^2 :=
    FiniteSphereSourceMass.trial_mass (p a) ρ a χ L hρ.le ha hχ _ hcenter
  have hmS : sourceMass (source p ρ χ R b hρ hχ hi A a)≤(V+C)*a^2 := by
    calc
      _ ≤ sourceMass (source p ρ χ R b hρ hχ hi A a-trial p ρ χ A a)+sourceMass (trial p ρ χ A a) :=
        sourceMass_le_sub_add _ _ hs.integrable ht.integrable
      _ ≤ C*a^3+V*a^2 := add_le_add herr hmU
      _ ≤ C*a^2+V*a^2 := add_le_add_right
        (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg a] : a^3≤a^2) hC) _
      _ = _ := by ring
  exact ⟨hs,ht,hmS,hmU.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) (sq_nonneg a)),herr⟩

end OQ14.RestrictedTESourceMass
#print axioms OQ14.RestrictedTESourceMass.source_actual
#print axioms OQ14.RestrictedTESourceMass.mass_and_gap
