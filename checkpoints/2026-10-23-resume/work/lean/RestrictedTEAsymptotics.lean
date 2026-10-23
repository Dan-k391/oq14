import RestrictedTEScale
import RestrictedTEFiniteBalls

/-! Actual scaled harmonic TE forcing discharges the finite-ball source asymptotics. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEAsymptotics
open MeasureTheory Metric Set Maxwell SymmetricHarmonicJets RestrictedTEPlaneLocal
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def forcing (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : Index →₀ ℂ) (a : ℝ) : VectorFourier.VectorL2 :=
  if ha : 0<a ∧ a≤1 then
    let d := FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha.1 ha.2
    RestrictedTEMaterial.datum _ d ((a : ℂ)⁻¹ • A)
  else 0

omit [DecidableEq ι] in
theorem forcing_actual (p : ℝ → ι → Space) (ρ χ R : ℝ) (hρ : 0<ρ) (hχ : 0≤χ)
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : Index →₀ ℂ)
    (a : ℝ) (ha : 0<a) (ha1 : a≤1) (i : Fin 3) :
    (fun x => forcing p ρ χ R hρ hχ hi A a (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ).value
        (VectorFourier.coordinateMap x)) : ℂ)*electric ((a : ℂ)⁻¹ • A) x i := by
  unfold forcing
  rw [dif_pos ⟨ha,ha1⟩]
  exact RestrictedTEMaterial.datum_actual _ _ _ i

theorem eventual_estimates (p : ℝ → ι → Space) (ρ χ δ R b : ℝ)
    (hρ : 0<ρ) (hχ : 0≤χ) (hδ : 0<δ) (hb : b≠0)
    (hsep : ∀ a, 0<a → a≤1 → ∀ i j, i≠j → δ≤dist (p a i) (p a j))
    (hi : ∀ a, 0<a → a≤1 → ∀ l, ‖p a l‖+ρ≤R) (A : Index →₀ ℂ) :
    ∃ C : ℝ, 0≤C ∧ ∃ η>0, ∀ a : ℝ, ∀ ha : 0<a, a<η → ∃ ha1 : a≤1,
      FiniteSphereAsymptotics.Estimates (p a) ρ a χ δ R 1 b C C hχ
        (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1)
        (forcing p ρ χ R hρ hχ hi A a)
        (fun l i => electric ((a : ℂ)⁻¹ • A) (p a l) i) := by
  obtain ⟨C,hC,hbound⟩ := RestrictedTEScale.scaled_bounds A R
  have hp (a : ℝ) (ha : 0<a) (ha1 : a≤1) (j : ι) : p a j∈closedBall (0 : Space) R := by
    simp only [mem_closedBall,dist_zero_right]
    linarith [hi a ha ha1 j]
  have hball (a : ℝ) (ha : 0<a) (ha1 : a≤1) (j : ι) (x : Space)
      (hx : x∈ball (p a j) (ρ*a)) : x∈closedBall (0 : Space) R := by
    have hs : ‖p a j‖+ρ*a≤R :=
      (add_le_add_left (mul_le_of_le_one_right hρ.le ha1) _).trans (hi a ha ha1 j)
    have hxlt : ‖x-p a j‖<ρ*a := by simpa only [mem_ball,dist_eq_norm] using hx
    have hn : ‖x‖≤‖x-p a j‖+‖p a j‖ := by
      calc
        _ = ‖x-p a j+p a j‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    simp only [mem_closedBall,dist_zero_right]
    linarith
  obtain ⟨η,hη,he⟩ := FiniteSphereAsymptotics.finite_sphere_family p ρ χ δ R 1 b C C
    hρ hχ hδ hb hC hC hsep hi (forcing p ρ χ R hρ hχ hi A)
    (fun a => electric ((a : ℂ)⁻¹ • A)) (fun a l i => electric ((a : ℂ)⁻¹ • A) (p a l) i)
    (fun _ _ _ _ _ => rfl)
    (fun a ha ha1 j i => (hbound a ha (p a j) (hp a ha ha1 j) i).1)
    (fun a ha ha1 i => forcing_actual p ρ χ R hρ hχ hi A a ha ha1 i)
    (fun a _ _ _ i _ _ => (RestrictedTEMaterial.electric_smooth _ i).contDiffAt.differentiableAt (by simp))
    (fun a ha ha1 j i x hx => (hbound a ha x (hball a ha ha1 j x hx) i).2)
  refine ⟨C,hC,min η 1,lt_min hη zero_lt_one,?_⟩
  intro a ha had
  have ha1 : a≤1 := (had.trans_le (min_le_right _ _)).le
  obtain ⟨d,hdr,hdc,hest⟩ := he a ha (had.trans_le (min_le_left _ _))
  have hd : d=FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1 :=
    FiniteSphereActualSources.support_ext d _ hdr hdc
  rw [hd] at hest
  exact ⟨ha1,hest⟩

end OQ14.RestrictedTEAsymptotics
#print axioms OQ14.RestrictedTEAsymptotics.forcing_actual
#print axioms OQ14.RestrictedTEAsymptotics.eventual_estimates
