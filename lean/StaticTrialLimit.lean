import FiniteStaticCoherent
import PlaneQuadraticMoving

/-! Actual trial free flux converges on the whole plane to its static coherent expression. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.StaticTrialLimit
open MeasureTheory Metric Set Filter PlaneSourceKernel MaxwellRadiation
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem quadratic_scaled_limit (k R T γ : ℝ) (hγ : γ ≠ 0) :
    Tendsto (fun a : ℝ => PlaneQuadraticFlux.wholeConstant k R T (γ*a)*a^4) (𝓝[>] 0) (𝓝 0) := by
  let P := fun a : ℝ =>
    (4*|k| *(4*Real.pi)⁻¹*PlaneMaxwellLocal.electricCoefficient k R T*(Real.pi+PlaneInverseCube.diskConstant))*
      (|k|/γ^2*a^2+(1/γ^3)*a)+
      (MaxwellPlaneTail.tailConstant k R*PlaneInverseCube.diskConstant/T)*a^4
  have hc : Continuous P := by dsimp [P]; fun_prop
  have ht := (hc.continuousAt (x := 0)).tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hz : P 0=0 := by dsimp [P]; ring
  rw [hz] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with a ha
  have han : a ≠ 0 := ne_of_gt ha
  dsimp [P]
  unfold PlaneQuadraticFlux.wholeConstant PlaneQuadraticFlux.diskConstant PlaneQuadraticFlux.magneticCoefficient
  field_simp
  ring

theorem trial_to_static (k R T γ M A₀ : ℝ) (hR : 0 ≤ R) (hk : k ≠ 0)
    (hT : 2 ≤ T) (hTR : 2*R ≤ T) (hγ : 0 < γ) (hM : 0 ≤ M) (_hA₀ : 0 ≤ A₀)
    (S : ℝ → Source) (p : ℝ → ι → Space) (j : ℝ → ι → Fin 3) (A : ℝ → ι → ℂ)
    (hS : ∀ᶠ a in 𝓝[>] 0, Admissible R (γ*a) (S a))
    (hp : ∀ᶠ a in 𝓝[>] 0, ∀ s, p a s ∈ closedBall 0 R)
    (hm : ∀ᶠ a in 𝓝[>] 0, sourceMass (S a) ≤ M*a^2)
    (hA : ∀ᶠ a in 𝓝[>] 0, (∑ s, ‖A a s‖) ≤ A₀/a) :
    Tendsto (fun a => ∫ q : Plane, ‖ParityTotalFlux.freeFlux k (S a) (p a) (j a) (A a) q-
      FiniteStaticCoherent.staticMixed k (S a) (p a) (j a) (A a) q‖) (𝓝[>] 0) (𝓝 0) := by
  let C := |StaticCoherentRemainder.wholeCoefficient k R T|
  have h1 : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have ht := (h1.const_mul (C*M*A₀)).add ((quadratic_scaled_limit k R T γ hγ.ne').const_mul (M^2))
  simp only [mul_zero,add_zero] at ht
  have hsmall : ∀ᶠ a : ℝ in 𝓝[>] 0, γ*a ≤ T+R := by
    have hlim := h1.const_mul γ
    simp only [mul_zero] at hlim
    exact (hlim.eventually (gt_mem_nhds (by linarith : 0 < T+R))).mono (fun a ha => ha.le)
  apply squeeze_zero' (Filter.Eventually.of_forall (fun a => integral_nonneg (fun q => norm_nonneg _))) _ ht
  filter_upwards [hS,hp,hm,hA,hsmall,self_mem_nhdsWithin] with a hS hp hm hA hdM ha
  have hd := mul_pos hγ ha
  have he := FiniteStaticCoherent.whole_mass k R T (γ*a) hR hd hk hT hTR hdM (S a) hS (p a) (j a) (A a) hp
  have he' : (∫ q : Plane, ‖SourceHerglotzFinite.electricMixed k (S a) (fun _ => true) (p a) (j a) (A a) q-
      FiniteStaticCoherent.staticMixed k (S a) (p a) (j a) (A a) q‖) ≤ (C*M*A₀)*a := by
    calc
      _ ≤ C*sourceMass (S a)*(∑ s, ‖A a s‖) := he.2.trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) (sourceMass_nonnegative _))
          (Finset.sum_nonneg (fun s _ => norm_nonneg _)))
      _ ≤ C*(M*a^2)*(A₀/a) := by dsimp [C]; gcongr
      _ = _ := by have han : a ≠ 0 := ne_of_gt ha; field_simp; ring
  have hq := PlaneQuadraticFlux.whole_mass k R T (γ*a) hR hd hT hTR (S a) (S a) hS hS
  have hq' : (∫ q : Plane, ‖MaxwellPlaneL1.flux k (S a) (S a) q‖) ≤
      M^2*(PlaneQuadraticFlux.wholeConstant k R T (γ*a)*a^4) := by
    have hm0 := sourceMass_nonnegative (S a)
    have hC := PlaneQuadraticFlux.whole_constant_nonnegative k R T (γ*a) hR (by linarith) hd
    calc
      _ ≤ PlaneQuadraticFlux.wholeConstant k R T (γ*a)*sourceMass (S a)*sourceMass (S a) := hq.2
      _ ≤ PlaneQuadraticFlux.wholeConstant k R T (γ*a)*(M*a^2)*(M*a^2) := by gcongr
      _ = _ := by ring
  obtain ⟨_,_,hwhole⟩ := MaxwellPlaneL1.whole_plane_bound k R (γ*a) hR hd
  have hiq := (hwhole (S a) (S a) hS hS).1
  have hsum (q : Plane) : ParityTotalFlux.freeFlux k (S a) (p a) (j a) (A a) q-
      FiniteStaticCoherent.staticMixed k (S a) (p a) (j a) (A a) q=
      (SourceHerglotzFinite.electricMixed k (S a) (fun _ => true) (p a) (j a) (A a) q-
        FiniteStaticCoherent.staticMixed k (S a) (p a) (j a) (A a) q)+MaxwellPlaneL1.flux k (S a) (S a) q := by
    rw [ParityTotalFlux.free_identity]; ring
  simp_rw [hsum]
  calc
    _ ≤ (∫ q : Plane, ‖SourceHerglotzFinite.electricMixed k (S a) (fun _ => true) (p a) (j a) (A a) q-
        FiniteStaticCoherent.staticMixed k (S a) (p a) (j a) (A a) q‖)+
        (∫ q : Plane, ‖MaxwellPlaneL1.flux k (S a) (S a) q‖) := by
      rw [← integral_add he.1.norm hiq.norm]
      exact integral_mono_ae (he.1.add hiq).norm (he.1.norm.add hiq.norm)
        (Filter.Eventually.of_forall (fun q => norm_add_le _ _))
    _ ≤ _ := add_le_add he' hq'

end OQ14.StaticTrialLimit
#print axioms OQ14.StaticTrialLimit.quadratic_scaled_limit
#print axioms OQ14.StaticTrialLimit.trial_to_static
