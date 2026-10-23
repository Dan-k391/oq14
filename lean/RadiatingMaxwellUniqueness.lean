import RadiatingFieldPower
import PiecewiseMaxwellUniqueness
import MaxwellZeroField
import UniformHelmholtzEquation
import FiniteRadialPartition

/-! Genuine outgoing uniqueness for weak Maxwell fields with actual far-field limits. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.RadiatingMaxwellUniqueness
open MeasureTheory Metric Filter Set OQ14.Maxwell OQ14.AngularPower
  OQ14.MaxwellFarField OQ14.ExteriorHelmholtz OQ14.RegionalMaxwellContinuation
open scoped Topology

theorem electric_exterior_zero (k : ℝ) (hk : 0<k) (R : ℝ) (hR : 0≤R)
    (ε : Space → ℝ) (hε : Measurable ε) (M : ℝ) (hbε : ∀ x, ‖ε x‖≤M)
    (E H : Field) (A : Sphere → Vector)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k ε E H)
    (hεout : ∀ᵐ x : Space, R<‖x‖ → ε x=1)
    (hEs : ∀ i x, R<‖x‖ → ContDiffAt ℝ (⊤ : ℕ∞) (fun z => E z i) x)
    (htrans : ∀ n : Sphere, dot (MaxwellRadiation.direction n) (A n)=0)
    (hc : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))) ∧
      Continuous (fun n : Sphere => H (r • (n : Space))))
    (hb : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
      ‖factor k r*E (r • (n : Space)) i‖≤C ∧ ‖factor k r*H (r • (n : Space)) i‖≤C)
    (he : ∀ n : Sphere, Tendsto (fun r => factor k r • E (r • (n : Space))) atTop (𝓝 (A n)))
    (hh : ∀ n : Sphere, Tendsto (fun r => factor k r • H (r • (n : Space))) atTop
      (𝓝 (crossProduct (MaxwellRadiation.direction n) (A n)))) :
    ∀ x, R<‖x‖ → E x=0 := by
  have hloc (i : Fin 3) : LocallyIntegrable (fun x => E x i) :=
    HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => hE T i)
  have hw (i : Fin 3) : WeakHelmholtzRegularity.IsWeakHelmholtz (k : ℂ)
      {x : Space | R<‖x‖} (fun x => E x i) := by
    simpa only [Real.sqrt_one,mul_one] using
      RegionalMaxwellLocalization.electric_weak_helmholtz_of_global k 1 hk.ne' (by norm_num)
        ε {x : Space | R<‖x‖} E H hMax
        (weight_equality_on_constant_region ε 1 {x : Space | R<‖x‖} E hεout) hloc i
  have heq (i : Fin 3) := UniformHelmholtzEquation.classical_of_weak {x : Space | R<‖x‖}
    (isOpen_lt continuous_const continuous_norm) k (fun x => E x i) (hEs i) (hw i)
  have hz (i : Fin 3) := ScalarExteriorRellich.zero_of_surface_mass R hR k hk
    (fun x => E x i) (fun x hx => (hEs i x hx).contDiffWithinAt) (heq i)
    (RadiatingFieldPower.electric_mass_zero k ε hε M hbε E H A hE hH hMax htrans hc hb he hh i)
  intro x hx
  exact funext (fun i => hz i x hx)

theorem vacuum_fields_zero (k : ℝ) (hk : 0<k) (R : ℝ) (hR : 0≤R)
    (E H : Field) (A : Sphere → Vector)
    (hE : ∀ T i, MemLp (fun x => E x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => H x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : MaterialMaxwell.TestMaxwell k (fun _ => 1) E H)
    (hEs : ∀ i x, R<‖x‖ → ContDiffAt ℝ (⊤ : ℕ∞) (fun z => E z i) x)
    (htrans : ∀ n : Sphere, dot (MaxwellRadiation.direction n) (A n)=0)
    (hc : ∀ᶠ r : ℝ in atTop, Continuous (fun n : Sphere => E (r • (n : Space))) ∧
      Continuous (fun n : Sphere => H (r • (n : Space))))
    (hb : ∃ C : ℝ, 0≤C ∧ ∀ᶠ r : ℝ in atTop, ∀ n : Sphere, ∀ i : Fin 3,
      ‖factor k r*E (r • (n : Space)) i‖≤C ∧ ‖factor k r*H (r • (n : Space)) i‖≤C)
    (he : ∀ n : Sphere, Tendsto (fun r => factor k r • E (r • (n : Space))) atTop (𝓝 (A n)))
    (hh : ∀ n : Sphere, Tendsto (fun r => factor k r • H (r • (n : Space))) atTop
      (𝓝 (crossProduct (MaxwellRadiation.direction n) (A n)))) :
    (E =ᵐ[volume] 0) ∧ (H =ᵐ[volume] 0) := by
  have hz := electric_exterior_zero k hk R hR (fun _ => 1) measurable_const 1 (by simp)
    E H A hE hH hMax (Eventually.of_forall (fun _ _ => rfl)) hEs htrans hc hb he hh
  have hloc (i : Fin 3) : LocallyIntegrable (fun x => E x i) :=
    HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _ (fun T => hE T i)
  let x₀ := RadialMaterialCells.axis (R+1)
  have hx₀ : R<‖x₀‖ := by
    dsimp [x₀]
    rw [RadialMaterialCells.axis_norm,abs_of_pos (by linarith : 0<R+1)]
    linarith
  have hΩ : IsOpen {x : Space | R<‖x‖} := isOpen_lt continuous_const continuous_norm
  have hza : E =ᵐ[volume.restrict {x : Space | R<‖x‖}] 0 := by
    apply (ae_restrict_iff' hΩ.measurableSet).mpr
    exact Eventually.of_forall hz
  have hzero : E =ᵐ[volume] 0 := by
    have h := electric_zero_on_weighted_region k 1 hk.ne' (by norm_num) (fun _ => 1)
      univ isOpen_univ isPreconnected_univ E H hMax hloc
      (Eventually.of_forall (fun _ _ _ => rfl)) x₀ (mem_univ _)
      (zero_germ_of_open E _ hΩ hza x₀ hx₀)
    simpa only [Measure.restrict_univ] using h
  exact ⟨hzero,MaxwellZeroField.magnetic_zero_of_electric_zero k hk.ne' (fun _ => 1)
    E H hMax (fun i => HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _
      (fun T => hH T i)) hzero⟩

end OQ14.RadiatingMaxwellUniqueness
#print axioms OQ14.RadiatingMaxwellUniqueness.electric_exterior_zero
#print axioms OQ14.RadiatingMaxwellUniqueness.vacuum_fields_zero
