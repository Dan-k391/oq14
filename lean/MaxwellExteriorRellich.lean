import ScalarExteriorRellich
import ComponentAngularEnergy
import HomogeneousVolumePower

/-! # Actual exterior vanishing of zero-power Maxwell volume fields -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaxwellExteriorRellich

open MeasureTheory Metric OQ14.Maxwell OQ14.ExteriorHelmholtz
  OQ14.ComponentAngularEnergy

theorem electric_zero_of_farPower_zero (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hz : AngularPower.farPower k ρ = 0) :
    ∀ x, R < ‖x‖ → ExteriorContinuity.electric k ρ x = 0 := by
  have hzero (i : Fin 3) : ∀ x, R < ‖x‖ → ExteriorContinuity.electric k ρ x i = 0 := by
    apply ScalarExteriorRellich.zero_of_surface_mass R hR k hk
      (fun x => ExteriorContinuity.electric k ρ x i)
    · intro x hx
      exact (contDiffAt_pi.mp (ExteriorSmooth.electric_contDiffAt k ρ hρ R hs x hx)
        i).contDiffWithinAt
    · exact fun x hx => electric_helmholtz k (ne_of_gt hk) ρ hρ R hs x hx i
    · exact electric_component_mass_zero_of_farPower_zero k R hR ρ hρ hs hz i
  intro x hx
  exact funext (fun i => hzero i x hx)

theorem magnetic_zero_of_farPower_zero (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hz : AngularPower.farPower k ρ = 0) :
    ∀ x, R < ‖x‖ → MagneticResponse.magnetic k ρ x = 0 := by
  have hzero (i : Fin 3) : ∀ x, R < ‖x‖ → MagneticResponse.magnetic k ρ x i = 0 := by
    apply ScalarExteriorRellich.zero_of_surface_mass R hR k hk
      (fun x => MagneticResponse.magnetic k ρ x i)
    · intro x hx
      exact (contDiffAt_pi.mp (ExteriorSmooth.magnetic_contDiffAt k ρ hρ R hs x hx)
        i).contDiffWithinAt
    · exact fun x hx => magnetic_helmholtz k (ne_of_gt hk) ρ hρ R hs x hx i
    · exact magnetic_component_mass_zero_of_farPower_zero k R hR ρ hρ hs hz i
  intro x hx
  exact funext (fun i => hzero i x hx)

theorem exterior_zero_of_farPower_zero (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hs : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0)
    (hz : AngularPower.farPower k ρ = 0) :
    ∀ x, R < ‖x‖ →
      ExteriorContinuity.electric k ρ x = 0 ∧ MagneticResponse.magnetic k ρ x = 0 :=
  fun x hx => ⟨electric_zero_of_farPower_zero k hk R hR ρ hρ hs hz x hx,
    magnetic_zero_of_farPower_zero k hk R hR ρ hρ hs hz x hx⟩

theorem homogeneous_exterior_zero (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    ∀ x, R < ‖x‖ →
      HomogeneousVolumePower.electric c k R u x = 0 ∧
      HomogeneousVolumePower.magnetic c k u x = 0 := by
  have h := exterior_zero_of_farPower_zero k hk R hR (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc)
    (HomogeneousVolumePower.homogeneous_farPower_zero c k R hR u hc hsol)
  intro x hx
  rw [HomogeneousVolumePower.electric_exterior c k R u x hx]
  exact h x hx

theorem homogeneous_fields_compact (c : StaticCoefficient.Coefficient)
    (k : ℝ) (hk : 0 < k) (R : ℝ) (hR : 0 ≤ R) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hsol : DynamicVolume.volumeBlock c k R u = 0) :
    HasCompactSupport (HomogeneousVolumePower.electric c k R u) ∧
      HasCompactSupport (HomogeneousVolumePower.magnetic c k u) := by
  have hz := homogeneous_exterior_zero c k hk R hR u hc hsol
  have hbound (E : Field) (hE : ∀ x, R < ‖x‖ → E x = 0) : HasCompactSupport E := by
    apply (isCompact_closedBall (0 : Space) R).of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hn
    have hr : R < ‖x‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hn
    exact hx (hE x hr)
  exact ⟨hbound _ (fun x hx => (hz x hx).1), hbound _ (fun x hx => (hz x hx).2)⟩

end OQ14.MaxwellExteriorRellich

#print axioms OQ14.MaxwellExteriorRellich.electric_zero_of_farPower_zero
#print axioms OQ14.MaxwellExteriorRellich.magnetic_zero_of_farPower_zero
#print axioms OQ14.MaxwellExteriorRellich.exterior_zero_of_farPower_zero
#print axioms OQ14.MaxwellExteriorRellich.homogeneous_exterior_zero
#print axioms OQ14.MaxwellExteriorRellich.homogeneous_fields_compact
