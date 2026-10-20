import MaxwellRadiation
import ExteriorMaterial
import MaterialHCurl

/-! # Actual outgoing small-volume Maxwell solutions

The radiation condition is a limit over all spatial points tending to
infinity. The fields are the proved continuous exterior representatives
of the actual volume responses.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.OutgoingMaterial

open MeasureTheory Metric Filter OQ14.Maxwell OQ14.MaterialMaxwell OQ14.MaterialHCurl
open scoped Topology

def spatialInfinity : Filter Space := comap (fun x : Space => ‖x‖) atTop

def Outgoing (E H : Field) : Prop :=
  ∀ i : Fin 3, Tendsto (fun x : Space => (‖x‖ : ℂ) *
    (crossProduct (H x) (MaxwellRadiation.direction x) i - E x i))
    spatialInfinity (𝓝 0)

theorem compact_source_outgoing (k R : ℝ) (hR : 0 ≤ R)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j) volume)
    (hc : ∀ j y, y ∉ closedBall 0 R → ρ j y = 0) :
    Outgoing (ExteriorContinuity.electric k ρ) (MagneticResponse.magnetic k ρ) := by
  intro i
  exact MaxwellRadiation.silver_mueller_limit k R hR ρ hρ hc id tendsto_comap i

theorem material_scattered_outgoing (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (hR : 0 ≤ R) (u : VectorFourier.VectorL2)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    Outgoing (ExteriorMaterial.scattered c k R u)
      (MagneticResponse.magnetic k (DynamicVolume.source c u)) := by
  have hO := compact_source_outgoing k R hR (DynamicVolume.source c u)
    (DynamicVolume.source_integrable c u R hc) (DynamicVolume.source_zero c u R hc)
  intro i
  apply (hO i).congr'
  have hlim : Tendsto (fun x : Space => ‖x‖) spatialInfinity atTop := tendsto_comap
  filter_upwards [hlim.eventually (eventually_gt_atTop R)] with x hx
  rw [ExteriorMaterial.scattered_exterior c k R u x hx]
  rfl

/-- An actual outgoing small-volume solution, with its inverse bound and
genuine regional H(curl) graphs on every bounded open region. -/
theorem exists_outgoing_small_volume_fields (c : StaticCoefficient.Coefficient)
    (k R : ℝ) (hR : 0 ≤ R) (hsmall : 252 * c.bound * k^2 * R^2 < 1)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (Einc Hinc : Field)
    (hE : ∀ T i, MemLp (fun x => Einc x i) 2 (volume.restrict (closedBall 0 T)))
    (hH : ∀ T i, MemLp (fun x => Hinc x i) 2 (volume.restrict (closedBall 0 T)))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    ∃ u : VectorFourier.VectorL2,
      DynamicVolume.volumeBlock c k R u = IncidentLocalization.datum c R Einc hc (hE R) ∧
      ‖u‖ ≤ (1 - 252 * c.bound * k^2 * R^2)⁻¹ *
        ‖IncidentLocalization.datum c R Einc hc (hE R)‖ ∧
      TestMaxwell k (dielectric c) (ExteriorMaterial.total c k R u Einc)
        (totalMagnetic c k u Hinc) ∧
      (∀ T i, MemLp (fun x => ExteriorMaterial.total c k R u Einc x i) 2
        (volume.restrict (closedBall 0 T))) ∧
      (∀ T i, MemLp (fun x => totalMagnetic c k u Hinc x i) 2
        (volume.restrict (closedBall 0 T))) ∧
      Outgoing (ExteriorMaterial.scattered c k R u)
        (MagneticResponse.magnetic k (DynamicVolume.source c u)) ∧
      (∀ x, R < ‖x‖ →
        ContinuousAt (ExteriorMaterial.scattered c k R u) x ∧
        ContinuousAt (MagneticResponse.magnetic k (DynamicVolume.source c u)) x) ∧
      (∀ Ω : Set Space, IsOpen Ω → Bornology.IsBounded Ω →
        ∃ e h : DomainCurl.HCurl Ω,
          (∀ j, (e.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
            fun x => ExteriorMaterial.total c k R u Einc x j) ∧
          (∀ j, (h.val.1 j : Space → ℂ) =ᵐ[DomainCurl.regionMeasure Ω]
            fun x => totalMagnetic c k u Hinc x j) ∧
          WeakConservation.WeakMaxwell k (fun _ => 1) (dielectric c) e h) := by
  obtain ⟨u, hu, hn, hM, hEu, hHu, hEc, _⟩ :=
    ExteriorMaterial.exists_small_volume_fields c k R hR hsmall hc Einc Hinc hE hH hMax
  refine ⟨u, hu, hn, hM, hEu, hHu, material_scattered_outgoing c k R hR u hc, ?_, ?_⟩
  · intro x hx
    exact ⟨hEc x hx, ExteriorContinuity.magnetic_continuousAt k (DynamicVolume.source c u)
      (DynamicVolume.source_integrable c u R hc) R (DynamicVolume.source_zero c u R hc) x hx⟩
  · intro Ω hΩ hbΩ
    have hEΩ := fun j => memLp_bounded_of_balls _ (fun T => hEu T j) Ω hbΩ
    have hHΩ := fun j => memLp_bounded_of_balls _ (fun T => hHu T j) Ω hbΩ
    exact exists_regional_fields hΩ k (dielectric c) _ _ hEΩ hHΩ
      (fun j => coefficient_mul_memLp Ω (dielectric c) (dielectric_measurable c)
        (1+c.bound) (dielectric_norm_bound c) _ (hEΩ j)) hM

end OQ14.OutgoingMaterial

#print axioms OQ14.OutgoingMaterial.compact_source_outgoing
#print axioms OQ14.OutgoingMaterial.material_scattered_outgoing
#print axioms OQ14.OutgoingMaterial.exists_outgoing_small_volume_fields
