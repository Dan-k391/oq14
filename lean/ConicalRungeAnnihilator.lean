import MaxwellExteriorRellich
import NewtonReciprocity
import ConicalSeparatedSource

/-! Actual transverse plane annihilation, exterior Rellich, and reciprocal annihilation of separated sources. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalRungeAnnihilator
open MeasureTheory Set Metric OQ14.Maxwell
open scoped InnerProductSpace
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def phase (k : ℝ) (n x : Space) : ℂ := Complex.exp (-Complex.I*k*(@inner ℝ Space _ n x : ℝ))

def planePair (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, DyadicRadiation.transverse n i j*(∫ x, phase k n x*ρ j x)

theorem scalar_amplitude_eq (k : ℝ) (ρ : Space → ℂ) (n : Space) :
    ScalarFarField.amplitude k ρ n=(4*(Real.pi : ℂ))⁻¹*(∫ x, phase k n x*ρ x) := by
  unfold ScalarFarField.amplitude
  calc
    _ = ∫ x, (4*(Real.pi : ℂ))⁻¹*(phase k n x*ρ x) := by
      apply integral_congr_ae
      filter_upwards with x
      unfold phase
      ring
    _ = _ := integral_const_mul _ _

theorem electric_amplitude_eq (k : ℝ) (ρ : Fin 3 → Space → ℂ) (n : Space) (i : Fin 3) :
    MaxwellFarField.electricAmplitude k ρ n i=(k : ℂ)^2*(4*(Real.pi : ℂ))⁻¹*planePair k ρ n i := by
  simp only [MaxwellFarField.electricAmplitude,MaxwellFarField.potentialAmplitude,scalar_amplitude_eq,
    planePair,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem farPower_zero (k : ℝ) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, planePair k ρ n i=0) : AngularPower.farPower k ρ=0 := by
  apply (AngularPowerZero.farPower_zero_iff_unit k ρ hρ).mpr
  intro n hn
  ext i
  rw [electric_amplitude_eq,h n hn i,mul_zero]
  rfl

theorem exterior_zero (k : ℝ) (hk : 0 < k) (a : ℝ) (ha : 0 ≤ a)
    (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j x, x ∉ closedBall (0 : Space) a → ρ j x=0)
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, planePair k ρ n i=0) :
    ∀ x, a < ‖x‖ → ExteriorContinuity.electric k ρ x=0 :=
  MaxwellExteriorRellich.electric_zero_of_farPower_zero k hk a ha ρ hρ hc (farPower_zero k ρ hρ h)

theorem literal_exterior_zero_ae (k : ℝ) (hk : 0 < k) (a : ℝ) (ha : 0 ≤ a)
    (F : VectorL2) (ρ : Fin 3 → Space → ℂ) (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j x, x ∉ closedBall (0 : Space) a → ρ j x=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, planePair k ρ n i=0) :
    ∀ᵐ x : Space, a < ‖x‖ → FieldResponse.electric k F ρ x=0 := by
  filter_upwards [ExteriorContinuity.electric_ae_exterior k F ρ hρ hF a hc] with x hx hax
  exact (hx hax).trans (exterior_zero k hk a ha ρ hρ hc h x hax)

theorem reciprocal_pair_zero (k : ℝ) (hk : 0 < k) (a T : ℝ) (ha : 0 ≤ a) (haT : a ≤ T)
    (F G : VectorL2) (ρ σ : Fin 3 → Space → ℂ)
    (hcρ : ∀ j x, x ∉ closedBall (0 : Space) a → ρ j x=0)
    (hcσ : ∀ j x, x ∉ closedBall (0 : Space) T → σ j x=0)
    (hσin : ∀ j x, x ∈ closedBall (0 : Space) a → σ j x=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (hG : ∀ j, (NewtonL2.physicalCoordinate G j : Space → ℂ) =ᵐ[volume] σ j)
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, planePair k ρ n i=0) :
    (∑ i : Fin 3, ∫ x, FieldResponse.electric k G σ x i*ρ i x)=0 := by
  have hcρT (j : Fin 3) (x : Space) (hx : x ∉ closedBall (0 : Space) T) : ρ j x=0 :=
    hcρ j x (fun hn => hx (closedBall_subset_closedBall haT hn))
  rw [NewtonReciprocity.electric_compact_L2_reciprocity k T G F σ ρ hcσ hcρT hG hF]
  have hρ := NewtonReciprocity.compact_source_integrable a F ρ hcρ hF
  have he := literal_exterior_zero_ae k hk a ha F ρ hρ hcρ hF h
  apply Finset.sum_eq_zero
  intro i _
  apply integral_eq_zero_of_ae
  filter_upwards [he] with x hx
  by_cases hin : x ∈ closedBall (0 : Space) a
  · simp only [hσin i x hin,zero_mul,Pi.zero_apply]
  · have hax : a < ‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hin
    rw [hx hax]
    simp only [Pi.zero_apply,mul_zero]

theorem separated_pair_zero (p : ConicalStaticVolume.Data) (a : ℝ) (ha : 0 ≤ a)
    (hai : a < p.cutoff.rIn) (k : ℝ) (hk : 0 < k)
    (F : VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hcρ : ∀ j x, x ∉ closedBall (0 : Space) a → ρ j x=0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate F j : Space → ℂ) =ᵐ[volume] ρ j)
    (h : ∀ n : Space, ‖n‖=1 → ∀ i, planePair k ρ n i=0) :
    (∑ i : Fin 3, ∫ x, FieldResponse.electric k (ConicalSeparatedSource.forcing p a)
      (ConicalSeparatedSource.physicalSource p a) x i*ρ i x)=0 :=
  reciprocal_pair_zero k hk a p.cutoff.rOut ha (hai.trans p.cutoff.rIn_lt_rOut).le
    F (ConicalSeparatedSource.forcing p a) ρ (ConicalSeparatedSource.physicalSource p a)
    hcρ (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.source_zero_material p a hai) hF (ConicalSeparatedSource.forcing_ae p a) h

end OQ14.ConicalRungeAnnihilator

#print axioms OQ14.ConicalRungeAnnihilator.scalar_amplitude_eq
#print axioms OQ14.ConicalRungeAnnihilator.electric_amplitude_eq
#print axioms OQ14.ConicalRungeAnnihilator.farPower_zero
#print axioms OQ14.ConicalRungeAnnihilator.exterior_zero
#print axioms OQ14.ConicalRungeAnnihilator.literal_exterior_zero_ae
#print axioms OQ14.ConicalRungeAnnihilator.reciprocal_pair_zero
#print axioms OQ14.ConicalRungeAnnihilator.separated_pair_zero
