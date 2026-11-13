import Packet06SchurInverse
import Packet06Laurent

/-! A simple scalar Schur zero yields the complete operator Laurent expansion. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SchurPole
open Filter Packet06RankOneRepair Packet06ScalarSchur Packet06SchurAnalytic Packet06SchurInverse
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem inverse_repair_analyticAt (A : ℂ → E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (z : ℂ) (hA : AnalyticAt ℂ A z) (hC : IsUnit (repair (A z) w ψ)) :
    AnalyticAt ℂ (fun v => Ring.inverse (repair (A v) w ψ)) z :=
  (analyticOnNhd_inverse (𝕜 := ℂ) _ hC).comp
    (f := fun v : ℂ => repair (A v) w ψ) (hA.add analyticAt_const)

theorem polarNumerator_analyticAt (A : ℂ → E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (z : ℂ) (hA : AnalyticAt ℂ A z) (hC : IsUnit (repair (A z) w ψ)) :
    AnalyticAt ℂ (fun v => polarNumerator (A v) w ψ) z := by
  have hi := inverse_repair_analyticAt A w ψ z hA hC
  have hψ := ((ContinuousLinearMap.compL ℂ E E ℂ ψ).analyticAt _).comp
    (f := fun v : ℂ => Ring.inverse (repair (A v) w ψ)) hi
  have hw := ((ContinuousLinearMap.apply ℂ E w).analyticAt _).comp
    (f := fun v : ℂ => Ring.inverse (repair (A v) w ψ)) hi
  exact ((ContinuousLinearMap.smulRightL ℂ E E).analyticAt_bilinear _).comp
    (f := fun v : ℂ => (ψ.comp (Ring.inverse (repair (A v) w ψ)),
      Ring.inverse (repair (A v) w ψ) w)) (hψ.prod hw)

theorem punctured_units (A : ℂ → E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (z d : ℂ) (hA : AnalyticAt ℂ A z) (hC : IsUnit (repair (A z) w ψ))
    (hd : HasDerivAt (fun v => scalar (A v) w ψ) d z) (hd0 : d ≠ 0) :
    ∀ᶠ v in 𝓝[≠] z, IsUnit (A v) := by
  have hS := scalar_analyticAt A w ψ z hA hC
  have hnonzero : ∀ᶠ v in 𝓝[≠] z, scalar (A v) w ψ ≠ 0 := by
    rcases hS.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact False.elim (hd0 (hd.unique ((hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq h)))
    · exact h
  have hunit : ∀ᶠ v in 𝓝 z, IsUnit (repair (A v) w ψ) :=
    (hA.continuousAt.add continuousAt_const).eventually (Units.isOpen.mem_nhds hC)
  filter_upwards [hnonzero,hunit.filter_mono nhdsWithin_le_nhds] with v hv hu
  exact (isUnit_iff_scalar _ w ψ hu).mpr hv

theorem inverse_meromorphicAt (A : ℂ → E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (z d : ℂ) (hA : AnalyticAt ℂ A z) (hC : IsUnit (repair (A z) w ψ))
    (hd : HasDerivAt (fun v => scalar (A v) w ψ) d z) (hd0 : d ≠ 0) :
    MeromorphicAt (fun v => Ring.inverse (A v)) z := by
  have hi := inverse_repair_analyticAt A w ψ z hA hC
  have hp := polarNumerator_analyticAt A w ψ z hA hC
  have hs := scalar_analyticAt A w ψ z hA hC
  have hm := hi.meromorphicAt.add (hs.meromorphicAt.inv.smul hp.meromorphicAt)
  apply hm.congr
  have hunit : ∀ᶠ v in 𝓝 z, IsUnit (repair (A v) w ψ) :=
    (hA.continuousAt.add continuousAt_const).eventually (Units.isOpen.mem_nhds hC)
  filter_upwards [punctured_units A w ψ z d hA hC hd hd0,
    hunit.filter_mono nhdsWithin_le_nhds] with v hv hu
  exact (inverse_formula _ w ψ hu ((isUnit_iff_scalar _ w ψ hu).mp hv)).symm

theorem simple_inverse_expansion (A : ℂ → E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ)
    (z : ℂ) (hA : AnalyticAt ℂ A z) (hC : IsUnit (repair (A z) w ψ))
    (hs : scalar (A z) w ψ = 0)
    (hd : deriv (fun v => scalar (A v) w ψ) z ≠ 0) :
    let u := Ring.inverse (repair (A z) w ψ) w
    let φ := ψ.comp (Ring.inverse (repair (A z) w ψ))
    ∃ (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, R x = (φ x / φ (deriv A z u)) • u) ∧
      Tendsto (fun v => (v-z) • Ring.inverse (A v)) (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ v in 𝓝[≠] z, Ring.inverse (A v) = (v-z)⁻¹ • R + B v) := by
  have hcross := scalar_hasDerivAt A (deriv A z) w ψ z hA.differentiableAt.hasDerivAt hC
  have hd' : ψ (Ring.inverse (repair (A z) w ψ)
      (deriv A z (Ring.inverse (repair (A z) w ψ) w))) ≠ 0 := by
    rwa [hcross.deriv] at hd
  have hker : ∀ x, A z x = 0 → ∃ a : ℂ, x = a • Ring.inverse (repair (A z) w ψ) w := by
    intro x hx
    exact ⟨ψ x,((scalar_kernel _ w ψ hC hs).2.2.2 x).mp hx⟩
  have hnot : ¬ IsUnit (A z) := fun h => (isUnit_iff_scalar _ w ψ hC).mp h hs
  exact Packet06Laurent.simple_inverse_expansion A (deriv A z) z hA.differentiableAt.hasDerivAt
    (Ring.inverse (repair (A z) w ψ) w) (ψ.comp (Ring.inverse (repair (A z) w ψ)))
    hker (left_annihilates _ w ψ hC hs) hd'
    (inverse_meromorphicAt A w ψ z _ hA hC hcross hd')
    (punctured_units A w ψ z _ hA hC hcross hd') hnot

end OQ14.Packet06SchurPole
#print axioms OQ14.Packet06SchurPole.inverse_repair_analyticAt
#print axioms OQ14.Packet06SchurPole.polarNumerator_analyticAt
#print axioms OQ14.Packet06SchurPole.punctured_units
#print axioms OQ14.Packet06SchurPole.inverse_meromorphicAt
#print axioms OQ14.Packet06SchurPole.simple_inverse_expansion
