import Packet06ScalarSchur

/-! Analytic scalar Schur functions and their exact crossing derivative. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06SchurAnalytic
open Packet06RankOneRepair Packet06ScalarSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem inverse_hasDerivAt (C : ℂ → E →L[ℂ] E) (C₁ : E →L[ℂ] E) (z : ℂ)
    (hC : HasDerivAt C C₁ z) (hu : IsUnit (C z)) :
    HasDerivAt (fun w => Ring.inverse (C w))
      (-(Ring.inverse (C z)*C₁*Ring.inverse (C z))) z := by
  have hi : HasFDerivAt Ring.inverse
      (-ContinuousLinearMap.mulLeftRight ℂ (E →L[ℂ] E) (Ring.inverse (C z)) (Ring.inverse (C z))) (C z) := by
    obtain ⟨u,hu⟩ := hu
    simpa only [←hu,Ring.inverse_unit] using (hasFDerivAt_ringInverse (𝕜 := ℂ) u)
  exact hi.comp_hasDerivAt z hC

theorem scalar_analyticAt (A : ℂ → E →L[ℂ] E) (w : E) (ψ : E →L[ℂ] ℂ) (z : ℂ)
    (hA : AnalyticAt ℂ A z) (hu : IsUnit (repair (A z) w ψ)) :
    AnalyticAt ℂ (fun v => scalar (A v) w ψ) z := by
  have hC : AnalyticAt ℂ (fun v => repair (A v) w ψ) z := hA.add analyticAt_const
  have hi : AnalyticAt ℂ (fun v => Ring.inverse (repair (A v) w ψ)) z :=
    (analyticOnNhd_inverse (𝕜 := ℂ) _ hu).comp
      (f := fun v : ℂ => repair (A v) w ψ) hC
  have he : AnalyticAt ℂ (fun v => Ring.inverse (repair (A v) w ψ) w) z :=
    ((ContinuousLinearMap.apply ℂ E w).analyticAt _).comp
      (f := fun v : ℂ => Ring.inverse (repair (A v) w ψ)) hi
  exact analyticAt_const.sub ((ψ.analyticAt _).comp
    (f := fun v : ℂ => Ring.inverse (repair (A v) w ψ) w) he)

theorem scalar_hasDerivAt (A : ℂ → E →L[ℂ] E) (A₁ : E →L[ℂ] E) (w : E)
    (ψ : E →L[ℂ] ℂ) (z : ℂ) (hA : HasDerivAt A A₁ z)
    (hu : IsUnit (repair (A z) w ψ)) :
    HasDerivAt (fun v => scalar (A v) w ψ)
      (ψ (Ring.inverse (repair (A z) w ψ) (A₁ (Ring.inverse (repair (A z) w ψ) w)))) z := by
  have hC : HasDerivAt (fun v => repair (A v) w ψ) A₁ z := by
    simpa only [add_zero] using hA.add_const (ψ.smulRight w)
  have hi := inverse_hasDerivAt _ A₁ z hC hu
  have he := hi.clm_apply (hasDerivAt_const z w)
  have hp := ψ.hasFDerivAt.comp_hasDerivAt z he
  have hs := (hasDerivAt_const z (1 : ℂ)).sub hp
  simpa only [scalar,map_zero,add_zero,ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mul_apply,map_neg,zero_sub,neg_neg] using hs

theorem scalar_crossing (A : ℂ → E →L[ℂ] E) (A₁ : E →L[ℂ] E) (u w : E)
    (φ ψ : E →L[ℂ] ℂ) (z : ℂ) (hA : HasDerivAt A A₁ z)
    (hu : IsUnit (repair (A z) w ψ)) (hAu : A z u = 0)
    (hψ : ψ u = 1) (hφ : φ w = 1) (hann : ∀ x, φ (A z x) = 0) :
    HasDerivAt (fun v => scalar (A v) w ψ) (φ (A₁ u)) z := by
  have h := scalar_hasDerivAt A A₁ w ψ z hA hu
  rwa [repaired_inverse_vector (A z) u w ψ hu hAu hψ,
    repaired_left_inverse (A z) w φ ψ hu hφ hann] at h

end OQ14.Packet06SchurAnalytic
#print axioms OQ14.Packet06SchurAnalytic.inverse_hasDerivAt
#print axioms OQ14.Packet06SchurAnalytic.scalar_analyticAt
#print axioms OQ14.Packet06SchurAnalytic.scalar_hasDerivAt
#print axioms OQ14.Packet06SchurAnalytic.scalar_crossing
