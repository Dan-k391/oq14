import MaterialMaxwell
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Actual electric AE zero forces magnetic AE zero in weak Maxwell -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.MaxwellZeroField

open Complex MeasureTheory Filter OQ14.Maxwell OQ14.DynamicSource
open scoped Topology

theorem fieldPair_zero_of_ae (E : Field) (hE : E =ᵐ[volume] 0) (i : Fin 3) (f : Test) :
    MaterialMaxwell.fieldPair E i f = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hE] with x hx
  simp only [hx,Pi.zero_apply,zero_mul]

theorem curlPair_zero_of_ae (E : Field) (hE : E =ᵐ[volume] 0) (i : Fin 3) (f : Test) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair E) i f = 0 := by
  simp only [MagneticResponse.curlPair,fieldPair_zero_of_ae E hE,sub_self]

theorem magnetic_testPair_zero (k : ℝ) (hk : k ≠ 0) (ε : Space → ℝ) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H) (hE : E =ᵐ[volume] 0)
    (i : Fin 3) (f : Test) : MaterialMaxwell.fieldPair H i f = 0 := by
  have he := (hM i f).1
  rw [curlPair_zero_of_ae E hE] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hk))

theorem magnetic_component_zero_of_electric_zero (k : ℝ) (hk : k ≠ 0)
    (ε : Space → ℝ) (E H : Field) (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hH : ∀ i, LocallyIntegrable (fun x => H x i)) (hE : E =ᵐ[volume] 0) (i : Fin 3) :
    (fun x => H x i) =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero (hH i)
  intro φ hφ hc
  let ψ : Space → ℂ := fun x => (φ x : ℂ)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Complex.ofRealCLM.contDiff.comp hφ
  have hψc : HasCompactSupport ψ := hc.comp_left (g := Complex.ofReal) (by simp)
  let f : Test := ⟨FourierL2.compactSmoothSchwartz ψ hψ hψc,hψc⟩
  have hz := magnetic_testPair_zero k hk ε E H hM hE i f
  change (∫ x, H x i*(φ x : ℂ)) = 0 at hz
  simpa only [Complex.real_smul,mul_comm] using hz

theorem magnetic_zero_of_electric_zero (k : ℝ) (hk : k ≠ 0)
    (ε : Space → ℝ) (E H : Field) (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hH : ∀ i, LocallyIntegrable (fun x => H x i)) (hE : E =ᵐ[volume] 0) :
    H =ᵐ[volume] 0 := by
  have hz := ae_all_iff.mpr (fun i => magnetic_component_zero_of_electric_zero k hk ε E H hM hH hE i)
  filter_upwards [hz] with x hx
  funext i
  exact hx i

end OQ14.MaxwellZeroField

#print axioms OQ14.MaxwellZeroField.fieldPair_zero_of_ae
#print axioms OQ14.MaxwellZeroField.curlPair_zero_of_ae
#print axioms OQ14.MaxwellZeroField.magnetic_testPair_zero
#print axioms OQ14.MaxwellZeroField.magnetic_component_zero_of_electric_zero
#print axioms OQ14.MaxwellZeroField.magnetic_zero_of_electric_zero
