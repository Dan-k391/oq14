import RegionalMaxwellHelmholtz
import MaterialMaxwell

/-! # Actual global Maxwell tests localized across a material interface -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.RegionalMaxwellLocalization

open Complex MeasureTheory Filter Set OQ14.Maxwell OQ14.RegionalMaxwellHelmholtz
  OQ14.WeakHelmholtzRegularity
open OQ14.WeakCurl (next previous)
open scoped Topology

def globalTest {Ω : Set Space} (f : Test Ω) : DynamicSource.Test :=
  ⟨FourierL2.compactSmoothSchwartz f.val f.property.1 f.property.2.1,f.property.2.1⟩

theorem globalTest_partial {Ω : Set Space} (f : Test Ω) (i : Fin 3) :
    DynamicSource.testPartial i (globalTest f) = globalTest (testPartial i f) := by
  apply Subtype.ext
  ext x
  rfl

theorem global_fieldPair {Ω : Set Space} (E : Field) (i : Fin 3) (f : Test Ω) :
    MaterialMaxwell.fieldPair E i (globalTest f) = fieldPair E i f := rfl

theorem global_curlPair {Ω : Set Space} (E : Field) (i : Fin 3) (f : Test Ω) :
    MagneticResponse.curlPair (MaterialMaxwell.fieldPair E) i (globalTest f) =
      curlPair (fieldPair E) i f := by
  unfold MagneticResponse.curlPair
  rw [globalTest_partial,globalTest_partial]
  rfl

theorem weighted_fieldPair (ε : Space → ℝ) (ε₀ : ℝ) (Ω : Set Space) (E : Field)
    (hε : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i)
    (i : Fin 3) (f : Test Ω) :
    (∫ x, (ε x : ℂ)*E x i*f.val x) = (ε₀ : ℂ)*fieldPair E i f := by
  rw [fieldPair,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hε] with x hx
  by_cases hi : x ∈ Ω
  · calc
      _ = ((ε₀ : ℂ)*E x i)*f.val x := congrArg (fun z => z*f.val x) (hx hi i)
      _ = _ := by ring
  · simp only [test_zero_outside f x hi,mul_zero]

theorem regional_testMaxwell_of_global (k ε₀ : ℝ) (ε : Space → ℝ) (Ω : Set Space) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hε : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i) :
    TestMaxwell k ε₀ Ω E H := by
  intro i f
  have h := hM i (globalTest f)
  rw [global_curlPair,global_fieldPair,global_curlPair] at h
  constructor
  · exact h.1
  · have hw := weighted_fieldPair ε ε₀ Ω E hε i f
    change (∫ x, (ε x : ℂ)*E x i*(globalTest f).val x) = _ at hw
    rw [hw] at h
    linear_combination h.2

theorem weight_equality_of_contrast_zero (ε : Space → ℝ) (ε₀ : ℝ) (Ω : Set Space) (E : Field)
    (hzero : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (((ε x-ε₀ : ℝ) : ℂ))*E x i = 0) :
    ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i := by
  filter_upwards [hzero] with x hx hi i
  have h := hx hi i
  push_cast at h
  linear_combination h

theorem weight_equality_of_material_or_zero (ε : Space → ℝ) (ε₀ : ℝ) (Ω : Set Space) (E : Field)
    (hside : ∀ᵐ x : Space, x ∈ Ω → ε x = ε₀ ∨ ∀ i : Fin 3, E x i = 0) :
    ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i := by
  filter_upwards [hside] with x hx hi i
  rcases hx hi with hε | hE
  · rw [hε]
  · simp only [hE i,mul_zero]

theorem regional_testMaxwell_of_contrast_zero (k ε₀ : ℝ) (ε : Space → ℝ)
    (Ω : Set Space) (E H : Field) (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hzero : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (((ε x-ε₀ : ℝ) : ℂ))*E x i = 0) :
    TestMaxwell k ε₀ Ω E H :=
  regional_testMaxwell_of_global k ε₀ ε Ω E H hM (weight_equality_of_contrast_zero ε ε₀ Ω E hzero)

theorem electric_weak_helmholtz_of_global (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : 0 < ε₀)
    (ε : Space → ℝ) (Ω : Set Space) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hε : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (i : Fin 3) :
    IsWeakHelmholtz ((k*Real.sqrt ε₀ : ℝ) : ℂ) Ω (fun x => E x i) :=
  electric_weak_helmholtz k ε₀ hk hε₀ Ω E H
    (regional_testMaxwell_of_global k ε₀ ε Ω E H hM hε)
    (locallyIntegrable_integrableTests Ω E hE) i

theorem magnetic_weak_helmholtz_of_global (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : 0 < ε₀)
    (ε : Space → ℝ) (Ω : Set Space) (E H : Field)
    (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hε : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3, (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i)
    (hH : ∀ i, LocallyIntegrable (fun x => H x i)) (i : Fin 3) :
    IsWeakHelmholtz ((k*Real.sqrt ε₀ : ℝ) : ℂ) Ω (fun x => H x i) :=
  magnetic_weak_helmholtz k ε₀ hk hε₀ Ω E H
    (regional_testMaxwell_of_global k ε₀ ε Ω E H hM hε)
    (locallyIntegrable_integrableTests Ω H hH) i

end OQ14.RegionalMaxwellLocalization

#print axioms OQ14.RegionalMaxwellLocalization.globalTest_partial
#print axioms OQ14.RegionalMaxwellLocalization.global_fieldPair
#print axioms OQ14.RegionalMaxwellLocalization.global_curlPair
#print axioms OQ14.RegionalMaxwellLocalization.weighted_fieldPair
#print axioms OQ14.RegionalMaxwellLocalization.regional_testMaxwell_of_global
#print axioms OQ14.RegionalMaxwellLocalization.weight_equality_of_contrast_zero
#print axioms OQ14.RegionalMaxwellLocalization.weight_equality_of_material_or_zero
#print axioms OQ14.RegionalMaxwellLocalization.regional_testMaxwell_of_contrast_zero
#print axioms OQ14.RegionalMaxwellLocalization.electric_weak_helmholtz_of_global
#print axioms OQ14.RegionalMaxwellLocalization.magnetic_weak_helmholtz_of_global
