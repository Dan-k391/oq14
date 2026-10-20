import WeakHelmholtzRegularity
import WeakPoynting.Conservation

/-! # Actual regional weak Maxwell equations imply scalar weak Helmholtz -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace OQ14.RegionalMaxwellHelmholtz

open Complex MeasureTheory Filter Set OQ14.Maxwell OQ14.ExteriorGreen OQ14.ExteriorHelmholtz
  OQ14.WeakHelmholtzRegularity
open OQ14.WeakCurl (next previous)
open scoped Topology

abbrev Test (Ω : Set Space) := {f : Space → ℂ //
  ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω}

theorem partial_tsupport (f : Space → ℂ) (i : Fin 3) :
    tsupport (fun x => dcoord f x i) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  exact hx (by simp only [dcoord,fderiv_of_not_mem_tsupport ℝ hn,
    ContinuousLinearMap.zero_apply])

def testPartial {Ω : Set Space} (i : Fin 3) (f : Test Ω) : Test Ω :=
  ⟨fun x => dcoord f.val x i, partial_contDiff f.property.1 i,
    f.property.2.1.fderiv_apply ℝ (basis i), (partial_tsupport f.val i).trans f.property.2.2⟩

theorem testPartial_commute {Ω : Set Space} (i j : Fin 3) (f : Test Ω) :
    testPartial i (testPartial j f) = testPartial j (testPartial i f) := by
  apply Subtype.ext
  funext x
  exact partial_comm (f.property.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) x i j

def curlPair {Ω : Set Space} (A : Fin 3 → Test Ω → ℂ) (i : Fin 3) (f : Test Ω) : ℂ :=
  A (next i) (testPartial (previous i) f)-A (previous i) (testPartial (next i) f)

def divPair {Ω : Set Space} (A : Fin 3 → Test Ω → ℂ) (f : Test Ω) : ℂ :=
  ∑ i : Fin 3, A i (testPartial i f)

def lapPair {Ω : Set Space} (A : Fin 3 → Test Ω → ℂ) (i : Fin 3) (f : Test Ω) : ℂ :=
  ∑ j : Fin 3, A i (testPartial j (testPartial j f))

theorem div_curlPair {Ω : Set Space} (A : Fin 3 → Test Ω → ℂ) (f : Test Ω) :
    divPair (curlPair A) f = 0 := by
  have h01 := testPartial_commute (0 : Fin 3) 1 f
  have h02 := testPartial_commute (0 : Fin 3) 2 f
  have h12 := testPartial_commute (1 : Fin 3) 2 f
  simp [divPair,curlPair,next,previous,Fin.sum_univ_three,h01,h02,h12]
  ring

theorem curlPair_curlPair {Ω : Set Space} (A : Fin 3 → Test Ω → ℂ) (i : Fin 3) (f : Test Ω) :
    curlPair (curlPair A) i f = divPair A (testPartial i f)-lapPair A i f := by
  have h01 := testPartial_commute (0 : Fin 3) 1 f
  have h02 := testPartial_commute (0 : Fin 3) 2 f
  have h12 := testPartial_commute (1 : Fin 3) 2 f
  fin_cases i <;>
    simp [divPair,lapPair,curlPair,next,previous,Fin.sum_univ_three,h01,h02,h12] <;> ring

theorem divPair_zero_of_curl {Ω : Set Space} (A B : Fin 3 → Test Ω → ℂ)
    (a : ℂ) (ha : a ≠ 0) (hcurl : ∀ i f, curlPair A i f = a*B i f) (f : Test Ω) :
    divPair B f = 0 := by
  have h := div_curlPair A f
  have heq : divPair (curlPair A) f = a*divPair B f := by
    simp only [divPair,hcurl,Finset.mul_sum]
  rw [heq] at h
  exact (mul_eq_zero.mp h).resolve_left ha

theorem pair_helmholtz {Ω : Set Space} (A B : Fin 3 → Test Ω → ℂ)
    (a b : ℂ) (hb : b ≠ 0)
    (hA : ∀ i f, curlPair A i f = a*B i f)
    (hB : ∀ i f, curlPair B i f = b*A i f) (i : Fin 3) (f : Test Ω) :
    lapPair A i f+(a*b)*A i f = 0 := by
  have hdiv := divPair_zero_of_curl B A b hb hB (testPartial i f)
  have hcc := curlPair_curlPair A i f
  have heq : curlPair (curlPair A) i f = (a*b)*A i f := by
    change curlPair A (next i) (testPartial (previous i) f)-
      curlPair A (previous i) (testPartial (next i) f) = _
    rw [hA,hA]
    have h := hB i f
    dsimp only [curlPair] at h
    linear_combination a*h
  rw [heq,hdiv] at hcc
  linear_combination hcc

def fieldPair {Ω : Set Space} (E : Field) (i : Fin 3) (f : Test Ω) : ℂ :=
  ∫ x, E x i*f.val x

def TestMaxwell (k ε : ℝ) (Ω : Set Space) (E H : Field) : Prop :=
  ∀ (i : Fin 3) (f : Test Ω),
    curlPair (fieldPair E) i f = (Complex.I*(k : ℂ))*fieldPair H i f ∧
    curlPair (fieldPair H) i f = (-(Complex.I*(k : ℂ)*(ε : ℂ)))*fieldPair E i f

def IntegrableTests (Ω : Set Space) (E : Field) : Prop :=
  ∀ (i : Fin 3) (f : Test Ω), Integrable (fun x => E x i*f.val x)

theorem locallyIntegrable_integrableTests (Ω : Set Space) (E : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) : IntegrableTests Ω E :=
  fun i f => PointSingularity.test_product_integrable _ _ (hE i)
    f.property.1.continuous f.property.2.1

theorem maxwell_electric_lapPair (k ε : ℝ) (hk : k ≠ 0) (hε : ε ≠ 0)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H) (i : Fin 3) (f : Test Ω) :
    lapPair (fieldPair E) i f+((k : ℂ)^2*(ε : ℂ))*fieldPair E i f = 0 := by
  have hb : -(Complex.I*(k : ℂ)*(ε : ℂ)) ≠ 0 :=
    neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hk))
      (ofReal_ne_zero.mpr hε))
  have h := pair_helmholtz (fieldPair E) (fieldPair H) (I*(k : ℂ))
    (-(I*(k : ℂ)*(ε : ℂ))) hb (fun j g => (hM j g).1) (fun j g => (hM j g).2) i f
  convert h using 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

theorem maxwell_electric_divPair (k ε : ℝ) (hk : k ≠ 0) (hε : ε ≠ 0)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H) (f : Test Ω) :
    divPair (fieldPair E) f = 0 :=
  divPair_zero_of_curl (fieldPair H) (fieldPair E) (-(I*(k : ℂ)*(ε : ℂ)))
    (neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hk))
      (ofReal_ne_zero.mpr hε))) (fun i g => (hM i g).2) f

theorem maxwell_magnetic_divPair (k ε : ℝ) (hk : k ≠ 0)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H) (f : Test Ω) :
    divPair (fieldPair H) f = 0 :=
  divPair_zero_of_curl (fieldPair E) (fieldPair H) (I*(k : ℂ))
    (mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hk)) (fun i g => (hM i g).1) f

theorem maxwell_magnetic_lapPair (k ε : ℝ) (hk : k ≠ 0)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H) (i : Fin 3) (f : Test Ω) :
    lapPair (fieldPair H) i f+((k : ℂ)^2*(ε : ℂ))*fieldPair H i f = 0 := by
  have ha : Complex.I*(k : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hk)
  have h := pair_helmholtz (fieldPair H) (fieldPair E) (-(I*(k : ℂ)*(ε : ℂ)))
    (I*(k : ℂ)) ha (fun j g => (hM j g).2) (fun j g => (hM j g).1) i f
  convert h using 1
  congr 1
  ring_nf
  simp [Complex.I_sq]

theorem fieldPair_helmholtz_integral (κ : ℂ) (Ω : Set Space) (E : Field)
    (hE : IntegrableTests Ω E) (i : Fin 3) (f : Test Ω) :
    (∫ x, E x i*(laplacian f.val x+κ^2*f.val x)) =
      lapPair (fieldPair E) i f+κ^2*fieldPair E i f := by
  have hi (j : Fin 3) : Integrable
      (fun x => E x i*dcoord (fun y => dcoord f.val y j) x j) :=
    hE i (testPartial j (testPartial j f))
  have h0 := hE i f
  have heq : (fun x => E x i*(laplacian f.val x+κ^2*f.val x)) =
      fun x => (∑ j : Fin 3, E x i*dcoord (fun y => dcoord f.val y j) x j)+
        κ^2*(E x i*f.val x) := by
    funext x
    simp only [laplacian,mul_add,Finset.mul_sum]
    ring
  rw [heq,integral_add (integrable_finset_sum _ (fun j _ => hi j)) (h0.const_mul _),
    integral_finset_sum _ (fun j _ => hi j),integral_const_mul]
  rfl

theorem material_frequency_square (k ε : ℝ) (hε : 0 ≤ ε) :
    (((k*Real.sqrt ε : ℝ) : ℂ))^2 = (k : ℂ)^2*(ε : ℂ) := by
  exact_mod_cast (show (k*Real.sqrt ε)^2 = k^2*ε by rw [mul_pow,Real.sq_sqrt hε])

theorem electric_weak_helmholtz (k ε : ℝ) (hk : k ≠ 0) (hε : 0 < ε)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H)
    (hE : IntegrableTests Ω E) (i : Fin 3) :
    IsWeakHelmholtz ((k*Real.sqrt ε : ℝ) : ℂ) Ω (fun x => E x i) := by
  intro φ hφ hc hs
  let f : Test Ω := ⟨φ,hφ,hc,hs⟩
  change (∫ x, E x i*(laplacian f.val x+(((k*Real.sqrt ε : ℝ) : ℂ))^2*f.val x)) = 0
  rw [fieldPair_helmholtz_integral _ Ω E hE i f,material_frequency_square k ε hε.le]
  exact maxwell_electric_lapPair k ε hk hε.ne' Ω E H hM i f

theorem magnetic_weak_helmholtz (k ε : ℝ) (hk : k ≠ 0) (hε : 0 < ε)
    (Ω : Set Space) (E H : Field) (hM : TestMaxwell k ε Ω E H)
    (hH : IntegrableTests Ω H) (i : Fin 3) :
    IsWeakHelmholtz ((k*Real.sqrt ε : ℝ) : ℂ) Ω (fun x => H x i) := by
  intro φ hφ hc hs
  let f : Test Ω := ⟨φ,hφ,hc,hs⟩
  change (∫ x, H x i*(laplacian f.val x+(((k*Real.sqrt ε : ℝ) : ℂ))^2*f.val x)) = 0
  rw [fieldPair_helmholtz_integral _ Ω H hH i f,material_frequency_square k ε hε.le]
  exact maxwell_magnetic_lapPair k ε hk Ω E H hM i f

def domainTest {Ω : Set Space} (f : Test Ω) : DomainCurl.Test Ω where
  function := f.val
  regular := f.property.1.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  compact := f.property.2.1
  inside := f.property.2.2

def domainField {Ω : Set Space} (E : DomainCurl.L2Vector Ω) : Field := fun x i => E i x

theorem test_zero_outside {Ω : Set Space} (f : Test Ω) (x : Space) (hx : x ∉ Ω) : f.val x = 0 := by
  by_contra hn
  exact hx (f.property.2.2 (subset_closure hn))

theorem domain_fieldPair_integral (Ω : Set Space) (E : DomainCurl.L2Vector Ω)
    (i : Fin 3) (f : Test Ω) :
    fieldPair (domainField E) i f = ∫ x in Ω, E i x*f.val x := by
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp only [test_zero_outside f x hx,mul_zero])).symm

theorem domain_integrableTests (Ω : Set Space) (E : DomainCurl.L2Vector Ω) :
    IntegrableTests Ω (domainField E) := by
  intro i f
  apply (integrableOn_iff_integrable_of_support_subset (s := Ω) ?_).mp
  · exact DomainCurl.testPair_integrable Ω f.val f.property.1.continuous f.property.2.1 (E i)
  · intro x hx
    by_contra hn
    exact hx (by simp only [domainField,test_zero_outside f x hn,mul_zero])

theorem domain_curl_pairing (Ω : Set Space) (E : DomainCurl.HCurl Ω)
    (i : Fin 3) (f : Test Ω) :
    curlPair (fieldPair (domainField E.val.1)) i f = ∫ x in Ω, E.val.2 i x*f.val x := by
  have h := (DomainCurl.hasWeakCurl_iff_integral Ω E.val.1 E.val.2).mp E.property (domainTest f) i
  change _ = (∫ x in Ω, E.val.1 (next i) x*dcoord f.val x (previous i))-
    (∫ x in Ω, E.val.1 (previous i) x*dcoord f.val x (next i)) at h
  rw [curlPair,domain_fieldPair_integral,domain_fieldPair_integral]
  exact h.symm

theorem domain_testMaxwell (k ε : ℝ) (Ω : Set Space) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) (fun _ => ε) E H) :
    TestMaxwell k ε Ω (domainField E.val.1) (domainField H.val.1) := by
  intro i f
  constructor
  · rw [domain_curl_pairing,domain_fieldPair_integral,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hM.1] with x hx
    rw [hx i]
    simp only [Complex.ofReal_one,mul_one]
    ring
  · rw [domain_curl_pairing,domain_fieldPair_integral,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hM.2] with x hx
    rw [hx i]
    ring

theorem domain_electric_weak_helmholtz (k ε : ℝ) (hk : k ≠ 0) (hε : 0 < ε)
    (Ω : Set Space) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) (fun _ => ε) E H) (i : Fin 3) :
    IsWeakHelmholtz ((k*Real.sqrt ε : ℝ) : ℂ) Ω (fun x => E.val.1 i x) :=
  electric_weak_helmholtz k ε hk hε Ω (domainField E.val.1) (domainField H.val.1)
    (domain_testMaxwell k ε Ω E H hM) (domain_integrableTests Ω E.val.1) i

theorem domain_magnetic_weak_helmholtz (k ε : ℝ) (hk : k ≠ 0) (hε : 0 < ε)
    (Ω : Set Space) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1) (fun _ => ε) E H) (i : Fin 3) :
    IsWeakHelmholtz ((k*Real.sqrt ε : ℝ) : ℂ) Ω (fun x => H.val.1 i x) :=
  magnetic_weak_helmholtz k ε hk hε Ω (domainField E.val.1) (domainField H.val.1)
    (domain_testMaxwell k ε Ω E H hM) (domain_integrableTests Ω H.val.1) i

end OQ14.RegionalMaxwellHelmholtz

#print axioms OQ14.RegionalMaxwellHelmholtz.partial_tsupport
#print axioms OQ14.RegionalMaxwellHelmholtz.testPartial_commute
#print axioms OQ14.RegionalMaxwellHelmholtz.div_curlPair
#print axioms OQ14.RegionalMaxwellHelmholtz.curlPair_curlPair
#print axioms OQ14.RegionalMaxwellHelmholtz.divPair_zero_of_curl
#print axioms OQ14.RegionalMaxwellHelmholtz.pair_helmholtz
#print axioms OQ14.RegionalMaxwellHelmholtz.locallyIntegrable_integrableTests
#print axioms OQ14.RegionalMaxwellHelmholtz.maxwell_electric_lapPair
#print axioms OQ14.RegionalMaxwellHelmholtz.maxwell_electric_divPair
#print axioms OQ14.RegionalMaxwellHelmholtz.maxwell_magnetic_divPair
#print axioms OQ14.RegionalMaxwellHelmholtz.maxwell_magnetic_lapPair
#print axioms OQ14.RegionalMaxwellHelmholtz.fieldPair_helmholtz_integral
#print axioms OQ14.RegionalMaxwellHelmholtz.material_frequency_square
#print axioms OQ14.RegionalMaxwellHelmholtz.electric_weak_helmholtz
#print axioms OQ14.RegionalMaxwellHelmholtz.magnetic_weak_helmholtz
#print axioms OQ14.RegionalMaxwellHelmholtz.test_zero_outside
#print axioms OQ14.RegionalMaxwellHelmholtz.domain_fieldPair_integral
#print axioms OQ14.RegionalMaxwellHelmholtz.domain_integrableTests
#print axioms OQ14.RegionalMaxwellHelmholtz.domain_curl_pairing
#print axioms OQ14.RegionalMaxwellHelmholtz.domain_testMaxwell
#print axioms OQ14.RegionalMaxwellHelmholtz.domain_electric_weak_helmholtz
#print axioms OQ14.RegionalMaxwellHelmholtz.domain_magnetic_weak_helmholtz
