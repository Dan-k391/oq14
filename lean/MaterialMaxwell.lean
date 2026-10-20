import MaterialField
import MagneticResponse

/-! # The actual volume solution satisfies dielectric Maxwell equations

All tests here are compact smooth functions. The incident field satisfies
the vacuum equations; the constructed response is proved to supply the
material polarization. Radiation and the local C1-test upgrade are separate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.MaterialMaxwell

open MeasureTheory Metric OQ14.Maxwell OQ14.DynamicSource OQ14.MagneticResponse
open OQ14.WeakCurl (next previous)

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

def fieldPair (E : Field) (i : Fin 3) (f : Test) : ℂ :=
  ∫ x, E x i * f.val x

def TestMaxwell (k : ℝ) (ε : Space → ℝ) (E H : Field) : Prop :=
  ∀ (i : Fin 3) (f : Test),
    curlPair (fieldPair E) i f = Complex.I * (k : ℂ) * fieldPair H i f ∧
    curlPair (fieldPair H) i f =
      -(Complex.I * (k : ℂ)) * (∫ x, (ε x : ℂ) * E x i * f.val x)

theorem classical_vacuum_testMaxwell (k : ℝ) (E H : Field)
    (hE : ∀ i, ContDiff ℝ 1 (fun x => E x i))
    (hH : ∀ i, ContDiff ℝ 1 (fun x => H x i))
    (hM : ∀ x, MaxwellAt k 1 1 E H x) : TestMaxwell k (fun _ => 1) E H := by
  intro i f
  have h := classical_maxwell_weak_form k 1 1 E H hE hH hM
    (f.val.smooth 1) f.property
  have he := congrFun h.1 i
  have hh := congrFun h.2 i
  have hp (F : Field) :
      weakCurlPairing F f.val i = curlPair (fieldPair F) i f := by
    fin_cases i <;> simp [weakCurlPairing, curlPair, fieldPair, next, previous,
      testPartial, GradientProjection.pderivative_apply]
  rw [hp] at he hh
  constructor
  · simpa only [Complex.ofReal_one, mul_one] using he
  · simpa only [Complex.ofReal_one, one_mul, mul_one, neg_mul] using hh

theorem fieldPair_add (E F : Field)
    (hE : ∀ i f, Integrable (fun x => E x i * (f : Test).val x))
    (hF : ∀ i f, Integrable (fun x => F x i * (f : Test).val x))
    (i : Fin 3) (f : Test) :
    fieldPair (fun x j => E x j + F x j) i f =
      fieldPair E i f + fieldPair F i f := by
  simp only [fieldPair, add_mul]
  exact integral_add (hE i f) (hF i f)

theorem curlPair_add (A B : Fin 3 → Test → ℂ) (i : Fin 3) (f : Test) :
    curlPair (fun j g => A j g + B j g) i f = curlPair A i f + curlPair B i f := by
  unfold curlPair
  ring

def dielectric (c : Coefficient) (x : Space) : ℝ :=
  1 + c.value (VectorFourier.coordinateMap x)

theorem dielectric_bounds (c : Coefficient) (x : Space) :
    1 ≤ dielectric c x ∧ dielectric c x ≤ 1 + c.bound := by
  unfold dielectric
  constructor
  · linarith [c.nonnegative (VectorFourier.coordinateMap x)]
  · linarith [c.bounded (VectorFourier.coordinateMap x)]

def totalMagnetic (c : Coefficient) (k : ℝ) (u : VectorL2) (incident : Field) : Field :=
  fun x i => incident x i + magnetic k (DynamicVolume.source c u) x i

theorem polarization_pairing (c : Coefficient) (k R : ℝ) (u f : VectorL2)
    (incident : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * incident x i)
    (hsol : DynamicVolume.volumeBlock c k R u = f)
    (hI : ∀ i, LocallyIntegrable (fun x => incident x i))
    (i : Fin 3) (g : Test) :
    (∫ x, (dielectric c x : ℂ) * MaterialField.total c k u incident x i * g.val x) =
      fieldPair incident i g + fieldPair (MaterialField.scattered c k u) i g +
        (∫ x, DynamicVolume.source c u i x * g.val x) := by
  have hi := PointSingularity.test_product_integrable _ _ (hI i) g.val.continuous g.property
  have hs := FieldResponse.electric_test_integrable k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u R hc)
    (MaterialField.source_compact c u R hc) i g
  change Integrable (fun x => MaterialField.scattered c k u x i * g.val x) at hs
  have his : Integrable (fun x => incident x i * g.val x +
      MaterialField.scattered c k u x i * g.val x) := hi.add hs
  have hr := PointSingularity.test_product_integrable _ _
    ((DynamicVolume.source_integrable c u R hc i).locallyIntegrable)
    g.val.continuous g.property
  have he : (fun x => (dielectric c x : ℂ) * MaterialField.total c k u incident x i * g.val x)
      =ᵐ[volume] fun x =>
        (incident x i * g.val x + MaterialField.scattered c k u x i * g.val x) +
          DynamicVolume.source c u i x * g.val x := by
    filter_upwards [MaterialField.material_relation c k R u f incident hc hincident hsol i]
      with x hx
    rw [hx]
    simp only [dielectric, Complex.ofReal_add, Complex.ofReal_one, MaterialField.total]
    ring
  rw [integral_congr_ae he, integral_add his hr, integral_add hi hs]
  rfl

/-- The actual spatial solution, with no equation assumed for the scattered
fields, satisfies both dielectric Maxwell equations on all compact smooth tests. -/
theorem volume_solution_testMaxwell (c : Coefficient) (k R : ℝ) (u f : VectorL2)
    (Einc Hinc : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * Einc x i)
    (hsol : DynamicVolume.volumeBlock c k R u = f)
    (hE : ∀ i, LocallyIntegrable (fun x => Einc x i))
    (hH : ∀ i, LocallyIntegrable (fun x => Hinc x i))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    TestMaxwell k (dielectric c) (MaterialField.total c k u Einc)
      (totalMagnetic c k u Hinc) := by
  have hρ := DynamicVolume.source_integrable c u R hc
  have hρc := MaterialField.source_compact c u R hc
  have hF := StaticNewton.material_source_ae c u
  have hEi (i : Fin 3) (g : Test) := PointSingularity.test_product_integrable _ _
    (hE i) g.val.continuous g.property
  have hHi (i : Fin 3) (g : Test) := PointSingularity.test_product_integrable _ _
    (hH i) g.val.continuous g.property
  have hEs (i : Fin 3) (g : Test) := FieldResponse.electric_test_integrable k
    (StaticCoefficient.sqrtMultiplier c u) (DynamicVolume.source c u) hρ hρc i g
  have hHs (i : Fin 3) (g : Test) := magnetic_test_integrable k
    (DynamicVolume.source c u) hρ hρc i g
  have ep (i : Fin 3) (g : Test) :
      fieldPair (MaterialField.total c k u Einc) i g =
        fieldPair Einc i g + fieldPair (MaterialField.scattered c k u) i g :=
    fieldPair_add Einc (MaterialField.scattered c k u) hEi hEs i g
  have hp (i : Fin 3) (g : Test) :
      fieldPair (totalMagnetic c k u Hinc) i g =
        fieldPair Hinc i g + fieldPair (magnetic k (DynamicVolume.source c u)) i g :=
    fieldPair_add Hinc (magnetic k (DynamicVolume.source c u)) hHi hHs i g
  intro i g
  have hm := hMax i g
  have he := electric_curl_pairing k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) hρ hρc hF i g
  have hh := magnetic_curl_pairing k (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) hρ hρc hF i g
  change curlPair (fieldPair (MaterialField.scattered c k u)) i g =
    Complex.I * (k : ℂ) * fieldPair (magnetic k (DynamicVolume.source c u)) i g at he
  change curlPair (fieldPair (magnetic k (DynamicVolume.source c u))) i g =
    -(Complex.I * (k : ℂ)) * (fieldPair (MaterialField.scattered c k u) i g +
      ∫ x, DynamicVolume.source c u i x * g.val x) at hh
  have heq : fieldPair (MaterialField.total c k u Einc) =
      fun j φ => fieldPair Einc j φ + fieldPair (MaterialField.scattered c k u) j φ := by
    funext j φ
    exact ep j φ
  have hhq : fieldPair (totalMagnetic c k u Hinc) =
      fun j φ => fieldPair Hinc j φ + fieldPair (magnetic k (DynamicVolume.source c u)) j φ := by
    funext j φ
    exact hp j φ
  constructor
  · rw [heq, curlPair_add, hp, hm.1, he]
    ring
  · rw [hhq, curlPair_add, hm.2, hh,
      polarization_pairing c k R u f Einc hc hincident hsol hE i g]
    simp only [Complex.ofReal_one, one_mul]
    unfold fieldPair
    ring

theorem small_volume_testMaxwell (c : Coefficient) (k R : ℝ) (hR : 0 ≤ R)
    (hsmall : DynamicVolume.errorBound c k R < 1) (f : VectorL2)
    (Einc Hinc : Field)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (hincident : ∀ i, (fun x => f (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * Einc x i)
    (hE : ∀ i, LocallyIntegrable (fun x => Einc x i))
    (hH : ∀ i, LocallyIntegrable (fun x => Hinc x i))
    (hMax : TestMaxwell k (fun _ => 1) Einc Hinc) :
    TestMaxwell k (dielectric c) (MaterialField.total c k (MaterialField.solution c k R f) Einc)
      (totalMagnetic c k (MaterialField.solution c k R f) Hinc) :=
  volume_solution_testMaxwell c k R _ f Einc Hinc hc hincident
    (MaterialField.solution_equation c k R hR hsmall f) hE hH hMax

end OQ14.MaterialMaxwell

#print axioms OQ14.MaterialMaxwell.classical_vacuum_testMaxwell
#print axioms OQ14.MaterialMaxwell.fieldPair_add
#print axioms OQ14.MaterialMaxwell.curlPair_add
#print axioms OQ14.MaterialMaxwell.dielectric_bounds
#print axioms OQ14.MaterialMaxwell.polarization_pairing
#print axioms OQ14.MaterialMaxwell.volume_solution_testMaxwell
#print axioms OQ14.MaterialMaxwell.small_volume_testMaxwell
