import MaterialMaxwell

/-! Genuine linear closure of vacuum Maxwell test equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.WeakMaxwellLinear
open MeasureTheory Maxwell MaterialMaxwell DynamicSource MagneticResponse

theorem smul_vacuum (k : ℝ) (z : ℂ) (E H : Field) (hm : TestMaxwell k (fun _ => 1) E H) :
    TestMaxwell k (fun _ => 1) (fun x i => z*E x i) (fun x i => z*H x i) := by
  intro i f
  have hp (F : Field) (j : Fin 3) (g : Test) : fieldPair (fun x a => z*F x a) j g=z*fieldPair F j g := by
    unfold fieldPair
    simp only [mul_assoc,integral_const_mul]
  have hfun (F : Field) : fieldPair (fun x a => z*F x a)=(fun j g => z*fieldPair F j g) := by funext j g; exact hp F j g
  have hc (F : Field) : curlPair (fun j g => z*fieldPair F j g) i f=z*curlPair (fieldPair F) i f := by unfold curlPair; ring
  have hh := hm i f
  simp only [Complex.ofReal_one,one_mul] at hh ⊢
  change curlPair (fieldPair (fun x a => z*E x a)) i f=_ ∧ curlPair (fieldPair (fun x a => z*H x a)) i f=_
  rw [hfun E,hfun H,hc,hc]
  constructor
  · rw [hh.1]; ring
  · rw [hh.2]
    simp only [fieldPair,mul_assoc,integral_const_mul]
    ring

theorem add_vacuum (k : ℝ) (E H F G : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hF : ∀ i, LocallyIntegrable (fun x => F x i)) (hG : ∀ i, LocallyIntegrable (fun x => G x i))
    (hm : TestMaxwell k (fun _ => 1) E H) (hn : TestMaxwell k (fun _ => 1) F G) :
    TestMaxwell k (fun _ => 1) (fun x i => E x i+F x i) (fun x i => H x i+G x i) := by
  have hEi (i : Fin 3) (g : Test) : Integrable (fun x : Space => E x i*g.val x) :=
    PointSingularity.test_product_integrable _ _ (hE i) g.val.continuous g.property
  have hHi (i : Fin 3) (g : Test) : Integrable (fun x : Space => H x i*g.val x) :=
    PointSingularity.test_product_integrable _ _ (hH i) g.val.continuous g.property
  have hFi (i : Fin 3) (g : Test) : Integrable (fun x : Space => F x i*g.val x) :=
    PointSingularity.test_product_integrable _ _ (hF i) g.val.continuous g.property
  have hGi (i : Fin 3) (g : Test) : Integrable (fun x : Space => G x i*g.val x) :=
    PointSingularity.test_product_integrable _ _ (hG i) g.val.continuous g.property
  have heq : fieldPair (fun x i => E x i+F x i)=(fun i g => fieldPair E i g+fieldPair F i g) := by
    funext i g
    exact fieldPair_add E F hEi hFi i g
  have hhq : fieldPair (fun x i => H x i+G x i)=(fun i g => fieldPair H i g+fieldPair G i g) := by
    funext i g
    exact fieldPair_add H G hHi hGi i g
  intro i f
  have hm' := hm i f
  have hn' := hn i f
  simp only [Complex.ofReal_one,one_mul] at hm' hn' ⊢
  change curlPair (fieldPair (fun x a => E x a+F x a)) i f=_ ∧ curlPair (fieldPair (fun x a => H x a+G x a)) i f=_
  rw [heq,hhq,curlPair_add,curlPair_add]
  constructor
  · rw [hm'.1,hn'.1]; ring
  · rw [hm'.2,hn'.2]
    simp only [add_mul,integral_add (hEi i f) (hFi i f)]
    ring

end OQ14.WeakMaxwellLinear
#print axioms OQ14.WeakMaxwellLinear.smul_vacuum
#print axioms OQ14.WeakMaxwellLinear.add_vacuum
