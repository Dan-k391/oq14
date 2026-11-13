import Packet04WeakSphereMaxwell

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04VectorTests
open Complex MeasureTheory Set OQ14.Maxwell OQ14.ExteriorHelmholtz
open OQ14.RegionalMaxwellHelmholtz OQ14.WeakAnnularMoment
open OQ14.WeakCurl (next previous)

theorem curl_component (F : Field) (x : Space) (i : Fin 3) :
    curl F x i = dcoord (fun y => F y (previous i)) x (next i) -
      dcoord (fun y => F y (next i)) x (previous i) := by
  fin_cases i <;> rfl

theorem vector_integrable (Ω : Set Space) (E : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (F : Fin 3 → Test Ω) :
    Integrable (fun x => ∑ i : Fin 3, E x i * curl (fun y j => (F j).val y) x i) := by
  apply integrable_finset_sum
  intro i _
  simp only [curl_component, mul_sub]
  apply Integrable.sub <;> apply integrable_mul_compact _ _ (hE i)
  · exact partial_continuous ((F (previous i)).property.1.of_le (by simp)) (next i)
  · exact (F (previous i)).property.2.1.fderiv_apply ℝ (basis (next i))
  · exact partial_continuous ((F (next i)).property.1.of_le (by simp)) (previous i)
  · exact (F (next i)).property.2.1.fderiv_apply ℝ (basis (previous i))

theorem vector_pair (Ω : Set Space) (E : Field)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i)) (F : Fin 3 → Test Ω) :
    (∑ i : Fin 3, curlPair (fieldPair E) i (F i)) =
      ∫ x, ∑ i : Fin 3, E x i * curl (fun y j => (F j).val y) x i := by
  have hi (i j k : Fin 3) : Integrable (fun x => E x i * dcoord (F j).val x k) :=
    integrable_mul_compact _ _ (hE i)
      (partial_continuous ((F j).property.1.of_le (by simp)) k)
      ((F j).property.2.1.fderiv_apply ℝ (basis k))
  simp_rw [curl_component, mul_sub]
  have hsum : (∫ x, ∑ i : Fin 3,
      (E x i * dcoord (F (previous i)).val x (next i) -
       E x i * dcoord (F (next i)).val x (previous i))) =
      ∑ i : Fin 3, ∫ x,
      (E x i * dcoord (F (previous i)).val x (next i) -
       E x i * dcoord (F (next i)).val x (previous i)) :=
    integral_finset_sum Finset.univ (fun i _ =>
      (hi i (previous i) (next i)).sub (hi i (next i) (previous i)))
  rw [hsum]
  simp_rw [integral_sub (hi _ _ _) (hi _ _ _)]
  simp only [Fin.sum_univ_three, curlPair, fieldPair, testPartial, next, previous]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

theorem vector_rhs (Ω : Set Space) (H : Field)
    (hH : ∀ i, LocallyIntegrable (fun x => H x i)) (F : Fin 3 → Test Ω) :
    (∑ i : Fin 3, fieldPair H i (F i)) = ∫ x, ∑ i : Fin 3, H x i * (F i).val x := by
  symm
  exact integral_finset_sum _ (fun i _ =>
    integrable_mul_compact _ _ (hH i) (F i).property.1.continuous (F i).property.2.1)

theorem weak_vector_curl (Ω : Set Space) (E H : Field) (a : ℂ)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hH : ∀ i, LocallyIntegrable (fun x => H x i))
    (hcurl : ∀ (i : Fin 3) (f : Test Ω), curlPair (fieldPair E) i f = a * fieldPair H i f)
    (F : Fin 3 → Test Ω) :
    (∫ x, ∑ i : Fin 3, E x i * curl (fun y j => (F j).val y) x i) =
      a * ∫ x, ∑ i : Fin 3, H x i * (F i).val x := by
  rw [← vector_pair Ω E hE F, ← vector_rhs Ω H hH F]
  simp only [hcurl, Finset.mul_sum]

end OQ14.Packet04VectorTests
#print axioms OQ14.Packet04VectorTests.curl_component
#print axioms OQ14.Packet04VectorTests.vector_integrable
#print axioms OQ14.Packet04VectorTests.vector_pair
#print axioms OQ14.Packet04VectorTests.vector_rhs
#print axioms OQ14.Packet04VectorTests.weak_vector_curl
