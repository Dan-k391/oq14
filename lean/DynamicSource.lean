import KernelSource

/-! # Exact distributional Maxwell dyadic source

All pairings below are integrals of the actual outgoing scalar kernel against
actual derivatives of compact smooth test functions. The singular Hessian is
retained, and its dynamic difference is an ordinary locally integrable kernel.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace OQ14.DynamicSource

open MeasureTheory OQ14.Maxwell OQ14.GreenKernel
open scoped SchwartzMap ContDiff

abbrev Test := {f : 𝓢(Space, ℂ) // HasCompactSupport (f : Space → ℂ)}

def testPartial (i : Fin 3) (f : Test) : Test :=
  ⟨GradientProjection.pderivative i f.val, f.property.fderiv_apply ℝ (basis i)⟩

theorem partial_commute (i j : Fin 3) (f : Test) :
    testPartial i (testPartial j f) = testPartial j (testPartial i f) := by
  apply Subtype.ext
  ext x
  exact Maxwell.partial_comm (f.val.smooth 2) x i j

def scalarPair (k : ℝ) (f : Test) : ℂ := ∫ x, phi k x * f.val x

theorem scalar_helmholtz (k : ℝ) (f : Test) :
    (∑ i : Fin 3, scalarPair k (testPartial i (testPartial i f))) +
      (k : ℂ)^2 * scalarPair k f = -f.val 0 :=
  KernelSource.outgoing_weak_helmholtz k f.val f.val.smooth' f.property

def dyadicPair (k : ℝ) (i j : Fin 3) (f : Test) : ℂ :=
  (k : ℂ)^2 * (if i = j then 1 else 0) * scalarPair k f +
    scalarPair k (testPartial j (testPartial i f))

/-- Full static distribution plus the ordinary dynamic remainder. -/
theorem dyadic_decomposition (k : ℝ) (i j : Fin 3) (f : Test) :
    dyadicPair k i j f =
      NewtonHessian.weakHessian j i f.val +
        ∫ x, DyadicKernel.remainder k x i j * f.val x := by
  have hp : Integrable (fun x => phi k x * f.val x) :=
    PointSingularity.test_product_integrable _ _ (KernelIntegrability.phi_locallyIntegrable k)
      f.val.continuous f.property
  have hh : Integrable (fun x => KernelSource.hessianDifference k i j x * f.val x) :=
    PointSingularity.test_product_integrable _ _
      (KernelSource.hessianDifference_locallyIntegrable k i j) f.val.continuous f.property
  have he : (fun x => DyadicKernel.remainder k x i j * f.val x) =
      fun x => ((k : ℂ)^2 * (if i = j then 1 else 0)) * (phi k x * f.val x) +
        KernelSource.hessianDifference k i j x * f.val x := by
    funext x
    simp only [DyadicKernel.remainder, DyadicKernel.dyadic, KernelSource.hessianDifference]
    ring
  rw [he, integral_add (hp.const_mul _) hh, integral_const_mul]
  unfold dyadicPair scalarPair
  change _ + (∫ x, phi k x * dcoord (fun y => dcoord f.val y i) x j) = _
  rw [KernelSource.outgoing_hessian_decomposition k i j f.val (f.val.smooth 2) f.property]
  have hn : NewtonHessian.weakHessian j i f.val =
      ∫ x, phi 0 x * dcoord (fun y => dcoord f.val y i) x j := rfl
  rw [hn]
  ring

theorem dyadic_symmetric (k : ℝ) (i j : Fin 3) (f : Test) :
    dyadicPair k i j f = dyadicPair k j i f := by
  simp only [dyadicPair, partial_commute j i f, eq_comm]

private theorem partial_three (i j : Fin 3) (f : Test) :
    testPartial j (testPartial i (testPartial i f)) = testPartial i (testPartial i (testPartial j f)) := by
  rw [partial_commute j i, partial_commute j i]

theorem dyadic_divergence_pairing (k : ℝ) (j : Fin 3) (f : Test) :
    (∑ i : Fin 3, dyadicPair k i j (testPartial i f)) = -(testPartial j f).val 0 := by
  simp only [dyadicPair, Finset.sum_add_distrib]
  have hd : (∑ i : Fin 3, (k : ℂ)^2 * (if i = j then 1 else 0) *
      scalarPair k (testPartial i f)) = (k : ℂ)^2 * scalarPair k (testPartial j f) := by
    simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp
  rw [hd, add_comm]
  have hs : (∑ i : Fin 3, scalarPair k (testPartial j (testPartial i (testPartial i f)))) =
      ∑ i : Fin 3, scalarPair k (testPartial i (testPartial i (testPartial j f))) :=
    Finset.sum_congr rfl (fun i _ => congrArg (scalarPair k) (partial_three i j f))
  rw [hs]
  exact scalar_helmholtz k (testPartial j f)

private theorem partial_four (i j l : Fin 3) (f : Test) :
    testPartial j (testPartial i (testPartial l (testPartial l f))) =
      testPartial l (testPartial l (testPartial j (testPartial i f))) := by
  rw [partial_three l i f, partial_three l j (testPartial i f)]

theorem dyadic_helmholtz_pairing (k : ℝ) (i j : Fin 3) (f : Test) :
    (∑ l : Fin 3, dyadicPair k i j (testPartial l (testPartial l f))) +
      (k : ℂ)^2 * dyadicPair k i j f =
        -((k : ℂ)^2 * (if i = j then 1 else 0) * f.val 0 +
          (testPartial j (testPartial i f)).val 0) := by
  have h0 := scalar_helmholtz k f
  have h2 := scalar_helmholtz k (testPartial j (testPartial i f))
  simp only [dyadicPair, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hs : (∑ l : Fin 3, scalarPair k
      (testPartial j (testPartial i (testPartial l (testPartial l f))))) =
      ∑ l : Fin 3, scalarPair k
        (testPartial l (testPartial l (testPartial j (testPartial i f)))) :=
    Finset.sum_congr rfl (fun l _ => congrArg (scalarPair k) (partial_four i j l f))
  rw [hs]
  linear_combination (k : ℂ)^2 * (if i = j then 1 else 0 : ℂ) * h0 + h2

/-- In actual coordinate weak derivatives, (curl curl - k²)K = k² I δ.
The first sum is the gradient of the divergence; the second is the Laplacian. -/
theorem dyadic_maxwell_source (k : ℝ) (i j : Fin 3) (f : Test) :
    (∑ l : Fin 3, dyadicPair k l j (testPartial l (testPartial i f))) -
      (∑ l : Fin 3, dyadicPair k i j (testPartial l (testPartial l f))) -
        (k : ℂ)^2 * dyadicPair k i j f =
          (k : ℂ)^2 * (if i = j then 1 else 0) * f.val 0 := by
  rw [dyadic_divergence_pairing k j (testPartial i f)]
  have h := dyadic_helmholtz_pairing k i j f
  linear_combination -h

end OQ14.DynamicSource

#print axioms OQ14.DynamicSource.partial_commute
#print axioms OQ14.DynamicSource.scalar_helmholtz
#print axioms OQ14.DynamicSource.dyadic_decomposition
#print axioms OQ14.DynamicSource.dyadic_symmetric
#print axioms OQ14.DynamicSource.dyadic_divergence_pairing
#print axioms OQ14.DynamicSource.dyadic_helmholtz_pairing
#print axioms OQ14.DynamicSource.dyadic_maxwell_source
