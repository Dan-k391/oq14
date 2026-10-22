import FiniteHerglotzFlux
import SphereParityMaxwell

/-! Actual finite parity point illuminations satisfy both global Maxwell equations. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteSphereMaxwell
open SphereReactionKernel (reaction)
open SphereMagneticParity (magneticReaction)
open Maxwell (Field MaxwellAt dcoord curl partial_const_mul basis)
open WeakCurl (next previous)
open FiniteHerglotzFlux (electric magnetic)
abbrev Space := FourierL2.Space
variable {ι : Type*} [Fintype ι]

theorem electric_differentiable (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) (i : Fin 3) : DifferentiableAt ℝ (fun y => electric k e p j A y i) x :=
  DifferentiableAt.sum (fun s _ => (SphereParityMaxwell.electric_differentiable (e s) k x (p s) i (j s)).const_mul (A s))

theorem magnetic_differentiable (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) (i : Fin 3) : DifferentiableAt ℝ (fun y => magnetic k e p j A y i) x :=
  DifferentiableAt.sum (fun s _ => (SphereParityMaxwell.magnetic_differentiable (e s) k x (p s) i (j s)).const_mul (A s))

private theorem curl_sum (F : ι → Field) (A : ι → ℂ) (x : Space)
    (hF : ∀ s i, DifferentiableAt ℝ (fun y => F s y i) x) (i : Fin 3) :
    curl (fun y a => ∑ s, A s*F s y a) x i=∑ s, A s*curl (F s) x i := by
  have hp (a b : Fin 3) : dcoord (fun y => ∑ s, A s*F s y b) x a=∑ s, A s*dcoord (fun y => F s y b) x a := by
    unfold dcoord
    rw [fderiv_sum (fun s _ => (hF s b).const_mul (A s))]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro s _
    exact partial_const_mul (hF s b) (A s) a
  have hc (G : Field) : curl G x i=dcoord (fun y => G y (previous i)) x (next i)-
      dcoord (fun y => G y (next i)) x (previous i) := by fin_cases i <;> rfl
  rw [hc, hp, hp, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  rw [hc]
  ring

theorem maxwell (k : ℝ) (e : ι → Bool) (p : ι → Space) (j : ι → Fin 3)
    (A : ι → ℂ) (x : Space) : MaxwellAt k 1 1 (electric k e p j A) (magnetic k e p j A) x := by
  constructor
  · funext i
    change curl (fun y a => ∑ s, A s*reaction (e s) k y (p s) a (j s)) x i=_
    rw [curl_sum _ A x (fun s i => SphereParityMaxwell.electric_differentiable (e s) k x (p s) i (j s))]
    simp_rw [SphereMagneticParity.curl_reaction]
    simp only [electric, magnetic, Complex.ofReal_one, mul_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  · funext i
    change curl (fun y a => ∑ s, A s*magneticReaction (e s) k y (p s) a (j s)) x i=_
    rw [curl_sum _ A x (fun s i => SphereParityMaxwell.magnetic_differentiable (e s) k x (p s) i (j s))]
    simp_rw [SphereParityMaxwell.curl_magnetic]
    simp only [electric, magnetic, Complex.ofReal_one, mul_one, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring

end OQ14.FiniteSphereMaxwell
#print axioms OQ14.FiniteSphereMaxwell.electric_differentiable
#print axioms OQ14.FiniteSphereMaxwell.magnetic_differentiable
#print axioms OQ14.FiniteSphereMaxwell.maxwell
