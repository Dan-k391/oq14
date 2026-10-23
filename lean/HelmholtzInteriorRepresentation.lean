import LocalHelmholtzRepresentation
import KernelGradient

/-! Actual cutoff Green identities with all derivatives transferred off the solution. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.HelmholtzInteriorRepresentation
open MeasureTheory Filter Set OQ14.Maxwell OQ14.GreenKernel OQ14.ExteriorHelmholtz
  OQ14.ExteriorGreen OQ14.LocalHelmholtzRepresentation
open scoped Topology

theorem translated_test_integrable (f g : Space → ℂ) (hf : LocallyIntegrable f)
    (hg : Continuous g) (hc : HasCompactSupport g) (x : Space) :
    Integrable (fun y => f (x-y)*g y) := by
  have hi := PointSingularity.test_product_integrable f (fun z => g (x-z)) hf
    (hg.comp (continuous_const.sub continuous_id))
    (hc.comp_homeomorph (Homeomorph.subLeft x))
  simpa only [sub_sub_self] using hi.comp_sub_left x

theorem translated_integral (f g : Space → ℂ) (x : Space) :
    (∫ y, f (x-y)*g y)=(∫ z, f z*g (x-z)) := by
  simpa only [sub_sub_self] using
    integral_sub_left_eq_self (fun z => f z*g (x-z)) volume x

theorem translated_gradient_test (k : ℝ) (ψ : Space → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) (x : Space) (i : Fin 3) :
    (∫ y, phiGradient k (x-y) i*ψ y)=(∫ y, phi k (x-y)*dcoord ψ y i) := by
  have h := KernelGradient.phi_weak_partial k i (reflect x ψ)
    ((hψ.comp (contDiff_const.sub contDiff_id)).of_le (by simp))
    (hc.comp_homeomorph (Homeomorph.subLeft x))
  simp only [reflect_partial x ψ (hψ.differentiable (by simp)),mul_neg,integral_neg,neg_neg,
    reflect] at h
  rw [translated_integral (fun z => phiGradient k z i) ψ x,
    translated_integral (phi k) (fun z => dcoord ψ z i) x]
  exact h

theorem remove_solution_derivative (k : ℝ) (χ u : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport χ) (x : Space) (i : Fin 3) :
    (∫ y, phi k (x-y)*(dcoord χ y i*dcoord u y i))=
      (∫ y, phiGradient k (x-y) i*(u y*dcoord χ y i))-
      (∫ y, phi k (x-y)*(u y*dcoord (fun z => dcoord χ z i) y i)) := by
  have hdχ := partial_contDiff hχ i
  have hdχc := hc.fderiv_apply ℝ (basis i)
  have h := translated_gradient_test k (fun y => u y*dcoord χ y i)
    (hu.mul hdχ) (hdχc.mul_left) x i
  have hi1 := translated_test_integrable (phi k)
    (fun y => u y*dcoord (fun z => dcoord χ z i) y i)
    (KernelIntegrability.phi_locallyIntegrable k)
    (hu.continuous.mul (partial_contDiff hdχ i).continuous)
    ((hdχc.fderiv_apply ℝ (basis i)).mul_left) x
  have hi2 := translated_test_integrable (phi k)
    (fun y => dcoord χ y i*dcoord u y i)
    (KernelIntegrability.phi_locallyIntegrable k)
    (hdχ.continuous.mul (partial_contDiff hu i).continuous) (hdχc.mul_right) x
  have he : (fun y => phi k (x-y)*dcoord (fun z => u z*dcoord χ z i) y i)=
      (fun y => phi k (x-y)*(u y*dcoord (fun z => dcoord χ z i) y i)+
        phi k (x-y)*(dcoord χ y i*dcoord u y i)) := by
    funext y
    rw [partial_mul (hu.differentiable (by simp) y) (hdχ.differentiable (by simp) y)]
    ring
  rw [he,integral_add hi1 hi2] at h
  linear_combination -h

def kernel (k : ℝ) (χ : Space → ℂ) (x y : Space) : ℂ :=
  phi k (x-y)*laplacian χ y-2*∑ i : Fin 3, phiGradient k (x-y) i*dcoord χ y i

theorem cutoff_source (k : ℝ) (χ u : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (heq : ∀ y ∈ tsupport χ, laplacian u y+(k : ℂ)^2*u y=0) (y : Space) :
    source k (fun z => χ z*u z) y=
      u y*laplacian χ y+2*∑ i : Fin 3, dcoord χ y i*dcoord u y i := by
  have hz : χ y*(laplacian u y+(k : ℂ)^2*u y)=0 := by
    by_cases hy : y ∈ tsupport χ
    · rw [heq y hy,mul_zero]
    · rw [image_eq_zero_of_nmem_tsupport hy,zero_mul]
  rw [source,HelmholtzTestCalculus.laplacian_mul χ u y hχ.contDiffAt hu.contDiffAt]
  linear_combination hz

theorem cutoff_representation (k : ℝ) (χ u : Space → ℂ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport χ)
    (heq : ∀ y ∈ tsupport χ, laplacian u y+(k : ℂ)^2*u y=0)
    (x : Space) (hx : χ x=1) : u x=∫ y, u y*kernel k χ x y := by
  have hiC (i : Fin 3) : Integrable (fun y => phi k (x-y)*
      (u y*dcoord (fun z => dcoord χ z i) y i)) :=
    translated_test_integrable _ _ (KernelIntegrability.phi_locallyIntegrable k)
      (hu.continuous.mul (partial_contDiff (partial_contDiff hχ i) i).continuous)
      (((hc.fderiv_apply ℝ (basis i)).fderiv_apply ℝ (basis i)).mul_left) x
  have hiB (i : Fin 3) : Integrable (fun y => phi k (x-y)*(dcoord χ y i*dcoord u y i)) :=
    translated_test_integrable _ _ (KernelIntegrability.phi_locallyIntegrable k)
      ((partial_contDiff hχ i).continuous.mul (partial_contDiff hu i).continuous)
      ((hc.fderiv_apply ℝ (basis i)).mul_right) x
  have hiG (i : Fin 3) : Integrable (fun y => phiGradient k (x-y) i*(u y*dcoord χ y i)) :=
    translated_test_integrable _ _ (KernelGradient.gradient_locallyIntegrable k i)
      (hu.continuous.mul (partial_contDiff hχ i).continuous)
      ((hc.fderiv_apply ℝ (basis i)).mul_left) x
  have hs : (fun y => phi k (x-y)*source k (fun z => χ z*u z) y)=
      (fun y => ∑ i : Fin 3, (phi k (x-y)*(u y*dcoord (fun z => dcoord χ z i) y i)+
        2*(phi k (x-y)*(dcoord χ y i*dcoord u y i)))) := by
    funext y
    rw [cutoff_source k χ u hχ hu heq y]
    simp only [laplacian,Fin.sum_univ_three]
    ring
  have h := compact_representation k (fun y => χ y*u y) (hχ.mul hu) hc.mul_right x
  simp only [hx,one_mul] at h
  rw [hs,integral_finset_sum (Finset.univ : Finset (Fin 3))
    (f := fun i y => phi k (x-y)*(u y*dcoord (fun z => dcoord χ z i) y i)+
      2*(phi k (x-y)*(dcoord χ y i*dcoord u y i)))
    (fun i _ => (hiC i).add ((hiB i).const_mul 2))] at h
  simp_rw [integral_add (hiC _) ((hiB _).const_mul 2),integral_const_mul,
    remove_solution_derivative k χ u hχ hu hc] at h
  have hk : (fun y => u y*kernel k χ x y)=
      (fun y => ∑ i : Fin 3, (phi k (x-y)*(u y*dcoord (fun z => dcoord χ z i) y i)-
        2*(phiGradient k (x-y) i*(u y*dcoord χ y i)))) := by
    funext y
    simp only [kernel,laplacian,Fin.sum_univ_three]
    ring
  rw [hk,integral_finset_sum (Finset.univ : Finset (Fin 3))
    (f := fun i y => phi k (x-y)*(u y*dcoord (fun z => dcoord χ z i) y i)-
      2*(phiGradient k (x-y) i*(u y*dcoord χ y i)))
    (fun i _ => (hiC i).sub ((hiG i).const_mul 2))]
  simp_rw [integral_sub (hiC _) ((hiG _).const_mul 2),integral_const_mul]
  simp only [Fin.sum_univ_three] at h ⊢
  linear_combination h

end OQ14.HelmholtzInteriorRepresentation
#print axioms OQ14.HelmholtzInteriorRepresentation.translated_test_integrable
#print axioms OQ14.HelmholtzInteriorRepresentation.translated_integral
#print axioms OQ14.HelmholtzInteriorRepresentation.translated_gradient_test
#print axioms OQ14.HelmholtzInteriorRepresentation.remove_solution_derivative
#print axioms OQ14.HelmholtzInteriorRepresentation.cutoff_source
#print axioms OQ14.HelmholtzInteriorRepresentation.cutoff_representation
