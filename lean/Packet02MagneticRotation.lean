import Packet02SourceSymmetry
import ComplexMagneticLocal
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet02MagneticRotation
open MeasureTheory OQ14.Maxwell OQ14.ModalAxialRotation OQ14.ComplexGreenKernel

theorem gradient_covariant (z : ℂ) (θ : ℝ) (x : Space) (i : Fin 3) :
    phiGradient z (rotation θ x) i = ∑ j : Fin 3, matrix θ i j * phiGradient z x j := by
  change phiGradient z (spatial θ x) i = _
  simp only [phiGradient, spatial_norm]
  fin_cases i <;> simp [spatial, matrix,
    WithLp.equiv_symm_pi_apply, Fin.sum_univ_three, Complex.ofReal_add,
    Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div] <;> ring


theorem response_rotation (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (z : ℂ) (θ : ℝ) (x : Space) (j l : Fin 3)
    (hI : ∀ a b, Integrable (fun y => DynamicVolume.source (ModalWeightedMode.coefficient n hn) u b y * phiGradient z (x-y) a)) :
    KernelConvolution.response (fun v => phiGradient z v j)
      (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u l) (rotation θ x) =
    ∑ a : Fin 3, ∑ b : Fin 3, matrix θ j a * matrix θ l b *
      KernelConvolution.response (fun v => phiGradient z v a)
        (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u b) x := by
  unfold KernelConvolution.response
  have hc := (rotation θ).measurePreserving.integral_comp (rotation θ).toHomeomorph.measurableEmbedding
    (fun y => DynamicVolume.source (ModalWeightedMode.coefficient n hn) u l y * phiGradient z (rotation θ x-y) j)
  rw [← hc]
  have he : (∫ y, DynamicVolume.source (ModalWeightedMode.coefficient n hn) u l (rotation θ y) *
      phiGradient z (rotation θ x - rotation θ y) j) =
      ∫ y, ∑ a : Fin 3, ∑ b : Fin 3, (matrix θ j a * matrix θ l b) *
        (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u b y * phiGradient z (x-y) a) := by
    apply integral_congr_ae
    filter_upwards [Packet02SourceSymmetry.source_covariant n hn u hu θ l] with y hy
    rw [hy, ← map_sub (rotation θ), gradient_covariant]
    simp only [Fin.sum_univ_three]
    ring
  rw [he, integral_finset_sum _ (fun a _ => integrable_finset_sum _ (fun b _ => (hI a b).const_mul _))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [integral_finset_sum _ (fun b _ => (hI a b).const_mul _)]
  simp only [integral_const_mul]

theorem magnetic_covariant (n : ℝ) (hn : 1 < n) (u : VectorFourier.VectorL2)
    (hu : u ∈ axialSector) (z : ℂ) (θ : ℝ) (x : Space) (i : Fin 3)
    (hI : ∀ a b, Integrable (fun y => DynamicVolume.source (ModalWeightedMode.coefficient n hn) u b y * phiGradient z (x-y) a)) :
    ComplexMagneticLocal.magnetic z (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u) (rotation θ x) i =
      ∑ j : Fin 3, matrix θ i j * ComplexMagneticLocal.magnetic z (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u) x j := by
  unfold ComplexMagneticLocal.magnetic
  simp_rw [response_rotation n hn u hu z θ x _ _ hI]
  fin_cases i <;> simp [WeakCurl.next, WeakCurl.previous, matrix, Fin.sum_univ_three]
  · ring
  · ring
  · left
    have h : Complex.cos (θ : ℂ)^2 + Complex.sin (θ : ℂ)^2 = 1 := Complex.cos_sq_add_sin_sq _
    linear_combination (KernelConvolution.response (fun v => phiGradient z v 0) (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u 1) x - KernelConvolution.response (fun v => phiGradient z v 1) (DynamicVolume.source (ModalWeightedMode.coefficient n hn) u 0) x) * h
#print axioms OQ14.Packet02MagneticRotation.gradient_covariant
#print axioms OQ14.Packet02MagneticRotation.response_rotation
#print axioms OQ14.Packet02MagneticRotation.magnetic_covariant
end OQ14.Packet02MagneticRotation
