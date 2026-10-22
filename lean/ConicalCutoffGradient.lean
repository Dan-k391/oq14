import ConicalWeakGradient

/-! Genuine weak gradient of the radially localized conical potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace OQ14.ConicalCutoffGradient
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalCapField
open scoped Topology

def cutoffGradient (χ : Space → ℝ) (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => fderiv ℝ χ x (basis i))

@[simp] theorem cutoffGradient_apply (χ : Space → ℝ) (x : Space) (i : Fin 3) :
    cutoffGradient χ x i=fderiv ℝ χ x (basis i) := rfl

def cutPotential (χ : Space → ℝ) (ν a t : ℝ) (x : Space) : ℝ := χ x*potential ν a t x

def cutElectric (χ : Space → ℝ) (ν a t : ℝ) (x : Space) : Space :=
  χ x • electric ν a t x+potential ν a t x • cutoffGradient χ x

theorem product_test_partial (χ ψ : Space → ℝ) (hχ : ContDiff ℝ 1 χ)
    (hψ : ContDiff ℝ 1 ψ) (x : Space) (i : Fin 3) :
    fderiv ℝ (fun y => χ y*ψ y) x (basis i)=χ x*fderiv ℝ ψ x (basis i)+
      fderiv ℝ χ x (basis i)*ψ x := by
  rw [fderiv_mul ((hχ.differentiable le_rfl) x) ((hψ.differentiable le_rfl) x)]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem cut_weak_partial (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (χ : Space → ℝ) (hχ : ContDiff ℝ 1 χ)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) (i : Fin 3) :
    (∫ x : Space, cutPotential χ ν a t x*fderiv ℝ ψ x (basis i))=
      -(∫ x : Space, cutElectric χ ν a t x i*ψ x) := by
  have hU := ConicalSpatialTests.potential_locallyIntegrable ν a t hν.le ha ht ht1
  have hE := ConicalSpatialTests.electric_component_locallyIntegrable ν a t hν.le ha ht ht1 i
  have hiA : Integrable (fun x : Space => potential ν a t x*(χ x*fderiv ℝ ψ x (basis i))) := by
    simpa only [smul_eq_mul] using hU.integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const))
      (hc.fderiv_apply ℝ (basis i)).mul_left
  have hiB : Integrable (fun x : Space => potential ν a t x*(fderiv ℝ χ x (basis i)*ψ x)) := by
    simpa only [smul_eq_mul] using hU.integrable_smul_right_of_hasCompactSupport
      (((hχ.continuous_fderiv le_rfl).clm_apply continuous_const).mul hψ.continuous) hc.mul_left
  have hiC : Integrable (fun x : Space => electric ν a t x i*(χ x*ψ x)) := by
    simpa only [smul_eq_mul] using hE.integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul hψ.continuous) hc.mul_left
  have hw := ConicalWeakGradient.weak_partial ν a t hν ha ht ht1 i (fun x => χ x*ψ x)
    (hχ.mul hψ) hc.mul_left
  have heL : (fun x : Space => potential ν a t x*fderiv ℝ (fun y => χ y*ψ y) x (basis i))=
      fun x => potential ν a t x*(χ x*fderiv ℝ ψ x (basis i))+
        potential ν a t x*(fderiv ℝ χ x (basis i)*ψ x) := by
    funext x
    rw [product_test_partial χ ψ hχ hψ x i]
    ring
  rw [heL,integral_add hiA hiB] at hw
  have htA : (∫ x : Space, cutPotential χ ν a t x*fderiv ℝ ψ x (basis i))=
      ∫ x : Space, potential ν a t x*(χ x*fderiv ℝ ψ x (basis i)) := by
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [cutPotential]
    ring
  have htR : (∫ x : Space, cutElectric χ ν a t x i*ψ x)=
      (∫ x : Space, electric ν a t x i*(χ x*ψ x))+
        ∫ x : Space, potential ν a t x*(fderiv ℝ χ x (basis i)*ψ x) := by
    rw [← integral_add hiC hiB]
    apply integral_congr_ae
    filter_upwards with x
    simp only [cutElectric,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul,cutoffGradient_apply]
    ring
  rw [htA,htR]
  linarith

end OQ14.ConicalCutoffGradient

#print axioms OQ14.ConicalCutoffGradient.cutoffGradient_apply
#print axioms OQ14.ConicalCutoffGradient.product_test_partial
#print axioms OQ14.ConicalCutoffGradient.cut_weak_partial
