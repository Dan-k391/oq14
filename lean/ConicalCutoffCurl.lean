import ConicalVectorPotential
import ConicalCutoffGradient

/-! Genuine weak curl of the localized conical vector potential. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalCutoffCurl
open MeasureTheory Set OQ14.Maxwell OQ14.ConicalDisplacement OQ14.ConicalVectorPotential
  OQ14.ConicalCutoffGradient
open scoped Topology

def cutVectorPotential (χ : Space → ℝ) (ν a d t : ℝ) (x : Space) : Space :=
  χ x • vectorPotential ν a d t x

def cutCurl (χ : Space → ℝ) (ν a d t : ℝ) (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i => χ x*displacement ν a d t x i+
    fderiv ℝ χ x (basis (WeakCurl.next i))*vectorPotential ν a d t x (WeakCurl.previous i)-
      fderiv ℝ χ x (basis (WeakCurl.previous i))*vectorPotential ν a d t x (WeakCurl.next i))

@[simp] theorem cutCurl_apply (χ : Space → ℝ) (ν a d t : ℝ) (x : Space) (i : Fin 3) :
    cutCurl χ ν a d t x i=χ x*displacement ν a d t x i+
      fderiv ℝ χ x (basis (WeakCurl.next i))*vectorPotential ν a d t x (WeakCurl.previous i)-
        fderiv ℝ χ x (basis (WeakCurl.previous i))*vectorPotential ν a d t x (WeakCurl.next i) := rfl

theorem potential_component_locallyIntegrable (ν a d t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    LocallyIntegrable (fun x => vectorPotential ν a d t x i) := by
  simpa only [vectorPotential,PiLp.smul_apply,smul_eq_mul,Pi.smul_apply] using
    (cross_component_locallyIntegrable ν a d t hν ha ht ht1 i).smul (-(ν+1)⁻¹)

theorem cut_weak_curl (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1)=a) (χ : Space → ℝ) (hχ : ContDiff ℝ 1 χ)
    (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    (∫ x : Space, cutVectorPotential χ ν a d t x (WeakCurl.next i)*fderiv ℝ ψ x (basis (WeakCurl.previous i)))-
      (∫ x : Space, cutVectorPotential χ ν a d t x (WeakCurl.previous i)*fderiv ℝ ψ x (basis (WeakCurl.next i)))=
        ∫ x : Space, cutCurl χ ν a d t x i*ψ x := by
  have hA (j : Fin 3) := potential_component_locallyIntegrable ν a d t hν.le ha ht ht1 j
  have hiA (j k : Fin 3) : Integrable (fun x : Space => vectorPotential ν a d t x j*(χ x*fderiv ℝ ψ x (basis k))) := by
    simpa only [smul_eq_mul] using (hA j).integrable_smul_right_of_hasCompactSupport
      (hχ.continuous.mul ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const))
      (hc.fderiv_apply ℝ (basis k)).mul_left
  have hiB (j k : Fin 3) : Integrable (fun x : Space => vectorPotential ν a d t x j*(fderiv ℝ χ x (basis k)*ψ x)) := by
    simpa only [smul_eq_mul] using (hA j).integrable_smul_right_of_hasCompactSupport
      (((hχ.continuous_fderiv le_rfl).clm_apply continuous_const).mul hψ.continuous) hc.mul_left
  have hiD : Integrable (fun x : Space => displacement ν a d t x i*(χ x*ψ x)) := by
    simpa only [smul_eq_mul] using
      (component_locallyIntegrable ν a d t hν.le ha ht ht1 i).integrable_smul_right_of_hasCompactSupport
        (hχ.continuous.mul hψ.continuous) hc.mul_left
  have he (j k : Fin 3) : (∫ x : Space, vectorPotential ν a d t x j*fderiv ℝ (fun y => χ y*ψ y) x (basis k))=
      (∫ x : Space, vectorPotential ν a d t x j*(χ x*fderiv ℝ ψ x (basis k)))+
        ∫ x : Space, vectorPotential ν a d t x j*(fderiv ℝ χ x (basis k)*ψ x) := by
    rw [← integral_add (hiA j k) (hiB j k)]
    apply integral_congr_ae
    filter_upwards with x
    rw [product_test_partial χ ψ hχ hψ x k]
    ring
  have hw := potential_weak_curl ν a d t hν ha ht ht1 hroot heq i
    (fun x => χ x*ψ x) (hχ.mul hψ) hc.mul_left
  rw [he,he] at hw
  have htL (j k : Fin 3) : (∫ x : Space, cutVectorPotential χ ν a d t x j*fderiv ℝ ψ x (basis k))=
      ∫ x : Space, vectorPotential ν a d t x j*(χ x*fderiv ℝ ψ x (basis k)) := by
    apply integral_congr_ae
    filter_upwards with x
    simp only [cutVectorPotential,PiLp.smul_apply,smul_eq_mul]
    ring
  have htR : (∫ x : Space, cutCurl χ ν a d t x i*ψ x)=
      (∫ x : Space, displacement ν a d t x i*(χ x*ψ x))+
      (∫ x : Space, vectorPotential ν a d t x (WeakCurl.previous i)*(fderiv ℝ χ x (basis (WeakCurl.next i))*ψ x))-
      (∫ x : Space, vectorPotential ν a d t x (WeakCurl.next i)*(fderiv ℝ χ x (basis (WeakCurl.previous i))*ψ x)) := by
    rw [← integral_add hiD (hiB (WeakCurl.previous i) (WeakCurl.next i))]
    have hI := integral_sub (hiD.add (hiB (WeakCurl.previous i) (WeakCurl.next i)))
      (hiB (WeakCurl.next i) (WeakCurl.previous i))
    simp only [Pi.add_apply] at hI
    rw [← hI]
    apply integral_congr_ae
    filter_upwards with x
    rw [cutCurl_apply]
    ring
  rw [htL,htL,htR]
  linarith

end OQ14.ConicalCutoffCurl

#print axioms OQ14.ConicalCutoffCurl.cutCurl_apply
#print axioms OQ14.ConicalCutoffCurl.potential_component_locallyIntegrable
#print axioms OQ14.ConicalCutoffCurl.cut_weak_curl
