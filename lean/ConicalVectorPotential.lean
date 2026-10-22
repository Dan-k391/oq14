import ConicalDisplacement
import HCurl

/-! An actual vector potential for the homogeneous conical displacement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ConicalVectorPotential
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalCapField
  OQ14.ConicalDisplacement
open scoped Topology

def crossPosition (ν a d t : ℝ) (x : Space) : Space :=
  (WithLp.equiv 2 (Fin 3 → ℝ)).symm (fun i =>
    x (WeakCurl.next i)*displacement ν a d t x (WeakCurl.previous i)-
      x (WeakCurl.previous i)*displacement ν a d t x (WeakCurl.next i))

@[simp] theorem crossPosition_apply (ν a d t : ℝ) (x : Space) (i : Fin 3) :
    crossPosition ν a d t x i=x (WeakCurl.next i)*displacement ν a d t x (WeakCurl.previous i)-
      x (WeakCurl.previous i)*displacement ν a d t x (WeakCurl.next i) := rfl

def vectorPotential (ν a d t : ℝ) (x : Space) : Space := -(ν+1)⁻¹ • crossPosition ν a d t x

theorem coordinate_test_fderiv (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (x v : Space) : fderiv ℝ (fun y : Space => y i*ψ y) x v = v i*ψ x+x i*fderiv ℝ ψ x v := by
  have hc : HasFDerivAt (fun y : Space => y i) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) x := by
    simpa using (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt (x := x)
  have hp := hc.mul ((hψ.differentiable le_rfl) x).hasFDerivAt
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    PiLp.proj_apply,smul_eq_mul]
  ring

theorem gauss_coordinate_moment (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1)=a) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun x : Space => x i*fderiv ℝ ψ x (displacement ν a d t x)) ∧
      (∫ x : Space, x i*fderiv ℝ ψ x (displacement ν a d t x))=
        -(∫ x : Space, displacement ν a d t x i*ψ x) := by
  let ψi : Space → ℝ := fun x => x i*ψ x
  have hψi : ContDiff ℝ 1 ψi :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).contDiff.mul hψ
  have hci : HasCompactSupport ψi := hc.mul_left
  have hiF : Integrable (fun x : Space => fderiv ℝ ψi x (displacement ν a d t x)) := by
    simpa only [displacement,map_smul,smul_eq_mul] using
      ConicalStaticDivergence.electric_test_integrable ν a d t hν.le ha ht ht1 ψi hψi hci
  have hiD : Integrable (fun x : Space => displacement ν a d t x i*ψ x) := by
    simpa only [smul_eq_mul] using
      (component_locallyIntegrable ν a d t hν.le ha ht ht1 i).integrable_smul_right_of_hasCompactSupport hψ.continuous hc
  have he : (fun x : Space => fderiv ℝ ψi x (displacement ν a d t x))=
      fun x => displacement ν a d t x i*ψ x+x i*fderiv ℝ ψ x (displacement ν a d t x) :=
    funext (fun x => coordinate_test_fderiv i ψ hψ x (displacement ν a d t x))
  have hiG : Integrable (fun x : Space => x i*fderiv ℝ ψ x (displacement ν a d t x)) := by
    apply (hiF.sub hiD).congr
    filter_upwards with x
    change fderiv ℝ ψi x (displacement ν a d t x)-displacement ν a d t x i*ψ x = _
    rw [congrFun he x]
    ring
  have hz := weak_gauss ν a d t hν ha ht ht1 hroot heq ψi hψi hci
  rw [he,integral_add hiD hiG] at hz
  exact ⟨hiG,by linarith⟩

private theorem locallyIntegrable_coordinate_mul (f : Space → ℝ) (hf : LocallyIntegrable f) (j : Fin 3) :
    LocallyIntegrable (fun x : Space => x j*f x) := by
  rw [locallyIntegrable_iff]
  intro K hK
  simpa only [mul_comm] using (hf.integrableOn_isCompact hK).mul_continuousOn
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) j).continuous.continuousOn hK

theorem cross_component_locallyIntegrable (ν a d t : ℝ) (hν : 0 ≤ ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (i : Fin 3) :
    LocallyIntegrable (fun x => crossPosition ν a d t x i) := by
  have hi (j k : Fin 3) : LocallyIntegrable (fun x : Space => x j*displacement ν a d t x k) :=
    locallyIntegrable_coordinate_mul _ (component_locallyIntegrable ν a d t hν ha ht ht1 k) j
  simp only [crossPosition_apply]
  exact (hi (WeakCurl.next i) (WeakCurl.previous i)).sub (hi (WeakCurl.previous i) (WeakCurl.next i))

theorem cross_weak_curl (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1)=a) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    (∫ x : Space, crossPosition ν a d t x (WeakCurl.next i)*fderiv ℝ ψ x (basis (WeakCurl.previous i)))-
      (∫ x : Space, crossPosition ν a d t x (WeakCurl.previous i)*fderiv ℝ ψ x (basis (WeakCurl.next i)))=
        -(ν+1)*(∫ x : Space, displacement ν a d t x i*ψ x) := by
  have hD (x v : Space) : fderiv ℝ ψ x v =
      v 0*fderiv ℝ ψ x (basis 0)+v 1*fderiv ℝ ψ x (basis 1)+v 2*fderiv ℝ ψ x (basis 2) := by
    have hv : (∑ j : Fin 3, v j • basis j)=v := by
      simpa only [EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using
        (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    conv_lhs => rw [← hv,map_sum]
    simp only [map_smul,smul_eq_mul,Fin.sum_univ_three]
  have he : (fun x : Space => crossPosition ν a d t x (WeakCurl.next i)*fderiv ℝ ψ x (basis (WeakCurl.previous i))-
      crossPosition ν a d t x (WeakCurl.previous i)*fderiv ℝ ψ x (basis (WeakCurl.next i)))=
      fun x => displacement ν a d t x i*fderiv ℝ ψ x x-x i*fderiv ℝ ψ x (displacement ν a d t x) := by
    funext x
    fin_cases i <;> simp [crossPosition_apply,WeakCurl.next,WeakCurl.previous]
    all_goals rw [hD x x,hD x (displacement ν a d t x)]; ring
  have hiCross (j k : Fin 3) : Integrable (fun x : Space => crossPosition ν a d t x j*fderiv ℝ ψ x (basis k)) := by
    simpa only [smul_eq_mul] using
      (cross_component_locallyIntegrable ν a d t hν.le ha ht ht1 j).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv le_rfl).clm_apply continuous_const) (hc.fderiv_apply ℝ (basis k))
  have hiEuler : Integrable (fun x : Space => displacement ν a d t x i*fderiv ℝ ψ x x) := by
    simpa only [smul_eq_mul] using
      (component_locallyIntegrable ν a d t hν.le ha ht ht1 i).integrable_smul_right_of_hasCompactSupport
        ((hψ.continuous_fderiv le_rfl).clm_apply continuous_id) (HomogeneousEuler.euler_test_compact ψ hc)
  obtain ⟨hiGauss,hGauss⟩ := gauss_coordinate_moment ν a d t hν ha ht ht1 hroot heq i ψ hψ hc
  rw [← integral_sub (hiCross (WeakCurl.next i) (WeakCurl.previous i))
    (hiCross (WeakCurl.previous i) (WeakCurl.next i)),he,integral_sub hiEuler hiGauss,
    component_weak_euler ν a d t hν ha ht ht1 i ψ hψ hc,hGauss]
  ring

theorem potential_weak_curl (ν a d t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hroot : CapAngularShooting.determinant d t a = 0)
    (heq : ν*(ν+1)=a) (i : Fin 3) (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    (∫ x : Space, vectorPotential ν a d t x (WeakCurl.next i)*fderiv ℝ ψ x (basis (WeakCurl.previous i)))-
      (∫ x : Space, vectorPotential ν a d t x (WeakCurl.previous i)*fderiv ℝ ψ x (basis (WeakCurl.next i)))=
        ∫ x : Space, displacement ν a d t x i*ψ x := by
  have hp (j k : Fin 3) : (∫ x : Space, vectorPotential ν a d t x j*fderiv ℝ ψ x (basis k))=
      -(ν+1)⁻¹*(∫ x : Space, crossPosition ν a d t x j*fderiv ℝ ψ x (basis k)) := by
    simp only [vectorPotential,PiLp.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
  rw [hp,hp]
  calc
    _ = -(ν+1)⁻¹*((∫ x : Space, crossPosition ν a d t x (WeakCurl.next i)*fderiv ℝ ψ x (basis (WeakCurl.previous i)))-
      (∫ x : Space, crossPosition ν a d t x (WeakCurl.previous i)*fderiv ℝ ψ x (basis (WeakCurl.next i)))) := by ring
    _ = _ := by
      rw [cross_weak_curl ν a d t hν ha ht ht1 hroot heq i ψ hψ hc]
      field_simp [show ν+1 ≠ 0 by linarith]
      ring

end OQ14.ConicalVectorPotential

#print axioms OQ14.ConicalVectorPotential.crossPosition_apply
#print axioms OQ14.ConicalVectorPotential.coordinate_test_fderiv
#print axioms OQ14.ConicalVectorPotential.gauss_coordinate_moment
#print axioms OQ14.ConicalVectorPotential.cross_component_locallyIntegrable
#print axioms OQ14.ConicalVectorPotential.cross_weak_curl
#print axioms OQ14.ConicalVectorPotential.potential_weak_curl
