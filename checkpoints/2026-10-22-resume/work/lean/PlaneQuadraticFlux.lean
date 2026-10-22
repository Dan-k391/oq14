import MaxwellPlaneL1
import PlaneMaxwellFields

/-! Actual source-source normal flux with a sharp enough gap dependence for shrinking inclusions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PlaneQuadraticFlux
open MeasureTheory Metric Set PlaneSourceKernel MaxwellRadiation MaxwellPlaneTail
open KernelConvolution (response)
open scoped Topology

def magneticCoefficient (k d : ℝ) : ℝ :=
  2*|k| *((4*Real.pi)⁻¹*(|k| *d⁻¹+(d⁻¹)^2))

theorem magnetic_coefficient_nonnegative (k d : ℝ) (hd : 0 < d) : 0 ≤ magneticCoefficient k d := by
  unfold magneticCoefficient
  positivity

theorem magnetic_bound (k R d : ℝ) (hd : 0 < d) (ρ : Source) (hρ : Admissible R d ρ)
    (q : Plane) (i : Fin 3) :
    ‖MagneticResponse.magnetic k ρ (planePoint q) i‖ ≤ magneticCoefficient k d*sourceMass ρ := by
  let C := (4*Real.pi)⁻¹*(|k| *d⁻¹+(d⁻¹)^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg (a j : Fin 3) :
      ‖response (fun z => GreenKernel.phiGradient k z a) (ρ j) (planePoint q)‖ ≤ C*sourceMass ρ := by
    apply (ScalarRadiation.response_norm_bound _ _ (KernelGradient.gradient_measurable k a) (hρ.integrable j) _ C ?_).trans
      (mul_le_mul_of_nonneg_left (component_mass_le ρ j) hC)
    intro y hy
    have hdy : d ≤ ‖planePoint q-y‖ := gap_distance d q y (hρ.gap j y hy)
    have hinv : ‖planePoint q-y‖⁻¹ ≤ d⁻¹ := inv_anti₀ hd hdy
    apply (KernelGradient.gradient_bound k (planePoint q-y) a).trans
    exact mul_le_mul_of_nonneg_left (add_le_add
      (mul_le_mul_of_nonneg_left hinv (abs_nonneg k))
      (pow_le_pow_left₀ (by positivity) hinv 2)) (by positivity)
  simp only [MagneticResponse.magnetic,norm_mul,norm_neg,Complex.norm_I,one_mul,
    Complex.norm_real,Real.norm_eq_abs]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (abs_nonneg k)).trans
  exact (mul_le_mul_of_nonneg_left (add_le_add (hg (WeakCurl.next i) (WeakCurl.previous i))
    (hg (WeakCurl.previous i) (WeakCurl.next i))) (abs_nonneg k)).trans_eq
      (by unfold magneticCoefficient; dsimp [C]; ring)

def diskConstant (k R T d : ℝ) : ℝ :=
  2*magneticCoefficient k d*(PlaneMaxwellLocal.electricCoefficient k R T*
    ((Real.pi+PlaneInverseCube.diskConstant)/d))

def wholeConstant (k R T d : ℝ) : ℝ :=
  diskConstant k R T d+MaxwellPlaneTail.tailConstant k R*PlaneInverseCube.diskConstant/T

theorem local_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    (∫ q : Plane in closedBall 0 T, ‖MaxwellPlaneL1.flux k ρ σ q‖) ≤
      diskConstant k R T d*sourceMass ρ*sourceMass σ := by
  obtain ⟨_,_,hw⟩ := MaxwellPlaneL1.whole_plane_bound k R d hR hd
  have hi : IntegrableOn (MaxwellPlaneL1.flux k ρ σ) (closedBall 0 T) := (hw ρ σ hρ hσ).1.integrableOn
  have he (i : Fin 3) := PlaneMaxwellFields.electric_mass k R T d hd ρ hρ i
  let E := fun q i => ExteriorContinuity.electric k ρ (planePoint q) i
  let B := magneticCoefficient k d*sourceMass σ
  have hB : 0 ≤ B := mul_nonneg (magnetic_coefficient_nonnegative k d hd) (sourceMass_nonnegative σ)
  have hb (q : Plane) : ‖MaxwellPlaneL1.flux k ρ σ q‖ ≤ B*(‖E q 0‖+‖E q 1‖) := by
    change ‖E q 0*star (MagneticResponse.magnetic k σ (planePoint q) 1)-
      E q 1*star (MagneticResponse.magnetic k σ (planePoint q) 0)‖ ≤ _
    apply (norm_sub_le _ _).trans
    simp only [norm_mul,norm_star]
    exact (add_le_add (mul_le_mul_of_nonneg_left (magnetic_bound k R d hd σ hσ q 1) (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (magnetic_bound k R d hd σ hσ q 0) (norm_nonneg _))).trans_eq (by ring)
  calc
    _ ≤ ∫ q : Plane in closedBall 0 T, B*(‖E q 0‖+‖E q 1‖) :=
      integral_mono_ae hi.norm (((he 0).1.norm.add (he 1).1.norm).const_mul B) (Filter.Eventually.of_forall hb)
    _ = B*((∫ q : Plane in closedBall 0 T, ‖E q 0‖)+(∫ q : Plane in closedBall 0 T, ‖E q 1‖)) := by
      rw [integral_const_mul,integral_add (he 0).1.norm (he 1).1.norm]
    _ ≤ B*((PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+PlaneInverseCube.diskConstant)/d))*sourceMass ρ+
      (PlaneMaxwellLocal.electricCoefficient k R T*((Real.pi+PlaneInverseCube.diskConstant)/d))*sourceMass ρ) :=
      mul_le_mul_of_nonneg_left (add_le_add (he 0).2 (he 1).2) hB
    _ = _ := by unfold diskConstant; dsimp [B]; ring

theorem whole_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hT : 2 ≤ T) (hTR : 2*R ≤ T)
    (ρ σ : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ) :
    Integrable (MaxwellPlaneL1.flux k ρ σ) ∧
    (∫ q : Plane, ‖MaxwellPlaneL1.flux k ρ σ q‖) ≤ wholeConstant k R T d*sourceMass ρ*sourceMass σ := by
  obtain ⟨_,_,hw⟩ := MaxwellPlaneL1.whole_plane_bound k R d hR hd
  have hi := (hw ρ σ hρ hσ).1
  refine ⟨hi,?_⟩
  have hb (q : Plane) (hq : T < ‖q‖) : ‖MaxwellPlaneL1.flux k ρ σ q‖ ≤
      (MaxwellPlaneTail.tailConstant k R*sourceMass ρ*sourceMass σ)/‖q‖^3 := by
    have hh := bilinear_flux_tail k R hR ρ σ hρ.integrable hσ.integrable hρ.support hσ.support
      (planePoint q) (by rw [planePoint_norm]; linarith) (by rw [planePoint_norm]; linarith) (by rfl)
    simpa only [MaxwellPlaneL1.flux,planePoint_norm,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm] using hh
  have ht := PlaneInverseCube.tail_integral_bound T _ (by linarith : 0 < T)
    hi.aestronglyMeasurable.restrict hb
  have heq : {q : Plane | T < ‖q‖}=(closedBall (0 : Plane) T)ᶜ := by ext q; simp
  rw [heq] at ht
  calc
    _ = (∫ q : Plane in closedBall 0 T, ‖MaxwellPlaneL1.flux k ρ σ q‖)+
      (∫ q : Plane in (closedBall (0 : Plane) T)ᶜ, ‖MaxwellPlaneL1.flux k ρ σ q‖) :=
      (integral_add_compl measurableSet_closedBall hi.norm).symm
    _ ≤ diskConstant k R T d*sourceMass ρ*sourceMass σ+
      (MaxwellPlaneTail.tailConstant k R*sourceMass ρ*sourceMass σ)*PlaneInverseCube.diskConstant/T :=
      add_le_add (local_mass k R T d hR hd ρ σ hρ hσ) ht
    _ = _ := by unfold wholeConstant; ring

theorem whole_constant_nonnegative (k R T d : ℝ) (hR : 0 ≤ R) (hT : 0 < T) (hd : 0 < d) :
    0 ≤ wholeConstant k R T d := by
  have hM := magnetic_coefficient_nonnegative k d hd
  unfold wholeConstant diskConstant PlaneMaxwellLocal.electricCoefficient
    PlaneMaxwellLocal.remainderCoefficient MaxwellPlaneTail.tailConstant
    MaxwellPlaneTail.leadingConstant MaxwellPlaneTail.electricErrorConstant
    MaxwellPlaneTail.magneticErrorConstant PlaneInverseCube.diskConstant
  positivity

theorem difference_mass (k R T d : ℝ) (hR : 0 ≤ R) (hd : 0 < d) (hT : 2 ≤ T) (hTR : 2*R ≤ T)
    (ρ σ ρ' σ' : Source) (hρ : Admissible R d ρ) (hσ : Admissible R d σ)
    (hρ' : Admissible R d ρ') (hσ' : Admissible R d σ') :
    (∫ q : Plane, ‖MaxwellPlaneL1.flux k ρ σ q-MaxwellPlaneL1.flux k ρ' σ' q‖) ≤
      wholeConstant k R T d*(sourceMass (ρ-ρ')*sourceMass σ+sourceMass ρ'*sourceMass (σ-σ')) := by
  have hi := (whole_mass k R T d hR hd hT hTR ρ σ hρ hσ).1.sub
    (whole_mass k R T d hR hd hT hTR ρ' σ' hρ' hσ').1
  have h₁ := whole_mass k R T d hR hd hT hTR (ρ-ρ') σ (admissible_sub R d ρ ρ' hρ hρ') hσ
  have h₂ := whole_mass k R T d hR hd hT hTR ρ' (σ-σ') hρ' (admissible_sub R d σ σ' hσ hσ')
  have hm : (∫ q : Plane, ‖MaxwellPlaneL1.flux k ρ σ q-MaxwellPlaneL1.flux k ρ' σ' q‖) ≤
      (∫ q : Plane, ‖MaxwellPlaneL1.flux k (ρ-ρ') σ q‖)+(∫ q : Plane, ‖MaxwellPlaneL1.flux k ρ' (σ-σ') q‖) := by
    rw [← integral_add h₁.1.norm h₂.1.norm]
    apply integral_mono_ae hi.norm (h₁.1.norm.add h₂.1.norm)
    filter_upwards with q
    change ‖bilinearFlux k ρ σ (planePoint q)-bilinearFlux k ρ' σ' (planePoint q)‖ ≤ _
    rw [bilinear_plane_sub k R d hd ρ σ ρ' σ' hρ hσ hρ' hσ' q]
    exact norm_add_le _ _
  exact (hm.trans (add_le_add h₁.2 h₂.2)).trans_eq (by ring)

end OQ14.PlaneQuadraticFlux
#print axioms OQ14.PlaneQuadraticFlux.magnetic_coefficient_nonnegative
#print axioms OQ14.PlaneQuadraticFlux.magnetic_bound
#print axioms OQ14.PlaneQuadraticFlux.local_mass
#print axioms OQ14.PlaneQuadraticFlux.whole_mass
#print axioms OQ14.PlaneQuadraticFlux.whole_constant_nonnegative
#print axioms OQ14.PlaneQuadraticFlux.difference_mass
