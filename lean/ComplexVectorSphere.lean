import TransverseHarmonicBasis

/-! Actual real and imaginary parts in complex Euclidean sphere vector L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ComplexVectorSphere
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis
open scoped ComplexInnerProductSpace

abbrev Vector := EuclideanSpace ℂ (Fin 3)
abbrev Ambient := Lp Vector 2 angularMeasure
abbrev RealAmbient := VectorHarmonicSeparation.Ambient

def embedVector : Space →L[ℝ] Vector :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)))

def reVector : Vector →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Complex.reCLM.comp
      ((EuclideanSpace.proj i : Vector →L[ℂ] ℂ).restrictScalars ℝ)))

def imVector : Vector →L[ℝ] Space :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => Complex.imCLM.comp
      ((EuclideanSpace.proj i : Vector →L[ℂ] ℂ).restrictScalars ℝ)))

theorem embed_apply (v : Space) (i : Fin 3) : embedVector v i=(v i : ℂ) := rfl
theorem re_apply (v : Vector) (i : Fin 3) : reVector v i=(v i).re := rfl
theorem im_apply (v : Vector) (i : Fin 3) : imVector v i=(v i).im := rfl

def realLift : RealAmbient →L[ℝ] Ambient := embedVector.compLpL 2 angularMeasure
def realPart : Ambient →L[ℝ] RealAmbient := reVector.compLpL 2 angularMeasure
def imagPart : Ambient →L[ℝ] RealAmbient := imVector.compLpL 2 angularMeasure

theorem realLift_inner (u v : RealAmbient) :
    ⟪realLift u,realLift v⟫=((@inner ℝ RealAmbient _ u v : ℝ) : ℂ) := by
  rw [L2.inner_def,L2.inner_def,← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [embedVector.coeFn_compLpL u,embedVector.coeFn_compLpL v] with n hu hv
  simp only [realLift,hu,hv,PiLp.inner_apply,embed_apply,RCLike.inner_apply,
    Complex.conj_ofReal,Complex.ofReal_sum,Complex.ofReal_mul,conj_trivial]

theorem real_imag_decomposition (u : Ambient) :
    u=realLift (realPart u)+Complex.I • realLift (imagPart u) := by
  apply Lp.ext
  filter_upwards [reVector.coeFn_compLpL u,imVector.coeFn_compLpL u,
    embedVector.coeFn_compLpL (realPart u),embedVector.coeFn_compLpL (imagPart u),
    Lp.coeFn_add (realLift (realPart u)) (Complex.I • realLift (imagPart u)),
    Lp.coeFn_smul Complex.I (realLift (imagPart u))] with n hr hi hrr hii ha hs
  simp only [realLift,realPart,imagPart] at *
  rw [ha]
  simp only [Pi.add_apply]
  rw [hs]
  simp only [Pi.smul_apply]
  rw [hrr,hii,hr,hi]
  apply PiLp.ext
  intro i
  simpa only [PiLp.add_apply,PiLp.smul_apply,embed_apply,re_apply,im_apply,smul_eq_mul,mul_comm]
    using (Complex.re_add_im (u n i)).symm

theorem inner_re (x : Space) (v : Vector) :
    (⟪embedVector x,v⟫ : ℂ).re=@inner ℝ Space _ x (reVector v) := by
  simp [PiLp.inner_apply,RCLike.inner_apply,embed_apply,re_apply,Complex.mul_re]

theorem inner_im (x : Space) (v : Vector) :
    (⟪embedVector x,v⟫ : ℂ).im=@inner ℝ Space _ x (imVector v) := by
  simp [PiLp.inner_apply,RCLike.inner_apply,embed_apply,im_apply,Complex.mul_im]

def IsTangential (F : Ambient) : Prop :=
  ∀ᵐ (n : Sphere) ∂angularMeasure,⟪embedVector (n : Space),F n⟫=0

theorem realPart_tangent (F : Ambient) (hF : IsTangential F) :
    VectorHarmonicSeparation.IsTangential (realPart F) := by
  filter_upwards [hF,reVector.coeFn_compLpL F] with n hn he
  change realPart F n=reVector (F n) at he
  rw [he,← inner_re,hn]
  rfl

theorem imagPart_tangent (F : Ambient) (hF : IsTangential F) :
    VectorHarmonicSeparation.IsTangential (imagPart F) := by
  filter_upwards [hF,imVector.coeFn_compLpL F] with n hn he
  change imagPart F n=imVector (F n) at he
  rw [he,← inner_im,hn]
  rfl

end OQ14.ComplexVectorSphere

#print axioms OQ14.ComplexVectorSphere.embed_apply
#print axioms OQ14.ComplexVectorSphere.re_apply
#print axioms OQ14.ComplexVectorSphere.im_apply
#print axioms OQ14.ComplexVectorSphere.realLift_inner
#print axioms OQ14.ComplexVectorSphere.real_imag_decomposition
#print axioms OQ14.ComplexVectorSphere.inner_re
#print axioms OQ14.ComplexVectorSphere.inner_im
#print axioms OQ14.ComplexVectorSphere.realPart_tangent
#print axioms OQ14.ComplexVectorSphere.imagPart_tangent
