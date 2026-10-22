import SphereHarmonicBasis
import HarmonicRotation

/-! Actual evaluation kernels of the constructed sphere harmonic L2 spaces. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000

namespace OQ14.SphereHarmonicAddition

open MeasureTheory OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
open scoped RealInnerProductSpace

def lift (l : ℕ) : harmonicSpace l →ₗ[ℝ] C(Sphere, ℝ) where
  toFun v := ∑ i : Index l, (SphereHarmonicBasis.basis l).repr v i • angular l i
  map_add' v w := by
    simp only [map_add,PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [map_smul,PiLp.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

theorem lift_toLp (l : ℕ) (v : harmonicSpace l) :
    ContinuousMap.toLp 2 angularMeasure ℝ (lift l v)=(v : Ambient) := by
  change ContinuousMap.toLp 2 angularMeasure ℝ (∑ i : Index l, (SphereHarmonicBasis.basis l).repr v i • angular l i)=_
  simp only [map_sum,map_smul,angular_toLp]
  have h := congrArg (harmonicSpace l).subtype ((SphereHarmonicBasis.basis l).sum_repr v)
  simpa only [map_sum,map_smul,Submodule.subtype_apply] using h

theorem lift_polynomial (l : ℕ) (p : harmonicPolynomials l) :
    lift l (polynomialVector l p)=SpherePolynomial.polynomialMap p :=
  (restriction_expansion l p).symm

def precompose (L : Space ≃ₗᵢ[ℝ] Space) : C(Sphere, ℝ) →ₐ[ℝ] C(Sphere, ℝ) :=
  ContinuousMap.compRightAlgHom ℝ ℝ
    ⟨SphereAngularSymmetry.sphereMap L,(SphereAngularSymmetry.sphereMap L).continuous⟩

def rotationRaw (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) : harmonicSpace l →ₗ[ℝ] Ambient :=
  (ContinuousMap.toLp 2 angularMeasure ℝ).toLinearMap.comp
    ((precompose L).toLinearMap.comp (lift l))

theorem rotationRaw_mem (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) (v : harmonicSpace l) :
    rotationRaw l L v ∈ harmonicSpace l := by
  obtain ⟨p,hp⟩ := v.property
  have hv : lift l v=SpherePolynomial.polynomialMap p := by
    apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) angularMeasure
    rw [lift_toLp]
    exact hp.symm
  refine ⟨⟨HarmonicRotation.rotate L p,
    HarmonicRotation.rotate_homogeneous L p l p.property.1,
    HarmonicRotation.rotate_harmonic L p p.property.2⟩,?_⟩
  change ContinuousMap.toLp 2 angularMeasure ℝ
    (SpherePolynomial.polynomialMap (HarmonicRotation.rotate L p))=
      ContinuousMap.toLp 2 angularMeasure ℝ (precompose L (lift l v))
  rw [HarmonicRotation.rotate_restriction,hv]
  rfl

def rotationLinear (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) : harmonicSpace l →ₗ[ℝ] harmonicSpace l :=
  LinearMap.codRestrict (harmonicSpace l) (rotationRaw l L) (rotationRaw_mem l L)

theorem rotationLinear_norm (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) (v : harmonicSpace l) :
    ‖rotationLinear l L v‖=‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq,← real_inner_self_eq_norm_sq]
  change ⟪rotationRaw l L v,rotationRaw l L v⟫=⟪(v : Ambient),(v : Ambient)⟫
  rw [← lift_toLp l v]
  change ⟪ContinuousMap.toLp 2 angularMeasure ℝ (precompose L (lift l v)),
    ContinuousMap.toLp 2 angularMeasure ℝ (precompose L (lift l v))⟫=
      ⟪ContinuousMap.toLp 2 angularMeasure ℝ (lift l v),ContinuousMap.toLp 2 angularMeasure ℝ (lift l v)⟫
  rw [ContinuousMap.inner_toLp,ContinuousMap.inner_toLp]
  simpa only [conj_trivial] using SphereAngularSymmetry.integral_sphereMap L
    (fun n => lift l v n*lift l v n)

def rotationIsometry (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) : harmonicSpace l →ₗᵢ[ℝ] harmonicSpace l where
  toLinearMap := rotationLinear l L
  norm_map' := rotationLinear_norm l L

def rotation (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) : harmonicSpace l ≃ₗᵢ[ℝ] harmonicSpace l :=
  LinearIsometryEquiv.ofSurjective (rotationIsometry l L)
    ((LinearMap.injective_iff_surjective).mp (rotationIsometry l L).injective)

theorem lift_rotation (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) (v : harmonicSpace l) :
    lift l (rotation l L v)=precompose L (lift l v) := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) angularMeasure
  rw [lift_toLp]
  rfl

theorem lift_basis (l : ℕ) (i : Index l) :
    lift l (SphereHarmonicBasis.basis l i)=angular l i := by
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℝ) angularMeasure
  rw [lift_toLp,angular_toLp]

def kernelVector (l : ℕ) (n : Sphere) : harmonicSpace l :=
  ∑ i : Index l, angular l i n • SphereHarmonicBasis.basis l i

def diagonal (l : ℕ) (n : Sphere) : ℝ := ∑ i : Index l, angular l i n^2

theorem kernelVector_inner (l : ℕ) (n : Sphere) (v : harmonicSpace l) :
    ⟪kernelVector l n,v⟫=lift l v n := by
  simp only [kernelVector,sum_inner,inner_smul_left,conj_trivial]
  change _=(∑ i : Index l, (SphereHarmonicBasis.basis l).repr v i • angular l i) n
  simp only [ContinuousMap.sum_apply,ContinuousMap.smul_apply,smul_eq_mul,
    OrthonormalBasis.repr_apply_apply,mul_comm]

theorem kernelVector_norm_sq (l : ℕ) (n : Sphere) : ‖kernelVector l n‖^2=diagonal l n := by
  have hb (i : Index l) : ⟪kernelVector l n,SphereHarmonicBasis.basis l i⟫=angular l i n := by
    rw [kernelVector_inner,lift_basis]
  have hb' (i : Index l) : ⟪SphereHarmonicBasis.basis l i,kernelVector l n⟫=angular l i n :=
    (real_inner_comm _ _).trans (hb i)
  have h := (SphereHarmonicBasis.basis l).sum_inner_mul_inner (kernelVector l n) (kernelVector l n)
  simpa only [hb,hb',← sq,real_inner_self_eq_norm_sq,diagonal] using h.symm

theorem diagonal_rotate (l : ℕ) (L : Space ≃ₗᵢ[ℝ] Space) (n : Sphere) :
    diagonal l (SphereAngularSymmetry.sphereMap L n)=diagonal l n := by
  have hK : rotation l L (kernelVector l (SphereAngularSymmetry.sphereMap L n))=kernelVector l n := by
    apply ext_inner_right ℝ
    intro v
    obtain ⟨w,rfl⟩ := (rotation l L).surjective v
    rw [(rotation l L).inner_map_map,kernelVector_inner,kernelVector_inner,lift_rotation]
    rfl
  calc
    _ = ‖kernelVector l (SphereAngularSymmetry.sphereMap L n)‖^2 := (kernelVector_norm_sq _ _).symm
    _ = ‖rotation l L (kernelVector l (SphereAngularSymmetry.sphereMap L n))‖^2 := by rw [(rotation l L).norm_map]
    _ = ‖kernelVector l n‖^2 := congrArg (fun v : harmonicSpace l => ‖v‖^2) hK
    _ = diagonal l n := kernelVector_norm_sq _ _

theorem diagonal_constant (l : ℕ) (n m : Sphere) : diagonal l n=diagonal l m := by
  let L : Space ≃ₗᵢ[ℝ] Space := (ℝ ∙ ((n : Space)-(m : Space)))ᗮ.reflection
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have hm : ‖(m : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using m.property
  have hL : SphereAngularSymmetry.sphereMap L n=m := by
    apply Subtype.ext
    exact Submodule.reflection_sub (hn.trans hm.symm)
  have h := diagonal_rotate l L n
  rw [hL] at h
  exact h.symm

theorem diagonal_integral (l : ℕ) :
    (∫ n : Sphere, diagonal l n ∂angularMeasure)=(Module.finrank ℝ (harmonicSpace l) : ℝ) := by
  unfold diagonal
  rw [integral_finset_sum _ (fun i _ => Continuous.integrable_of_hasCompactSupport
    ((angular l i).continuous.pow 2) (HasCompactSupport.of_compactSpace _))]
  simp only [angular_integral_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem diagonal_mul_area (l : ℕ) (n : Sphere) :
    diagonal l n*angularMeasure.real Set.univ=(Module.finrank ℝ (harmonicSpace l) : ℝ) := by
  rw [← diagonal_integral]
  calc
    _ = ∫ _m : Sphere, diagonal l n ∂angularMeasure := by simp [integral_const,smul_eq_mul,mul_comm]
    _ = ∫ m : Sphere, diagonal l m ∂angularMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (diagonal_constant l n)

theorem area_pos : 0 < angularMeasure.real Set.univ := by
  let n : Sphere := ⟨Maxwell.basis 0,by simp [Maxwell.basis,Metric.mem_sphere]⟩
  have hp : 0 < angularMeasure Set.univ :=
    isOpen_univ.measure_pos angularMeasure ⟨n,Set.mem_univ _⟩
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

theorem diagonal_formula (l : ℕ) (n : Sphere) :
    diagonal l n=(Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ :=
  (eq_div_iff (ne_of_gt area_pos)).mpr (diagonal_mul_area l n)

theorem angular_sq_bound (l : ℕ) (i : Index l) (n : Sphere) :
    angular l i n^2 ≤ (Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ := by
  rw [← diagonal_formula l n]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (angular l j n)) (Finset.mem_univ i)

theorem angular_norm_bound (l : ℕ) (i : Index l) (n : Sphere) :
    ‖angular l i n‖ ≤ Real.sqrt ((Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ) := by
  have h : ‖angular l i n‖^2 ≤ (Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ := by
    simpa only [Real.norm_eq_abs,sq_abs] using angular_sq_bound l i n
  calc
    _ = Real.sqrt (‖angular l i n‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h

def kernel (l : ℕ) (n m : Sphere) : ℝ := ∑ i : Index l, angular l i n*angular l i m

theorem kernel_inner (l : ℕ) (n m : Sphere) :
    ⟪kernelVector l n,kernelVector l m⟫=kernel l n m := by
  rw [kernelVector_inner]
  simp only [kernelVector,map_sum,map_smul,lift_basis,ContinuousMap.sum_apply,
    ContinuousMap.smul_apply,smul_eq_mul,kernel,mul_comm]

theorem kernelVector_norm (l : ℕ) (n : Sphere) :
    ‖kernelVector l n‖=Real.sqrt ((Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ) := by
  rw [← diagonal_formula l n,← kernelVector_norm_sq]
  exact (Real.sqrt_sq (norm_nonneg _)).symm

theorem kernel_bound (l : ℕ) (n m : Sphere) :
    ‖kernel l n m‖ ≤ (Module.finrank ℝ (harmonicSpace l) : ℝ)/angularMeasure.real Set.univ := by
  rw [← kernel_inner]
  calc
    _ ≤ ‖kernelVector l n‖*‖kernelVector l m‖ := norm_inner_le_norm _ _
    _ = _ := by
      rw [kernelVector_norm,kernelVector_norm,← sq,Real.sq_sqrt]
      exact div_nonneg (Nat.cast_nonneg _) area_pos.le

end OQ14.SphereHarmonicAddition

#print axioms OQ14.SphereHarmonicAddition.lift_toLp
#print axioms OQ14.SphereHarmonicAddition.lift_polynomial
#print axioms OQ14.SphereHarmonicAddition.rotationRaw_mem
#print axioms OQ14.SphereHarmonicAddition.rotationLinear_norm
#print axioms OQ14.SphereHarmonicAddition.lift_rotation
#print axioms OQ14.SphereHarmonicAddition.lift_basis
#print axioms OQ14.SphereHarmonicAddition.kernelVector_inner
#print axioms OQ14.SphereHarmonicAddition.kernelVector_norm_sq
#print axioms OQ14.SphereHarmonicAddition.diagonal_rotate
#print axioms OQ14.SphereHarmonicAddition.diagonal_constant
#print axioms OQ14.SphereHarmonicAddition.diagonal_integral
#print axioms OQ14.SphereHarmonicAddition.diagonal_mul_area
#print axioms OQ14.SphereHarmonicAddition.area_pos
#print axioms OQ14.SphereHarmonicAddition.diagonal_formula
#print axioms OQ14.SphereHarmonicAddition.angular_sq_bound
#print axioms OQ14.SphereHarmonicAddition.angular_norm_bound
#print axioms OQ14.SphereHarmonicAddition.kernel_inner
#print axioms OQ14.SphereHarmonicAddition.kernelVector_norm
#print axioms OQ14.SphereHarmonicAddition.kernel_bound
