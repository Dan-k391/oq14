import ComplexTransverseExpansion
import SphereDyadicTransform

/-! Actual projected plane fields in complex Euclidean sphere vector L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.TransversePlaneFields
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace

def normal (n : Sphere) : ComplexVectorSphere.Vector := embedVector (n : Space)
def unit (i : Fin 3) : ComplexVectorSphere.Vector := EuclideanSpace.single i 1
def projected (i : Fin 3) (n : Sphere) : ComplexVectorSphere.Vector :=
  unit i-(n.val i : ℂ) • normal n

theorem normal_inner (n : Sphere) : ⟪normal n,normal n⟫=1 := by
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  calc
    _ = ((@inner ℝ Space _ (n : Space) (n : Space) : ℝ) : ℂ) := by
      simp only [normal,PiLp.inner_apply,embed_apply,RCLike.inner_apply,Complex.conj_ofReal,
        Complex.ofReal_mul,Complex.ofReal_sum,conj_trivial]
    _ = 1 := by rw [real_inner_self_eq_norm_sq,hn];norm_num

theorem normal_unit (n : Sphere) (i : Fin 3) : ⟪normal n,unit i⟫=(n.val i : ℂ) := by
  change ⟪normal n,EuclideanSpace.single i 1⟫=(n.val i : ℂ)
  rw [EuclideanSpace.inner_single_right]
  simp [normal,embed_apply]

theorem projected_tangent (i : Fin 3) (n : Sphere) : ⟪normal n,projected i n⟫=0 := by
  rw [projected,inner_sub_right,inner_smul_right,normal_inner,normal_unit]
  ring

theorem projected_inner (i j : Fin 3) (n : Sphere) :
    ⟪projected i n,projected j n⟫=SphereReactionKernel.amplitude n i j := by
  have hu : ⟪unit i,unit j⟫=(if i=j then 1 else 0 : ℂ) := by
    simp [unit,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply]
  have hi : ⟪unit i,normal n⟫=(n.val i : ℂ) := by
    rw [← inner_conj_symm,normal_unit,Complex.conj_ofReal]
  simp only [projected,inner_sub_left,inner_sub_right,inner_smul_left,inner_smul_right,
    normal_inner,normal_unit,hi,hu,Complex.conj_ofReal,SphereReactionKernel.amplitude]
  ring

def plane (k : ℝ) (x : Space) (i : Fin 3) : C(Sphere,ComplexVectorSphere.Vector) where
  toFun n := SphereReactionKernel.wave (-k) x n • projected i n
  continuous_toFun := by
    have hc : Continuous (fun n : Sphere => normal n) := embedVector.continuous.comp continuous_subtype_val
    have hphase : Continuous (fun n : Sphere => SphereReactionKernel.wave (-k) x n) := by
      unfold SphereReactionKernel.wave
      fun_prop
    exact hphase.smul (continuous_const.sub ((Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp continuous_subtype_val)).smul hc))

def field (k : ℝ) (x : Space) (i : Fin 3) : ComplexVectorSphere.Ambient :=
  ContinuousMap.toLp 2 angularMeasure ℂ (plane k x i)

theorem field_tangent (k : ℝ) (x : Space) (i : Fin 3) : IsTangential (field k x i) := by
  filter_upwards [(plane k x i).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hn
  change field k x i n=plane k x i n at hn
  rw [hn]
  change ⟪normal n,SphereReactionKernel.wave (-k) x n • projected i n⟫=0
  rw [inner_smul_right,projected_tangent,mul_zero]

theorem wave_product (k : ℝ) (x y : Space) (n : Sphere) :
    star (SphereReactionKernel.wave (-k) x n)*SphereReactionKernel.wave (-k) y n=
      SphereReactionKernel.wave k (x-y) n := by
  unfold SphereReactionKernel.wave
  change (starRingEnd ℂ) (Complex.exp _)*Complex.exp _=Complex.exp _
  rw [← Complex.exp_conj,← Complex.exp_add]
  congr 1
  simp only [map_mul,map_neg,Complex.conj_ofReal,Complex.conj_I,inner_sub_right,
    Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_sub]
  ring

theorem field_inner (k : ℝ) (x y : Space) (i j : Fin 3) :
    ⟪field k x i,field k y j⟫=
      ∫ n : Sphere,SphereReactionKernel.amplitude n i j*SphereReactionKernel.wave k (x-y) n
        ∂angularMeasure := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(plane k x i).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    (plane k y j).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hx hy
  change field k x i n=plane k x i n at hx
  change field k y j n=plane k y j n at hy
  rw [hx,hy]
  change ⟪SphereReactionKernel.wave (-k) x n • projected i n,
    SphereReactionKernel.wave (-k) y n • projected j n⟫=_
  rw [inner_smul_left,inner_smul_right,projected_inner]
  change (starRingEnd ℂ) (SphereReactionKernel.wave (-k) x n)*
    (SphereReactionKernel.wave (-k) y n*SphereReactionKernel.amplitude n i j)=_
  rw [← mul_assoc]
  change (star (SphereReactionKernel.wave (-k) x n)*SphereReactionKernel.wave (-k) y n)*
    SphereReactionKernel.amplitude n i j=_
  rw [wave_product]
  ring

theorem J_series (k : ℝ) (x y : Space) (i j : Fin 3) :
    HasSum (fun a : ComplexTransverseExpansion.ModeIndex =>
      (((k^3/(16*Real.pi^2) : ℝ) : ℂ)*
        (⟪field k x i,ComplexTransverseExpansion.vector a⟫*
          ⟪ComplexTransverseExpansion.vector a,field k y j⟫)))
      (SphereReactionKernel.J k (x-y) i j) := by
  have h := (ComplexTransverseExpansion.inner_series (field k x i) (field k y j)
    (field_tangent k y j)).mul_left (((k^3/(16*Real.pi^2) : ℝ) : ℂ))
  simpa only [field_inner,SphereReactionKernel.J,SphereReactionKernel.surface] using h

end OQ14.TransversePlaneFields

#print axioms OQ14.TransversePlaneFields.normal_inner
#print axioms OQ14.TransversePlaneFields.normal_unit
#print axioms OQ14.TransversePlaneFields.projected_tangent
#print axioms OQ14.TransversePlaneFields.projected_inner
#print axioms OQ14.TransversePlaneFields.field_tangent
#print axioms OQ14.TransversePlaneFields.wave_product
#print axioms OQ14.TransversePlaneFields.field_inner
#print axioms OQ14.TransversePlaneFields.J_series
