import AngularHerglotz
import PlaneDebyeCoefficients

/-! Actual L2 angular amplitudes give bounded entire-space electric evaluation functionals. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.HerglotzAngularL2
open MeasureTheory Set OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere
open scoped ComplexInnerProductSpace Topology
abbrev Sphere := AngularPower.Sphere
abbrev Space := Maxwell.Space
abbrev Ambient := ComplexVectorSphere.Ambient

def value (k : ℝ) (x : Space) (i : Fin 3) : Ambient →L[ℂ] ℂ :=
  innerSL ℂ (TransversePlaneFields.field (-k) x i)

theorem plane_norm (k : ℝ) (x : Space) (i : Fin 3) :
    ‖TransversePlaneFields.field k x i‖=‖TransversePlaneFields.field 0 0 i‖ := by
  have h : @inner ℂ Ambient _ (TransversePlaneFields.field k x i) (TransversePlaneFields.field k x i)=
      @inner ℂ Ambient _ (TransversePlaneFields.field 0 0 i) (TransversePlaneFields.field 0 0 i) := by
    rw [TransversePlaneFields.field_inner,TransversePlaneFields.field_inner]
    apply integral_congr_ae
    filter_upwards with n
    simp only [sub_self,SphereReactionKernel.wave,inner_zero_right,mul_zero,Complex.ofReal_zero,zero_mul,
      Complex.exp_zero,mul_one]
  have he : ‖TransversePlaneFields.field k x i‖^2=‖TransversePlaneFields.field 0 0 i‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ Ambient,@norm_sq_eq_re_inner ℂ Ambient,h]
  nlinarith [norm_nonneg (TransversePlaneFields.field k x i),norm_nonneg (TransversePlaneFields.field 0 0 i)]

def bound : ℝ := ∑ i : Fin 3, ‖TransversePlaneFields.field 0 0 i‖

theorem bound_nonnegative : 0 ≤ bound := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem value_norm_le (k : ℝ) (x : Space) (i : Fin 3) (F : Ambient) :
    ‖value k x i F‖ ≤ bound*‖F‖ := by
  change ‖@inner ℂ Ambient _ (TransversePlaneFields.field (-k) x i) F‖ ≤ _
  apply (norm_inner_le_norm _ _).trans
  rw [plane_norm]
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => norm_nonneg (TransversePlaneFields.field 0 0 j))
    (Finset.mem_univ i)) (norm_nonneg _)

theorem value_difference_bound (k : ℝ) (x : Space) (i : Fin 3) (F G : Ambient) :
    ‖value k x i F-value k x i G‖ ≤ bound*‖F-G‖ := by
  rw [← map_sub]
  exact value_norm_le k x i _


theorem inner_projected (v : ComplexVectorSphere.Vector) (n : Sphere) (i : Fin 3)
    (hv : @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) v=0) :
    @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.projected i n) v=v i := by
  rw [TransversePlaneFields.projected,inner_sub_left,inner_smul_left,hv,mul_zero,sub_zero]
  simp [TransversePlaneFields.unit,EuclideanSpace.inner_single_left]

theorem conjugate_wave (k : ℝ) (x : Space) (n : Sphere) :
    star (SphereReactionKernel.wave k x n)=SphereReactionKernel.wave (-k) x n := by
  unfold SphereReactionKernel.wave
  change (starRingEnd ℂ) (Complex.exp _) = _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_neg,Complex.ofReal_mul]
  ring

theorem value_toLp (k : ℝ) (A : C(Sphere,ComplexVectorSphere.Vector))
    (ht : ∀ n, @inner ℂ ComplexVectorSphere.Vector _ (TransversePlaneFields.normal n) (A n)=0)
    (x : Space) (i : Fin 3) :
    value k x i (ContinuousMap.toLp 2 angularMeasure ℂ A)=
      AngularHerglotz.electric k (fun n j => A n j) x i := by
  change @inner ℂ Ambient _ (TransversePlaneFields.field (-k) x i) (ContinuousMap.toLp 2 angularMeasure ℂ A)=_
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(TransversePlaneFields.plane (-k) x i).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    A.coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hp hA
  change TransversePlaneFields.field (-k) x i n=TransversePlaneFields.plane (-k) x i n at hp
  rw [hp,hA]
  change @inner ℂ ComplexVectorSphere.Vector _
    (SphereReactionKernel.wave (-(-k)) x n • TransversePlaneFields.projected i n) (A n)=_
  rw [inner_smul_left,inner_projected (A n) n i (ht n),neg_neg]
  change star (SphereReactionKernel.wave k x n)*A n i=A n i*SphereReactionKernel.wave (-k) x n
  rw [conjugate_wave]
  ring

def finiteAmplitude (c : ComplexTransverseExpansion.ModeIndex →₀ ℂ) : Ambient :=
  c.sum (fun m z => z • ComplexTransverseExpansion.vector m)

theorem finite_approximation (F : Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ComplexTransverseExpansion.ModeIndex →₀ ℂ, ‖finiteAmplitude c-F‖ < ε := by
  have h := ComplexTransverseExpansion.expansion F hF
  obtain ⟨s,hs⟩ := (Metric.tendsto_nhds.mp h ε hε).exists
  have hm : (∑ m ∈ s, @inner ℂ Ambient _ (ComplexTransverseExpansion.vector m) F • ComplexTransverseExpansion.vector m) ∈
      Submodule.span ℂ (Set.range ComplexTransverseExpansion.vector) :=
    Submodule.sum_mem _ (fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m,rfl⟩))
  obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hm
  refine ⟨c,?_⟩
  change ‖c.sum (fun m z => z • ComplexTransverseExpansion.vector m)-F‖ < ε
  rw [hc]
  simpa only [dist_eq_norm] using hs

theorem uniform_finite_approximation (F : Ambient) (hF : ComplexVectorSphere.IsTangential F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ComplexTransverseExpansion.ModeIndex →₀ ℂ, ∀ (k : ℝ) (x : Space) (i : Fin 3),
      ‖value k x i (finiteAmplitude c)-value k x i F‖ < ε := by
  have hB : 0 < bound+1 := by linarith [bound_nonnegative]
  obtain ⟨c,hc⟩ := finite_approximation F hF (ε/(bound+1)) (div_pos hε hB)
  refine ⟨c,?_⟩
  intro k x i
  apply (value_difference_bound k x i _ _).trans_lt
  calc
    _ ≤ (bound+1)*‖finiteAmplitude c-F‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (bound+1)*(ε/(bound+1)) := mul_lt_mul_of_pos_left hc hB
    _=ε := mul_div_cancel₀ _ hB.ne'


end OQ14.HerglotzAngularL2
#print axioms OQ14.HerglotzAngularL2.plane_norm
#print axioms OQ14.HerglotzAngularL2.bound_nonnegative
#print axioms OQ14.HerglotzAngularL2.value_norm_le
#print axioms OQ14.HerglotzAngularL2.value_difference_bound

#print axioms OQ14.HerglotzAngularL2.inner_projected
#print axioms OQ14.HerglotzAngularL2.conjugate_wave
#print axioms OQ14.HerglotzAngularL2.value_toLp
#print axioms OQ14.HerglotzAngularL2.finite_approximation
#print axioms OQ14.HerglotzAngularL2.uniform_finite_approximation
