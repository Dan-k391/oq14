import ComplexTransverseExpansion
import HarmonicRadiationFactors

/-! Literal continuous representatives of the normalized complex transverse harmonic basis. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace OQ14.FiniteVectorAngular
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.ComplexTransverseExpansion
open scoped ComplexInnerProductSpace

def realAngular : ModeIndex → C(Sphere,Space)
  | Sum.inl a => normalizer a.1 • restriction (AngularHarmonicEnergy.tangential (representative (a.1+1) a.2) (a.1+1))
  | Sum.inr a => normalizer a.1 • restriction (AngularHarmonicEnergy.toroidal (representative (a.1+1) a.2))

def angular (m : ModeIndex) : C(Sphere,ComplexVectorSphere.Vector) :=
  ⟨fun n => ComplexVectorSphere.embedVector (realAngular m n),
    ComplexVectorSphere.embedVector.continuous.comp (realAngular m).continuous⟩

theorem realAngular_toLp (m : ModeIndex) :
    ContinuousMap.toLp 2 angularMeasure ℝ (realAngular m)=polarized m := by
  cases m <;> simp only [realAngular,map_smul,polarized,Sum.elim_inl,Sum.elim_inr,
    normalizedP,normalizedT,poloidal,toroidalField,VectorHarmonicNormalization.restrictionL2]

theorem angular_toLp (m : ModeIndex) :
    ContinuousMap.toLp 2 angularMeasure ℂ (angular m)=ComplexTransverseExpansion.vector m := by
  unfold ComplexTransverseExpansion.vector
  rw [←realAngular_toLp]
  apply Lp.ext
  filter_upwards [(angular m).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure,
    ComplexVectorSphere.embedVector.coeFn_compLpL (ContinuousMap.toLp 2 angularMeasure ℝ (realAngular m)),
    (realAngular m).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n ha he hr
  change ComplexVectorSphere.realLift (ContinuousMap.toLp 2 angularMeasure ℝ (realAngular m)) n=
    ComplexVectorSphere.embedVector (ContinuousMap.toLp 2 angularMeasure ℝ (realAngular m) n) at he
  rw [ha,he,hr]
  rfl

theorem angular_poloidal (a : PositiveIndex) (n : Sphere) (i : Fin 3) :
    angular (Sum.inl a) n i=(normalizer a.1 : ℂ)*
      DebyeRadialTrace.angularPoloidal (representative (a.1+1) a.2) (a.1+1) n i := by
  simp only [angular,realAngular,ContinuousMap.coe_mk,ContinuousMap.smul_apply,
    ComplexVectorSphere.embed_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,
    restriction_poloidal_component]

theorem angular_toroidal (a : PositiveIndex) (n : Sphere) (i : Fin 3) :
    angular (Sum.inr a) n i=(normalizer a.1 : ℂ)*
      DebyeRadialTrace.angularToroidal (representative (a.1+1) a.2) n i := by
  simp only [angular,realAngular,ContinuousMap.coe_mk,ContinuousMap.smul_apply,
    ComplexVectorSphere.embed_apply,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,
    restriction_toroidal_component]

def amplitude (c : ModeIndex →₀ ℂ) : C(Sphere,ComplexVectorSphere.Vector) :=
  ∑ m∈c.support,c m • angular m

theorem amplitude_toLp (c : ModeIndex →₀ ℂ) :
    ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c)=
      ∑ m∈c.support,c m • ComplexTransverseExpansion.vector m := by
  simp only [amplitude,map_sum,map_smul,angular_toLp]

theorem amplitude_coefficient (c : ModeIndex →₀ ℂ) (m : ModeIndex) :
    ⟪ComplexTransverseExpansion.vector m,ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c)⟫=c m := by
  classical
  rw [amplitude_toLp,inner_sum]
  simp only [inner_smul_right,orthonormal_iff_ite.mp vector_orthonormal]
  by_cases hm : m∈c.support
  · simp [hm]
  · simp [hm,Finsupp.not_mem_support_iff.mp hm]

theorem amplitude_nonzero (c : ModeIndex →₀ ℂ) (hc : c≠0) :
    ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c)≠0 := by
  intro h
  apply hc
  ext m
  have he := congrArg (fun F : ComplexVectorSphere.Ambient => ⟪ComplexTransverseExpansion.vector m,F⟫) h
  simpa only [amplitude_coefficient,inner_zero_right,Finsupp.zero_apply] using he

theorem amplitude_norm_sq (c : ModeIndex →₀ ℂ) :
    ‖ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c)‖^2=∑ m∈c.support,‖c m‖^2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ,amplitude_toLp,
    vector_orthonormal.inner_sum]
  simp only [map_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im]
  apply Finset.sum_congr rfl
  intro m _
  rw [←Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply]
  change (c m).re*(c m).re-(-(c m).im)*(c m).im=(c m).re*(c m).re+(c m).im*(c m).im
  ring

theorem amplitude_energy (c : ModeIndex →₀ ℂ) :
    (∫ n : Sphere,Maxwell.energy (fun i => amplitude c n i) ∂angularMeasure)=
      ‖ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c)‖^2 := by
  have hi : Integrable (fun n : Sphere => ⟪amplitude c n,amplitude c n⟫) angularMeasure :=
    ((amplitude c).continuous.inner (amplitude c).continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : ⟪ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c),
      ContinuousMap.toLp 2 angularMeasure ℂ (amplitude c)⟫=
      ∫ n : Sphere,⟪amplitude c n,amplitude c n⟫ ∂angularMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(amplitude c).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hn
    rw [hn]
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ,he,←integral_re hi]
  apply integral_congr_ae
  filter_upwards with n
  rw [←InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
  simp only [PiLp.norm_sq_eq_of_L2,Fin.sum_univ_three,Maxwell.energy,Complex.normSq_eq_norm_sq]

theorem amplitude_energy_positive (c : ModeIndex →₀ ℂ) (hc : c≠0) :
    0<(∫ n : Sphere,Maxwell.energy (fun i => amplitude c n i) ∂angularMeasure) := by
  rw [amplitude_energy]
  exact sq_pos_of_pos (norm_pos_iff.mpr (amplitude_nonzero c hc))

end OQ14.FiniteVectorAngular




#print axioms OQ14.FiniteVectorAngular.realAngular_toLp
#print axioms OQ14.FiniteVectorAngular.angular_toLp
#print axioms OQ14.FiniteVectorAngular.angular_poloidal
#print axioms OQ14.FiniteVectorAngular.angular_toroidal
#print axioms OQ14.FiniteVectorAngular.amplitude_toLp
#print axioms OQ14.FiniteVectorAngular.amplitude_coefficient
#print axioms OQ14.FiniteVectorAngular.amplitude_nonzero
#print axioms OQ14.FiniteVectorAngular.amplitude_norm_sq
#print axioms OQ14.FiniteVectorAngular.amplitude_energy
#print axioms OQ14.FiniteVectorAngular.amplitude_energy_positive
