import RestrictedTEPower
import ComplexVectorSphere

/-! Actual transverse complex sphere L2 incoming data with the physical power norm. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEInput
open Complex MeasureTheory Maxwell HarmonicPolynomial DebyeRadialTrace
open RestrictedTEIncoming RestrictedTEAmplitude SymmetricHarmonicJets
open scoped ComplexInnerProductSpace
abbrev Sphere := SphereReactionKernel.Sphere
abbrev Vector := ComplexVectorSphere.Vector
abbrev Ambient := ComplexVectorSphere.Ambient

def angularMap (q : Index) : C(Sphere,Vector) :=
  ⟨fun n => (WithLp.equiv 2 (Fin 3 → ℂ)).symm (angularToroidal (polynomial q) n),
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
      ((HarmonicRadiationGeometry.angularToroidal_continuous (polynomial q)).comp continuous_subtype_val)⟩

def amplitudeColumn (q : Index) : C(Sphere,Vector) :=
  (((4*Real.pi : ℂ)*I^q.val.1)*RegularTEIncoming.coefficient q.val.1 true/2) • angularMap q

def amplitudeMap : (Index →₀ ℂ) →ₗ[ℂ] C(Sphere,Vector) :=
  Finsupp.linearCombination ℂ amplitudeColumn

theorem amplitudeMap_apply (A : Index →₀ ℂ) (n : Sphere) (j : Fin 3) :
    amplitudeMap A n j=RestrictedTEAmplitude.amplitude A n j := by
  have hs (s : Finset Index) (F : Index → Vector) : (∑ q ∈ s, F q) j=∑ q ∈ s, F q j :=
    map_sum (EuclideanSpace.proj j : Vector →L[ℂ] ℂ) F s
  simp only [amplitudeMap,Finsupp.linearCombination_apply,Finsupp.sum,ContinuousMap.sum_apply,
    ContinuousMap.coe_smul,Pi.smul_apply,Finset.sum_apply,hs,PiLp.smul_apply,smul_eq_mul,
    amplitudeColumn,RestrictedTEAmplitude.amplitude,FiniteTEIncomingPower.amplitude,FiniteTEIncomingPower.amplitudeCoefficient,
    coefficient,FiniteTEIncomingPower.angular,angularMap]
  apply Finset.sum_congr rfl
  intro q _
  change A q*((((4*Real.pi : ℂ)*I^q.val.1)*RegularTEIncoming.coefficient q.val.1 true/2)*
      angularToroidal (polynomial q) n j)=
    (A q*((4*Real.pi : ℂ)*I^q.val.1))*RegularTEIncoming.coefficient q.val.1 true/2*
      angularToroidal (polynomial q) n j
  ring

def rawInput : (Index →₀ ℂ) →ₗ[ℂ] Ambient :=
  (ContinuousMap.toLp 2 SphereReactionKernel.surface ℂ).toLinearMap.comp amplitudeMap

def input : (Index →₀ ℂ) →ₗ[ℂ] Ambient := (1/(Real.sqrt 2 : ℂ)) • rawInput

theorem raw_norm_sq (A : Index →₀ ℂ) :
    ‖rawInput A‖^2=2*physicalPower A := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def]
  have hEq : (∫ n : Sphere, (⟪rawInput A n,rawInput A n⟫ : ℂ) ∂SphereReactionKernel.surface)=
      ∫ n : Sphere, (energy (RestrictedTEAmplitude.amplitude A n) : ℂ) ∂SphereReactionKernel.surface := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) SphereReactionKernel.surface (amplitudeMap A)] with n hn
    change rawInput A n=amplitudeMap A n at hn
    rw [hn]
    simp only [PiLp.inner_apply,RCLike.inner_apply,amplitudeMap_apply,Fin.sum_univ_three,
      energy,ofReal_add,← mul_conj]
  change (∫ n : Sphere, (⟪rawInput A n,rawInput A n⟫ : ℂ) ∂SphereReactionKernel.surface).re=_
  rw [hEq]
  have hr := congrArg Complex.re (integral_ofReal (𝕜 := ℂ) (μ := SphereReactionKernel.surface)
    (f := fun n : Sphere => energy (RestrictedTEAmplitude.amplitude A n)))
  exact hr.trans (by
  change (∫ n : Sphere, energy (RestrictedTEAmplitude.amplitude A n) ∂SphereReactionKernel.surface)=
    2*((∫ n : Sphere, energy (RestrictedTEAmplitude.amplitude A n) ∂SphereReactionKernel.surface)/2)
  ring)

theorem input_norm_sq (A : Index →₀ ℂ) : ‖input A‖^2=physicalPower A := by
  change ‖(1/(Real.sqrt 2 : ℂ)) • rawInput A‖^2=_
  rw [norm_smul,mul_pow,raw_norm_sq]
  have hs : 0<Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have he := Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)
  simp only [norm_div,norm_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
  field_simp

theorem input_zero_fields (A : Index →₀ ℂ) (h : input A=0) :
    DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A)=0 ∧
      DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A)=0 := by
  apply RestrictedTEPower.fields_zero_of_power_zero A
  rw [← input_norm_sq,h,norm_zero,zero_pow (by decide : (2 : ℕ)≠0)]

theorem input_transverse (A : Index →₀ ℂ) : ComplexVectorSphere.IsTangential (input A) := by
  change ∀ᵐ n : Sphere ∂SphereReactionKernel.surface,
    (⟪ComplexVectorSphere.embedVector n,input A n⟫ : ℂ)=0
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) SphereReactionKernel.surface (amplitudeMap A),
    Lp.coeFn_smul (1/(Real.sqrt 2 : ℂ)) (rawInput A)] with n hn hs
  change rawInput A n=amplitudeMap A n at hn
  change input A n=(1/(Real.sqrt 2 : ℂ)) • rawInput A n at hs
  rw [hs,hn,inner_smul_right]
  have ht := RestrictedTEAmplitude.amplitude_transverse A n
  simp only [dot,position] at ht
  simp only [PiLp.inner_apply,RCLike.inner_apply,ComplexVectorSphere.embed_apply,
    conj_ofReal,amplitudeMap_apply,Fin.sum_univ_three]
  linear_combination (1/(Real.sqrt 2 : ℂ))*ht

end OQ14.RestrictedTEInput
#print axioms OQ14.RestrictedTEInput.amplitudeMap_apply
#print axioms OQ14.RestrictedTEInput.raw_norm_sq
#print axioms OQ14.RestrictedTEInput.input_norm_sq
#print axioms OQ14.RestrictedTEInput.input_zero_fields
#print axioms OQ14.RestrictedTEInput.input_transverse
