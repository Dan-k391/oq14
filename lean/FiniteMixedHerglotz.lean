import FiniteMixedTraces
import FiniteAngularHerglotz

/-! Exact identification of the finite Debye pair with the negative-phase angular Herglotz fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.FiniteMixedHerglotz
open Complex MeasureTheory OQ14.Maxwell OQ14.VectorHarmonicNormalization OQ14.SphereHarmonicBasis
open OQ14.ComplexTransverseExpansion OQ14.FiniteMixedFields

theorem continuous_wave (k : ℝ) (x : Maxwell.Space) :
    Continuous (fun θ : SphereReactionKernel.Sphere => SphereReactionKernel.wave k x θ) := by
  unfold SphereReactionKernel.wave
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_subtype_val.inner continuous_const))).mul continuous_const)

theorem wave_scale (k : ℝ) (x : Maxwell.Space) (θ : SphereReactionKernel.Sphere) :
    SphereReactionKernel.wave (-k) x θ=SphereReactionKernel.wave (-1) (k • x) θ := by
  unfold SphereReactionKernel.wave
  congr 2
  rw [real_inner_smul_right]
  push_cast
  ring

theorem electric_scale (k : ℝ) (A : SphereReactionKernel.Sphere → Vector) (x : Maxwell.Space) (i : Fin 3) :
    AngularHerglotz.electric k A x i=AngularHerglotz.electric 1 A (k • x) i := by
  unfold AngularHerglotz.electric SphereWaveCalculus.moment
  apply integral_congr_ae
  filter_upwards with θ
  rw [wave_scale]

theorem incident_E_scale (k : ℝ) (c : ModeIndex →₀ ℂ) (x : Maxwell.Space) :
    (FiniteAngularHerglotz.incident k c).E x=(FiniteAngularHerglotz.incident 1 c).E (k • x) := by
  funext i
  exact electric_scale k _ x i

theorem incident_H_scale (k : ℝ) (c : ModeIndex →₀ ℂ) (x : Maxwell.Space) :
    (FiniteAngularHerglotz.incident k c).H x=(FiniteAngularHerglotz.incident 1 c).H (k • x) := by
  funext i
  exact electric_scale k _ x i

theorem wave_neg (l : ℕ) (p : HarmonicPolynomial.Poly) :
    SolidScalarHelmholtz.wave l ((-1 : ℝ) : ℂ) p=SolidScalarHelmholtz.wave l 1 p := by
  funext x
  simp only [SolidScalarHelmholtz.wave,SolidScalarHelmholtz.radial]
  norm_num

theorem mode_integral (m : ModeIndex) (x : Maxwell.Space) (i : Fin 3) :
    (∫ θ : SphereReactionKernel.Sphere,FiniteVectorAngular.angular m θ i*
      SphereReactionKernel.wave (-1) x θ ∂SphereReactionKernel.surface)=
      phaseFactor m*(normalizer (index m).1 : ℂ)*modeElectric m x i := by
  cases m with
  | inl a =>
    have h := PoloidalPlaneWaveMoment.actual_poloidal_integral (a.1+1) (representative (a.1+1) a.2)
      (representative_homogeneous _ _) (representative_harmonic _ _) (-1) (by norm_num) x i
    simp only [FiniteVectorAngular.angular_poloidal,mul_assoc,integral_const_mul]
    rw [h,wave_neg]
    simp only [modeElectric,SolidMaxwellProfiles.electric,phaseFactor,index,Sum.elim_inl,id_eq]
    have hI : (1 : ℂ)/(I*((-1 : ℝ) : ℂ))=I := by
      push_cast
      field_simp
    have hp : I^(a.1+1)*(((-1 : ℝ) : ℂ))^(a.1+1)=(-I)^(a.1+1) := by
      rw [←mul_pow]
      congr 1
      push_cast
      ring
    rw [show ((4*Real.pi : ℂ)*I^(a.1+1)*(((-1 : ℝ) : ℂ))^(a.1+1)/(I*((-1 : ℝ) : ℂ)))=
      (4*Real.pi : ℂ)*(I^(a.1+1)*(((-1 : ℝ) : ℂ))^(a.1+1))*(1/(I*((-1 : ℝ) : ℂ))) by ring,hI,hp]
    ring
  | inr a =>
    have h := ToroidalPlaneWaveMoment.actual_toroidal_integral (a.1+1) (representative (a.1+1) a.2)
      (representative_homogeneous _ _) (representative_harmonic _ _) (-1) x i
    simp only [FiniteVectorAngular.angular_toroidal,mul_assoc,integral_const_mul]
    rw [h,wave_neg]
    simp only [modeElectric,phaseFactor,index,Sum.elim_inr,id_eq,DebyeMaxwell.teElectric]
    have hp : I^(a.1+1)*(((-1 : ℝ) : ℂ))^(a.1+1)=(-I)^(a.1+1) := by
      rw [←mul_pow]
      congr 1
      push_cast
      ring
    rw [show (4*Real.pi : ℂ)*I^(a.1+1)*(((-1 : ℝ) : ℂ))^(a.1+1)=(4*Real.pi : ℂ)*(I^(a.1+1)*(((-1 : ℝ) : ℂ))^(a.1+1)) by ring,hp]
    ring

theorem incident_electric_eq (c : ModeIndex →₀ ℂ) (x : Maxwell.Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident 1 c).E x i=electric c x i := by
  have hamp : ∀ θ : SphereReactionKernel.Sphere,FiniteVectorAngular.amplitude c θ i=
      ∑ m∈c.support,c m*FiniteVectorAngular.angular m θ i := fun θ => FiniteMixedTraces.amplitude_apply c θ i
  change (∫ θ : SphereReactionKernel.Sphere,FiniteVectorAngular.amplitude c θ i*
    SphereReactionKernel.wave (-1) x θ ∂SphereReactionKernel.surface)=_
  have hint : ∀ m∈c.support,Integrable (fun θ : SphereReactionKernel.Sphere => c m*(FiniteVectorAngular.angular m θ i*
      SphereReactionKernel.wave (-1) x θ)) SphereReactionKernel.surface := by
    intro m _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul ((((continuous_apply i).comp (FiniteVectorAngular.angular m).continuous)).mul
      (continuous_wave _ x))
  simp_rw [hamp,Finset.sum_mul]
  have hs : (fun θ : SphereReactionKernel.Sphere => ∑ m∈c.support,c m*FiniteVectorAngular.angular m θ i*
      SphereReactionKernel.wave (-1) x θ)=
      fun θ => ∑ m∈c.support,c m*(FiniteVectorAngular.angular m θ i*SphereReactionKernel.wave (-1) x θ) := by
    funext θ
    apply Finset.sum_congr rfl
    intro m _
    ring
  rw [hs,integral_finset_sum _ hint]
  simp only [integral_const_mul,mode_integral]
  simp only [electric,scalar]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem incident_magnetic_eq (c : ModeIndex →₀ ℂ) (x : Maxwell.Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident 1 c).H x i=magnetic c x i := by
  have hE : (FiniteAngularHerglotz.incident 1 c).E=electric c :=
    funext (fun y => funext (fun j => incident_electric_eq c y j))
  have h1 := ((FiniteAngularHerglotz.incident 1 c).maxwell x).1
  rw [hE] at h1
  have h2 := congrFun (h1.symm.trans (actual_maxwell c x).1) i
  simp only [Complex.ofReal_one,mul_one] at h2
  exact mul_left_cancel₀ I_ne_zero h2

theorem incident_electric_scaled (k : ℝ) (c : ModeIndex →₀ ℂ) (x : Maxwell.Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident k c).E x i=electric c (k • x) i := by
  rw [incident_E_scale]
  exact incident_electric_eq c _ i

theorem incident_magnetic_scaled (k : ℝ) (c : ModeIndex →₀ ℂ) (x : Maxwell.Space) (i : Fin 3) :
    (FiniteAngularHerglotz.incident k c).H x i=magnetic c (k • x) i := by
  rw [incident_H_scale]
  exact incident_magnetic_eq c _ i

end OQ14.FiniteMixedHerglotz
#print axioms OQ14.FiniteMixedHerglotz.continuous_wave
#print axioms OQ14.FiniteMixedHerglotz.wave_scale
#print axioms OQ14.FiniteMixedHerglotz.electric_scale
#print axioms OQ14.FiniteMixedHerglotz.incident_E_scale
#print axioms OQ14.FiniteMixedHerglotz.incident_H_scale
#print axioms OQ14.FiniteMixedHerglotz.wave_neg
#print axioms OQ14.FiniteMixedHerglotz.mode_integral
#print axioms OQ14.FiniteMixedHerglotz.incident_electric_eq
#print axioms OQ14.FiniteMixedHerglotz.incident_magnetic_eq
#print axioms OQ14.FiniteMixedHerglotz.incident_electric_scaled
#print axioms OQ14.FiniteMixedHerglotz.incident_magnetic_scaled
