import FiniteMixedFields

/-! Actual incoming traces of finite normalized TM and TE regular fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.FiniteMixedTraces
open Complex Filter Set Metric OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.ComplexTransverseExpansion OQ14.FiniteMixedFields
open scoped Topology

def angular (m : ModeIndex) : C(Sphere,Vector) :=
  ⟨fun n i => FiniteVectorAngular.angular m n i,
    continuous_pi (fun i => (continuous_apply i).comp (FiniteVectorAngular.angular m).continuous)⟩

def radialAngular (m : ModeIndex) : C(Sphere,Vector) :=
  (normalizer (index m).1 : ℂ) • RegularTMIncoming.angularR (polynomial m)

theorem poloidal_factor (a : PositiveIndex) (n : Sphere) (i : Fin 3) :
    angular (Sum.inl a) n i=(normalizer a.1 : ℂ)*
      HarmonicRadiationFactors.poloidal (representative (a.1+1) a.2) n i := by
  rw [show angular (Sum.inl a) n i=FiniteVectorAngular.angular (Sum.inl a) n i from rfl,
    FiniteVectorAngular.angular_poloidal,HarmonicRadiationFactors.poloidal_formula _ _ (representative_homogeneous _ _)]
  simp only [DebyeRadialTrace.angularPoloidal,HarmonicRadiationFactors.radial]
  ring

def electricCoefficient : ModeIndex → ℝ → ℂ
  | Sum.inl a,r => phaseFactor (Sum.inl a)*(RegularTEIncoming.phase true r*RegularTEIncoming.radialD (a.1+1) true r/2)
  | Sum.inr a,r => phaseFactor (Sum.inr a)*(RegularTEIncoming.phase true r*RegularTEIncoming.radial (a.1+1) true r/2)
def magneticCoefficient : ModeIndex → ℝ → ℂ
  | Sum.inl a,r => phaseFactor (Sum.inl a)*(-I*(RegularTEIncoming.phase true r*RegularTEIncoming.radial (a.1+1) true r)/2)
  | Sum.inr a,r => phaseFactor (Sum.inr a)*(I*(RegularTEIncoming.phase true r*RegularTEIncoming.radialD (a.1+1) true r)/2)
def radialCoefficient : ModeIndex → ℝ → ℂ
  | Sum.inl a,r => phaseFactor (Sum.inl a)*(((a.1+1 : ℕ) : ℂ)*((a.1+1 : ℕ)+1)*
      (RegularTEIncoming.phase true r*RegularTEIncoming.radial (a.1+1) true r/(r : ℂ))/2)
  | Sum.inr _,_ => 0

theorem electricCoefficient_limit (m : ModeIndex) :
    Tendsto (electricCoefficient m) atTop (𝓝 ((2*Real.pi : ℂ)*I)) := by
  cases m with
  | inl a =>
    have h := ((RegularTEIncoming.scaled_radialD_limit (a.1+1) true).div_const (2 : ℂ)).const_mul (phaseFactor (Sum.inl a))
    simp only [if_pos rfl,if_true] at h
    rw [incoming_poloidal_phase] at h
    exact h
  | inr a =>
    have h := ((RegularTEIncoming.scaled_radial_limit (a.1+1) true).div_const (2 : ℂ)).const_mul (phaseFactor (Sum.inr a))
    have he : phaseFactor (Sum.inr a)*(RegularTEIncoming.coefficient (a.1+1) true/2)=(2*Real.pi : ℂ)*I := by
      rw [←mul_div_assoc]
      exact incoming_toroidal_phase a
    rw [he] at h
    exact h

theorem magneticCoefficient_limit (m : ModeIndex) :
    Tendsto (magneticCoefficient m) atTop (𝓝 ((2*Real.pi : ℂ)*I)) := by
  cases m with
  | inl a =>
    have h := (((RegularTEIncoming.scaled_radial_limit (a.1+1) true).const_mul (-I)).div_const (2 : ℂ)).const_mul (phaseFactor (Sum.inl a))
    have he : phaseFactor (Sum.inl a)*(-I*RegularTEIncoming.coefficient (a.1+1) true/2)=(2*Real.pi : ℂ)*I := by
      convert incoming_poloidal_phase a using 1 <;> ring
    rw [he] at h
    exact h
  | inr a =>
    have h := (((RegularTEIncoming.scaled_radialD_limit (a.1+1) true).const_mul I).div_const (2 : ℂ)).const_mul (phaseFactor (Sum.inr a))
    have he : phaseFactor (Sum.inr a)*(I*(RegularTEIncoming.coefficient (a.1+1) true*(-I))/2)=(2*Real.pi : ℂ)*I := by
      calc
        _ = phaseFactor (Sum.inr a)*RegularTEIncoming.coefficient (a.1+1) true/2 := by
          have hi : I*(-I)=(1 : ℂ) := by norm_num
          rw [show I*(RegularTEIncoming.coefficient (a.1+1) true*(-I))=
            (I*(-I))*RegularTEIncoming.coefficient (a.1+1) true by ring,hi,one_mul,mul_div_assoc]
        _ = _ := incoming_toroidal_phase a
    simp only [if_pos rfl,if_true] at h
    rw [he] at h
    exact h

theorem radialCoefficient_limit (m : ModeIndex) : Tendsto (radialCoefficient m) atTop (𝓝 0) := by
  cases m with
  | inr a => exact tendsto_const_nhds
  | inl a =>
    have h : Tendsto (fun r : ℝ => RegularTEIncoming.phase true r*RegularTEIncoming.radial (a.1+1) true r/(r : ℂ)) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv,mul_zero] using
        (RegularTEIncoming.scaled_radial_limit (a.1+1) true).mul HankelEnergy.inverse_real_tendsto
    simpa only [mul_zero,zero_div] using
      ((h.const_mul (((a.1+1 : ℕ) : ℂ)*((a.1+1 : ℕ)+1))).div_const (2 : ℂ)).const_mul (phaseFactor (Sum.inl a))

def electricModeMap (m : ModeIndex) (r : ℝ) : C(Sphere,Vector) :=
  electricCoefficient m r • angular m+radialCoefficient m r • radialAngular m
def magneticModeMap (m : ModeIndex) (r : ℝ) : C(Sphere,Vector) := magneticCoefficient m r • angular m

theorem electricModeMap_actual (m : ModeIndex) (r : ℝ) (hr : 0<r) (n : Sphere) :
    (RegularTEIncoming.phase true r*(r : ℂ)) •
      ((phaseFactor m*(normalizer (index m).1 : ℂ)) • halfElectric m true (r • (n : Space)))=
      electricModeMap m r n := by
  cases m with
  | inl a =>
    rw [show halfElectric (Sum.inl a) true=RegularTMIncoming.electric (a.1+1) true (representative (a.1+1) a.2) from rfl,
      RegularTMIncoming.electric_ray _ _ _ (representative_homogeneous _ _) (representative_harmonic _ _) n r hr]
    ext i
    simp only [electricModeMap,electricCoefficient,radialCoefficient,radialAngular,polynomial,degree,index,
      Sum.elim_inl,id_eq,ContinuousMap.add_apply,ContinuousMap.smul_apply,RegularTMIncoming.angularR,
      ContinuousMap.coe_mk,Pi.smul_apply,Pi.add_apply,smul_eq_mul,poloidal_factor]
    have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
    field_simp [hrc]
    ring
  | inr a =>
    rw [show halfElectric (Sum.inr a) true=RegularTEIncoming.electric (a.1+1) true (representative (a.1+1) a.2) from rfl,
      RegularTEIncoming.electric_ray _ _ _ (representative_homogeneous _ _) n r hr]
    ext i
    simp only [electricModeMap,electricCoefficient,radialCoefficient,zero_smul,add_zero,angular,
      FiniteVectorAngular.angular_toroidal,index,Sum.elim_inr,id_eq,ContinuousMap.smul_apply,
      ContinuousMap.coe_mk,Pi.smul_apply,smul_eq_mul]
    have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
    field_simp [hrc]
    ring

theorem magneticModeMap_actual (m : ModeIndex) (r : ℝ) (hr : 0<r) (n : Sphere) :
    (RegularTEIncoming.phase true r*(r : ℂ)) •
      crossProduct (DebyeRadialTrace.position n)
        ((phaseFactor m*(normalizer (index m).1 : ℂ)) • halfMagnetic m true (r • (n : Space)))=
      magneticModeMap m r n := by
  rw [map_smul]
  cases m with
  | inl a =>
    rw [show halfMagnetic (Sum.inl a) true=RegularTMIncoming.magnetic (a.1+1) true (representative (a.1+1) a.2) from rfl,
      RegularTMIncoming.magnetic_tangent_ray _ _ _ (representative_homogeneous _ _) n r hr]
    ext i
    simp only [magneticModeMap,magneticCoefficient,index,Sum.elim_inl,id_eq,ContinuousMap.smul_apply,
      Pi.smul_apply,smul_eq_mul,poloidal_factor]
    have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
    field_simp [hrc]
    ring
  | inr a =>
    rw [show halfMagnetic (Sum.inr a) true=RegularTEIncoming.magnetic (a.1+1) true (representative (a.1+1) a.2) from rfl,
      RegularTEIncoming.magnetic_tangent_ray _ _ _ (representative_homogeneous _ _) (representative_harmonic _ _) n r hr]
    ext i
    simp only [magneticModeMap,magneticCoefficient,angular,FiniteVectorAngular.angular_toroidal,index,
      Sum.elim_inr,id_eq,ContinuousMap.smul_apply,ContinuousMap.coe_mk,Pi.smul_apply,smul_eq_mul]
    have hrc : (r : ℂ)≠0 := ofReal_ne_zero.mpr hr.ne'
    field_simp [hrc]
    ring

theorem electricModeMap_limit (m : ModeIndex) :
    Tendsto (electricModeMap m) atTop (𝓝 (((2*Real.pi : ℂ)*I) • angular m)) := by
  have h := ((electricCoefficient_limit m).smul_const (angular m)).add
    ((radialCoefficient_limit m).smul_const (radialAngular m))
  convert h using 1
  congr 1
  ext n i
  simp [smul_eq_mul]

theorem magneticModeMap_limit (m : ModeIndex) :
    Tendsto (magneticModeMap m) atTop (𝓝 (((2*Real.pi : ℂ)*I) • angular m)) :=
  (magneticCoefficient_limit m).smul_const (angular m)

def electricMap (c : ModeIndex →₀ ℂ) (r : ℝ) : C(Sphere,Vector) := ∑ m∈c.support,c m • electricModeMap m r
def magneticMap (c : ModeIndex →₀ ℂ) (r : ℝ) : C(Sphere,Vector) := ∑ m∈c.support,c m • magneticModeMap m r
def amplitude (c : ModeIndex →₀ ℂ) : C(Sphere,Vector) :=
  ⟨fun n i => FiniteVectorAngular.amplitude c n i,
    continuous_pi (fun i => (continuous_apply i).comp (FiniteVectorAngular.amplitude c).continuous)⟩

theorem amplitude_apply (c : ModeIndex →₀ ℂ) (n : Sphere) (i : Fin 3) :
    amplitude c n i=∑ m∈c.support,c m*angular m n i := by
  change (EuclideanSpace.proj i : ComplexVectorSphere.Vector →L[ℂ] ℂ)
    (∑ m∈c.support,c m • FiniteVectorAngular.angular m n)=_
  simp only [map_sum,map_smul,smul_eq_mul]
  rfl

theorem electricMap_limit (c : ModeIndex →₀ ℂ) :
    Tendsto (electricMap c) atTop (𝓝 (((2*Real.pi : ℂ)*I) • amplitude c)) := by
  have h := tendsto_finset_sum c.support (fun m _ => (electricModeMap_limit m).const_smul (c m))
  convert h using 1
  congr 1
  ext n i
  simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  rw [amplitude_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem magneticMap_limit (c : ModeIndex →₀ ℂ) :
    Tendsto (magneticMap c) atTop (𝓝 (((2*Real.pi : ℂ)*I) • amplitude c)) := by
  have h := tendsto_finset_sum c.support (fun m _ => (magneticModeMap_limit m).const_smul (c m))
  convert h using 1
  congr 1
  ext n i
  simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,Pi.smul_apply,Finset.sum_apply,smul_eq_mul]
  rw [amplitude_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

end OQ14.FiniteMixedTraces
