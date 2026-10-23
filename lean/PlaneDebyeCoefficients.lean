import PlaneFieldCoefficients

/-! Actual normalized transverse plane coefficients in regular Debye fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.PlaneDebyeCoefficients
open MeasureTheory OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.ComplexVectorSphere
open OQ14.TransversePlaneFields OQ14.VectorHarmonicNormalization OQ14.PlaneFieldCoefficients
open scoped ComplexInnerProductSpace

def phaseCoefficient (l : ℕ) (k : ℝ) : ℂ := (4*Real.pi : ℂ)*Complex.I^l*(-(k : ℂ))^l

theorem raw_poloidal (a : Σ l,Index l) (k : ℝ) (hk : k≠0) (x : Space) (i : Fin 3) :
    ⟪realLift (VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.poloidalField a)),field k x i⟫=
      (phaseCoefficient a.1 k/(Complex.I*(-(k : ℂ))))*
        DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave a.1 (-k) (representative a.1 a.2)) x i := by
  rw [coefficient_integral _ (TransverseHarmonicBasis.poloidal_tangent a)]
  have he : (∫ n : Sphere,((VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.poloidalField a)) n i : ℂ)*
      SphereReactionKernel.wave (-k) x n ∂angularMeasure)=
      ∫ n : Sphere,DebyeRadialTrace.angularPoloidal (representative a.1 a.2) a.1 n i*
        SphereReactionKernel.wave (-k) x n ∂angularMeasure := by
    apply integral_congr_ae
    filter_upwards [(VectorHarmonicBasisSpan.poloidalField a).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n hn
    change VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.poloidalField a) n=
      VectorHarmonicBasisSpan.poloidalField a n at hn
    rw [hn]
    congr 1
    exact restriction_poloidal_component _ a.1 n i
  rw [he]
  simpa only [phaseCoefficient,Complex.ofReal_neg,SphereReactionKernel.surface] using PoloidalPlaneWaveMoment.actual_poloidal_integral a.1 _ (representative_homogeneous a.1 a.2)
    (representative_harmonic a.1 a.2) (-k) (neg_ne_zero.mpr hk) x i

theorem raw_toroidal (a : Σ l,Index l) (k : ℝ) (x : Space) (i : Fin 3) :
    ⟪realLift (VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.toroidalField a)),field k x i⟫=
      phaseCoefficient a.1 k*
        DebyeCalculus.toroidal (SolidScalarHelmholtz.wave a.1 (-k) (representative a.1 a.2)) x i := by
  rw [coefficient_integral _ (TransverseHarmonicBasis.toroidal_tangent a)]
  have he : (∫ n : Sphere,((VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.toroidalField a)) n i : ℂ)*
      SphereReactionKernel.wave (-k) x n ∂angularMeasure)=
      ∫ n : Sphere,DebyeRadialTrace.angularToroidal (representative a.1 a.2) n i*
        SphereReactionKernel.wave (-k) x n ∂angularMeasure := by
    apply integral_congr_ae
    filter_upwards [(VectorHarmonicBasisSpan.toroidalField a).coeFn_toLp (p := 2) (𝕜 := ℝ) angularMeasure] with n hn
    change VectorHarmonicSeparation.lift (VectorHarmonicBasisSpan.toroidalField a) n=
      VectorHarmonicBasisSpan.toroidalField a n at hn
    rw [hn]
    congr 1
    exact restriction_toroidal_component _ n i
  rw [he]
  simpa only [phaseCoefficient,Complex.ofReal_neg,SphereReactionKernel.surface] using ToroidalPlaneWaveMoment.actual_toroidal_integral a.1 _ (representative_homogeneous a.1 a.2)
    (representative_harmonic a.1 a.2) (-k) x i

theorem normalized_poloidal (a : PositiveIndex) (k : ℝ) (hk : k≠0) (x : Space) (i : Fin 3) :
    ⟪ComplexTransverseExpansion.vector (Sum.inl a),field k x i⟫=
      (normalizer a.1 : ℂ)*(phaseCoefficient (a.1+1) k/(Complex.I*(-(k : ℂ))))*
        DebyeMaxwell.tmElectric (SolidScalarHelmholtz.wave (a.1+1) (-k) (representative (a.1+1) a.2)) x i := by
  change ⟪realLift (normalizer a.1 • VectorHarmonicSeparation.lift
    (VectorHarmonicBasisSpan.poloidalField ⟨a.1+1,a.2⟩)),field k x i⟫=_
  rw [map_smul]
  rw [← Complex.coe_smul,inner_smul_left,Complex.conj_ofReal]
  rw [raw_poloidal ⟨a.1+1,a.2⟩ k hk]
  push_cast
  ring

theorem normalized_toroidal (a : PositiveIndex) (k : ℝ) (x : Space) (i : Fin 3) :
    ⟪ComplexTransverseExpansion.vector (Sum.inr a),field k x i⟫=
      (normalizer a.1 : ℂ)*phaseCoefficient (a.1+1) k*
        DebyeCalculus.toroidal (SolidScalarHelmholtz.wave (a.1+1) (-k) (representative (a.1+1) a.2)) x i := by
  change ⟪realLift (normalizer a.1 • VectorHarmonicSeparation.lift
    (VectorHarmonicBasisSpan.toroidalField ⟨a.1+1,a.2⟩)),field k x i⟫=_
  rw [map_smul]
  rw [← Complex.coe_smul,inner_smul_left,Complex.conj_ofReal]
  rw [raw_toroidal ⟨a.1+1,a.2⟩]
  push_cast
  ring

end OQ14.PlaneDebyeCoefficients

#print axioms OQ14.PlaneDebyeCoefficients.raw_poloidal
#print axioms OQ14.PlaneDebyeCoefficients.raw_toroidal
#print axioms OQ14.PlaneDebyeCoefficients.normalized_poloidal
#print axioms OQ14.PlaneDebyeCoefficients.normalized_toroidal
