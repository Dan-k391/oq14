import PointDyadicFarField
import SourceFarAmplitude
import SourceCoreReaction
import DebyeUnitReaction

/-! Actual unit-frequency free far-field coefficients fix the layered source-mode signs. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FreeSourceCoefficients
open OQ14.Maxwell OQ14.SphereHarmonicBasis OQ14.VectorHarmonicNormalization
open OQ14.PlaneDebyeCoefficients OQ14.TransversePlaneFields OQ14.DebyeUnitReaction
open scoped ComplexInnerProductSpace

def freeAmplitude (y : Space) (j : Fin 3) : ComplexVectorSphere.Ambient :=
  ((4*Real.pi : ℂ)⁻¹) • field 1 y j

theorem phaseCoefficient_one (l : ℕ) :
    phaseCoefficient l 1=(4*Real.pi : ℂ)*Complex.I*SourceRadiation.phase l := by
  unfold phaseCoefficient
  simp only [Complex.ofReal_one]
  rw [mul_assoc (4*Real.pi : ℂ),← mul_pow]
  have he : Complex.I*(-1 : ℂ)= -Complex.I := by ring_nf
  rw [he]
  simp only [SourceRadiation.phase,pow_succ]
  ring_nf
  rw [Complex.I_sq]
  ring_nf

theorem poloidal_coefficient (a : PositiveIndex) (y : Space) (j : Fin 3) :
    ⟪ComplexTransverseExpansion.vector (Sum.inl a),freeAmplitude y j⟫=
      -(normalizer a.1 : ℂ)*SourceRadiation.phase (a.1+1)*electric a y j := by
  rw [freeAmplitude,inner_smul_right,normalized_poloidal a 1 (by norm_num),phaseCoefficient_one]
  have hw := SolidWaveReality.wave_neg (a.1+1) 1 (representative (a.1+1) a.2)
  change SolidScalarHelmholtz.wave (a.1+1) (-1) (representative (a.1+1) a.2)=_ at hw
  simp only [Complex.ofReal_one,mul_neg,mul_one,hw]
  change (4*Real.pi : ℂ)⁻¹*((normalizer a.1 : ℂ)*
    ((4*Real.pi : ℂ)*Complex.I*SourceRadiation.phase (a.1+1)/(-Complex.I))*electric a y j)=_
  have hp : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp,Complex.I_ne_zero]
  ring_nf

theorem toroidal_coefficient (a : PositiveIndex) (y : Space) (j : Fin 3) :
    ⟪ComplexTransverseExpansion.vector (Sum.inr a),freeAmplitude y j⟫=
      Complex.I*(normalizer a.1 : ℂ)*SourceRadiation.phase (a.1+1)*toroidal a y j := by
  rw [freeAmplitude,inner_smul_right,normalized_toroidal a 1,phaseCoefficient_one]
  have hw := SolidWaveReality.wave_neg (a.1+1) 1 (representative (a.1+1) a.2)
  change SolidScalarHelmholtz.wave (a.1+1) (-1) (representative (a.1+1) a.2)=_ at hw
  simp only [Complex.ofReal_one,hw]
  change (4*Real.pi : ℂ)⁻¹*((normalizer a.1 : ℂ)*
    ((4*Real.pi : ℂ)*Complex.I*SourceRadiation.phase (a.1+1))*toroidal a y j)=_
  have hp : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hp]
  ring_nf

def tmCoefficient (a : PositiveIndex) (y : Space) (j : Fin 3) : ℂ := -weight a*electric a y j
def teCoefficient (a : PositiveIndex) (y : Space) (j : Fin 3) : ℂ := -Complex.I*weight a*toroidal a y j

theorem tm_source_coefficient (a : PositiveIndex) (y : Space) (j : Fin 3) :
    (normalizer a.1 : ℂ)*⟪ComplexTransverseExpansion.vector (Sum.inl a),freeAmplitude y j⟫=
      tmCoefficient a y j*SourceRadiation.phase (a.1+1) := by
  rw [poloidal_coefficient]
  have he := normalizer_sq a.1
  dsimp [tmCoefficient,weight]
  linear_combination -electric a y j*SourceRadiation.phase (a.1+1)*he

theorem te_source_coefficient (a : PositiveIndex) (y : Space) (j : Fin 3) :
    (normalizer a.1 : ℂ)*⟪ComplexTransverseExpansion.vector (Sum.inr a),freeAmplitude y j⟫=
      teCoefficient a y j*(-SourceRadiation.phase (a.1+1)) := by
  rw [toroidal_coefficient]
  have he := normalizer_sq a.1
  dsimp [teCoefficient,weight]
  linear_combination Complex.I*toroidal a y j*SourceRadiation.phase (a.1+1)*he

theorem projected_component (n : Sphere) (i j : Fin 3) :
    projected j n i=SphereReactionKernel.amplitude n i j := by
  simp [projected,unit,normal,ComplexVectorSphere.embed_apply,PiLp.smul_apply,
    EuclideanSpace.single_apply,SphereReactionKernel.amplitude,eq_comm,mul_comm]

theorem actual_point_amplitude (y : Space) (j : Fin 3) :
    ∀ᵐ (n : Sphere) ∂angularMeasure,∀ i : Fin 3,
      Filter.Tendsto (fun r : ℝ => MaxwellFarField.factor 1 r*DyadicKernel.dyadic 1 (r • (n : Space)-y) i j)
        Filter.atTop (nhds (freeAmplitude y j n i)) := by
  filter_upwards [MeasureTheory.Lp.coeFn_smul ((4*Real.pi : ℂ)⁻¹) (field 1 y j),
    (plane 1 y j).coeFn_toLp (p := 2) (𝕜 := ℂ) angularMeasure] with n hs he
  change field 1 y j n=plane 1 y j n at he
  change freeAmplitude y j n= ((4*Real.pi : ℂ)⁻¹) • field 1 y j n at hs
  intro i
  have hn : ‖(n : Space)‖=1 := by simpa only [Metric.mem_sphere,dist_zero_right] using n.property
  have h := PointDyadicFarField.electric_limit 1 (n : Space) y hn i j
  have hw : SphereReactionKernel.wave (-1) y n=
      Complex.exp (-Complex.I*(@inner ℝ Space _ (n : Space) y : ℂ)) := by
    unfold SphereReactionKernel.wave
    congr 1
    push_cast
    ring_nf
  have ht : DyadicRadiation.transverse (n : Space) i j=SphereReactionKernel.amplitude n i j := by
    simp only [DyadicRadiation.transverse,GreenKernel.unitCoordinate,hn,Complex.ofReal_one,
      div_one,SphereReactionKernel.amplitude]
  convert h using 1
  rw [hs,he]
  simp only [plane,ContinuousMap.coe_mk,PiLp.smul_apply,projected_component,hw,ht,
    Complex.ofReal_one,one_pow,one_mul,smul_eq_mul]
  ring_nf

theorem vacuum_amplitude (d : SourceRadialSystem.Data) :
    SourceRadiation.amplitude (SourceCoreReaction.vacuum d)= -Complex.I := by
  simp only [SourceRadiation.amplitude,SourceCoreReaction.vacuum]
  rw [SourceCoreReaction.vacuum_coefficients]
  simp only [Complex.inv_I]

theorem vacuum_tm_far (d : SourceRadialSystem.Data) (p : HarmonicPolynomial.Poly)
    (hp : p.IsHomogeneous d.l) (n : Sphere) :
    Filter.Tendsto (fun r : ℝ => SourceFarAmplitude.electricWeighted (SourceCoreReaction.vacuum d) p
      (r • (n : Space))) Filter.atTop
      (nhds (SourceRadiation.phase d.l • HarmonicRadiationFactors.poloidal p n)) := by
  have h := SourceFarAmplitude.electric_ray_limit (SourceCoreReaction.vacuum d) p hp n
  have he : SourceRadiation.amplitude (SourceCoreReaction.vacuum d)*SourceRadiation.phase d.l*Complex.I=
      SourceRadiation.phase d.l := by
    rw [vacuum_amplitude]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  simpa only [show (SourceCoreReaction.vacuum d).l=d.l from rfl,he] using h

theorem vacuum_te_far (d : SourceRadialSystem.Data) (p : HarmonicPolynomial.Poly)
    (hp : p.IsHomogeneous d.l) (n : Sphere) :
    Filter.Tendsto (fun r : ℝ => SourceFarAmplitude.magneticWeighted (SourceCoreReaction.vacuum d) p
      (r • (n : Space))) Filter.atTop
      (nhds ((-SourceRadiation.phase d.l) • DebyeRadialTrace.angularToroidal p n)) := by
  have h := SourceFarAmplitude.magnetic_ray_limit (SourceCoreReaction.vacuum d) p hp n
  have he : -Complex.I*SourceRadiation.amplitude (SourceCoreReaction.vacuum d)*SourceRadiation.phase d.l=
      -SourceRadiation.phase d.l := by
    rw [vacuum_amplitude]
    ring_nf
    rw [Complex.I_sq]
    ring_nf
  simpa only [show (SourceCoreReaction.vacuum d).l=d.l from rfl,he] using h

end OQ14.FreeSourceCoefficients

#print axioms OQ14.FreeSourceCoefficients.phaseCoefficient_one
#print axioms OQ14.FreeSourceCoefficients.poloidal_coefficient
#print axioms OQ14.FreeSourceCoefficients.toroidal_coefficient
#print axioms OQ14.FreeSourceCoefficients.tm_source_coefficient
#print axioms OQ14.FreeSourceCoefficients.te_source_coefficient
#print axioms OQ14.FreeSourceCoefficients.projected_component
#print axioms OQ14.FreeSourceCoefficients.actual_point_amplitude
#print axioms OQ14.FreeSourceCoefficients.vacuum_amplitude
#print axioms OQ14.FreeSourceCoefficients.vacuum_tm_far
#print axioms OQ14.FreeSourceCoefficients.vacuum_te_far
