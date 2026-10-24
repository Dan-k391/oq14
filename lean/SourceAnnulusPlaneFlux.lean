import SourceAnnulusStateBounds
import SourceRemotePlaneBandTail

/-! The plane area estimate for the stack annulus, and the vanishing of the absolute plane flux of the
paired-shell source band through the annulus section as the shell index tends to infinity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceAnnulusPlaneFlux
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.PlaneInverseCube OQ14.SourceRemotePlaneBand
open scoped Topology

/-- The annulus section of the plane. -/
def annSection (R X : ℝ) : Set Plane := {q : Plane | R<‖q‖ ∧ ‖q‖ ≤ X}

theorem section_measurable (R X : ℝ) : MeasurableSet (annSection R X) :=
  (measurableSet_lt measurable_const measurable_norm).inter (measurableSet_le measurable_norm measurable_const)

theorem diskConstant_nonneg : 0 ≤ diskConstant := by
  unfold diskConstant
  have : 0 ≤ (volume : Measure Plane).real (ball 0 1) := measureReal_nonneg
  linarith

theorem annulus_integral_le (F : Plane → ℂ) (C R X : ℝ) (hC : 0 ≤ C) (hR : 0<R) (hRX : R ≤ X)
    (hF : AEStronglyMeasurable F (volume.restrict (annSection R X)))
    (hb : ∀ q : Plane, R<‖q‖ → ‖q‖ ≤ X → ‖F q‖ ≤ C/‖q‖^3) :
    IntegrableOn (fun q => ‖F q‖) (annSection R X) ∧
      (∫ q in annSection R X, ‖F q‖) ≤ C*diskConstant*(X-R)/R^2 := by
  have hX : 0<X := hR.trans_le hRX
  let g : Plane → ℝ := fun q => C*(profile R ‖q‖-profile X ‖q‖)
  have hgi : Integrable g :=
    ((inverse_cube_integrable R hR).sub (inverse_cube_integrable X hX)).const_mul C
  have hg0 : ∀ q : Plane, 0 ≤ g q := by
    intro q
    apply mul_nonneg hC
    simp only [profile,Set.indicator,mem_Ioi]
    by_cases h1 : X<‖q‖
    · rw [if_pos h1,if_pos (hRX.trans_lt h1)]
      simp
    · rw [if_neg h1]
      by_cases h2 : R<‖q‖
      · rw [if_pos h2]
        have : 0 ≤ (‖q‖^3)⁻¹ := by positivity
        linarith
      · rw [if_neg h2]
        simp
  have hgA (q : Plane) (h1 : R<‖q‖) (h2 : ‖q‖ ≤ X) : g q=C/‖q‖^3 := by
    simp only [g,profile,Set.indicator,mem_Ioi,if_pos h1,if_neg (not_lt.mpr h2)]
    ring
  have hbA : ∀ᵐ q : Plane ∂(volume.restrict (annSection R X)), ‖‖F q‖‖ ≤ g q := by
    apply ae_restrict_of_forall_mem (section_measurable R X)
    intro q hq
    rw [norm_norm,hgA q hq.1 hq.2]
    exact hb q hq.1 hq.2
  have hint : IntegrableOn (fun q => ‖F q‖) (annSection R X) :=
    Integrable.mono' hgi.integrableOn hF.norm hbA
  refine ⟨hint,?_⟩
  have h1 : (∫ q in annSection R X, ‖F q‖) ≤ ∫ q in annSection R X, g q := by
    apply setIntegral_mono_on hint hgi.integrableOn (section_measurable R X)
    intro q hq
    rw [hgA q hq.1 hq.2]
    exact hb q hq.1 hq.2
  have h2 : (∫ q in annSection R X, g q) ≤ ∫ q, g q :=
    setIntegral_le_integral hgi (Eventually.of_forall hg0)
  have h3 : (∫ q, g q)=C*(diskConstant/R-diskConstant/X) := by
    simp only [g]
    rw [integral_const_mul,integral_sub (inverse_cube_integrable R hR) (inverse_cube_integrable X hX),
      inverse_cube_integral R hR,inverse_cube_integral X hX]
  have h4 : C*(diskConstant/R-diskConstant/X) ≤ C*diskConstant*(X-R)/R^2 := by
    have hd := diskConstant_nonneg
    have e : C*(diskConstant/R-diskConstant/X)=C*diskConstant*(X-R)/(R*X) := by
      field_simp
      ring
    rw [e]
    apply div_le_div_of_nonneg_left (by have := sub_nonneg.mpr hRX; positivity) (by positivity)
    nlinarith
  exact (h1.trans h2).trans (h3.le.trans h4)

theorem inverseSigma_measurable (d : Data) : Measurable (SourceRadialSystem.inverseSigma d) := by
  have hf : Measurable (ClippedLayerProfiles.inverseSigma d.gs) :=
    ClippedLayerProfiles.select_measurable d.gs _ _ (fun g => measurable_const) measurable_const
  unfold SourceRadialSystem.inverseSigma SourceRadialSystem.extend
  show Measurable fun r : ℝ => if r ≤ d.R then (1 : ℂ) else if r ≤ d.X then ClippedLayerProfiles.inverseSigma d.gs r else 1
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_id measurable_const) hf measurable_const)

theorem electric_aesm (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    AEStronglyMeasurable (fun q : Plane => SourceUnclippedMaxwell.electric d P (MaxwellPlaneTail.planePoint q))
      (volume.restrict (annSection d.R d.X)) := by
  have hAm := section_measurable d.R d.X
  have hnorm : Continuous (fun q : Plane => ‖MaxwellPlaneTail.planePoint q‖) :=
    continuous_norm.comp MaxwellPlaneTail.planePoint_continuous
  have hnm : Measurable (fun q : Plane => ((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hnorm.measurable
  have hraw : ContinuousOn (fun q : Plane => raw d ‖MaxwellPlaneTail.planePoint q‖) (annSection d.R d.X) := by
    apply (RadialGluing.sourceState_continuousOn d.l d.chain d.hR).comp hnorm.continuousOn
    intro q hq
    show 0<‖MaxwellPlaneTail.planePoint q‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact d.hR.trans hq.1
  have h1 : AEStronglyMeasurable (fun q : Plane => (raw d ‖MaxwellPlaneTail.planePoint q‖).1)
      (volume.restrict (annSection d.R d.X)) := (continuous_fst.comp_continuousOn hraw).aestronglyMeasurable hAm
  have h2 : AEStronglyMeasurable (fun q : Plane => (raw d ‖MaxwellPlaneTail.planePoint q‖).2)
      (volume.restrict (annSection d.R d.X)) := (continuous_snd.comp_continuousOn hraw).aestronglyMeasurable hAm
  have hinv : Measurable (fun q : Plane => inverseSigma d ‖MaxwellPlaneTail.planePoint q‖) :=
    (inverseSigma_measurable d).comp hnorm.measurable
  have hpw (k : ℕ) : Measurable (fun q : Plane => (((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)^k)⁻¹) :=
    (hnm.pow_const k).inv
  have hpol : Continuous (fun q : Plane => HarmonicRadiationFactors.poloidal P (MaxwellPlaneTail.planePoint q)) :=
    (HarmonicRadiationFactors.poloidal_continuous P).comp MaxwellPlaneTail.planePoint_continuous
  have hrad : Continuous (fun q : Plane => HarmonicRadiationFactors.radial P (MaxwellPlaneTail.planePoint q)) :=
    (HarmonicRadiationFactors.radial_continuous P).comp MaxwellPlaneTail.planePoint_continuous
  have hg : AEStronglyMeasurable (fun q : Plane =>
      ((raw d ‖MaxwellPlaneTail.planePoint q‖).2*(((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)^(d.l+2))⁻¹) •
        HarmonicRadiationFactors.poloidal P (MaxwellPlaneTail.planePoint q)+
      (inverseSigma d ‖MaxwellPlaneTail.planePoint q‖*(((d.l : ℂ)*(d.l+1))*(raw d ‖MaxwellPlaneTail.planePoint q‖).1*
        (((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)^(d.l+3))⁻¹)) •
        HarmonicRadiationFactors.radial P (MaxwellPlaneTail.planePoint q))
      (volume.restrict (annSection d.R d.X)) :=
    ((h2.mul (hpw (d.l+2)).aestronglyMeasurable).smul hpol.aestronglyMeasurable).add
      ((hinv.aestronglyMeasurable.mul ((aestronglyMeasurable_const.mul h1).mul
        (hpw (d.l+3)).aestronglyMeasurable)).smul hrad.aestronglyMeasurable)
  apply hg.congr
  apply ae_restrict_of_forall_mem hAm
  intro q hq
  have hx0 : MaxwellPlaneTail.planePoint q≠0 := by
    apply norm_pos_iff.mp
    rw [MaxwellPlaneTail.planePoint_norm]
    exact d.hR.trans hq.1
  beta_reduce
  rw [SourceAnnulusStateBounds.electric_pol_rad d P hp _ hx0]
  simp only [div_eq_mul_inv,mul_assoc]

theorem magnetic_aesm (d : Data) (P : Poly) :
    AEStronglyMeasurable (fun q : Plane => SourceUnclippedMaxwell.magnetic d P (MaxwellPlaneTail.planePoint q))
      (volume.restrict (annSection d.R d.X)) := by
  have hAm := section_measurable d.R d.X
  have hnorm : Continuous (fun q : Plane => ‖MaxwellPlaneTail.planePoint q‖) :=
    continuous_norm.comp MaxwellPlaneTail.planePoint_continuous
  have hnm : Measurable (fun q : Plane => ((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp hnorm.measurable
  have hraw : ContinuousOn (fun q : Plane => raw d ‖MaxwellPlaneTail.planePoint q‖) (annSection d.R d.X) := by
    apply (RadialGluing.sourceState_continuousOn d.l d.chain d.hR).comp hnorm.continuousOn
    intro q hq
    show 0<‖MaxwellPlaneTail.planePoint q‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact d.hR.trans hq.1
  have h1 : AEStronglyMeasurable (fun q : Plane => (raw d ‖MaxwellPlaneTail.planePoint q‖).1)
      (volume.restrict (annSection d.R d.X)) := (continuous_fst.comp_continuousOn hraw).aestronglyMeasurable hAm
  have hpw (k : ℕ) : Measurable (fun q : Plane => (((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)^k)⁻¹) :=
    (hnm.pow_const k).inv
  have hT : Continuous (fun q : Plane => DebyeRadialTrace.angularToroidal P (MaxwellPlaneTail.planePoint q)) :=
    (HarmonicRadiationGeometry.angularToroidal_continuous P).comp MaxwellPlaneTail.planePoint_continuous
  have hg : AEStronglyMeasurable (fun q : Plane =>
      ((-I*(raw d ‖MaxwellPlaneTail.planePoint q‖).1)*(((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)^1)⁻¹) •
        ((((‖MaxwellPlaneTail.planePoint q‖ : ℝ) : ℂ)^d.l)⁻¹ •
          DebyeRadialTrace.angularToroidal P (MaxwellPlaneTail.planePoint q)))
      (volume.restrict (annSection d.R d.X)) :=
    (((aestronglyMeasurable_const.mul h1).mul (hpw 1).aestronglyMeasurable)).smul
      ((hpw d.l).aestronglyMeasurable.smul hT.aestronglyMeasurable)
  apply hg.congr
  apply ae_restrict_of_forall_mem hAm
  intro q hq
  have hx0 : MaxwellPlaneTail.planePoint q≠0 := by
    apply norm_pos_iff.mp
    rw [MaxwellPlaneTail.planePoint_norm]
    exact d.hR.trans hq.1
  beta_reduce
  rw [SourceAnnulusStateBounds.magnetic_tor d P _ hx0]
  simp only [div_eq_mul_inv,pow_one]

theorem modeElectric_aesm (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    AEStronglyMeasurable (fun q : Plane => modeElectric tm d P (MaxwellPlaneTail.planePoint q))
      (volume.restrict (annSection d.R d.X)) := by
  cases tm
  · simpa only [modeElectric,Bool.false_eq_true,if_false,SourceGeneralMaxwell.teElectric] using magnetic_aesm d P
  · simpa only [modeElectric,if_true] using electric_aesm d P hp

theorem modeMagnetic_aesm (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    AEStronglyMeasurable (fun q : Plane => modeMagnetic tm d P (MaxwellPlaneTail.planePoint q))
      (volume.restrict (annSection d.R d.X)) := by
  cases tm
  · have h := (electric_aesm d P hp).neg
    have : (fun q : Plane => modeMagnetic false d P (MaxwellPlaneTail.planePoint q))=
        fun q : Plane => -SourceUnclippedMaxwell.electric d P (MaxwellPlaneTail.planePoint q) := by
      funext q
      funext i
      simp [modeMagnetic,SourceGeneralMaxwell.teMagnetic]
    rw [this]
    exact h
  · simpa only [modeMagnetic,if_true] using magnetic_aesm d P

theorem band_annulus_flux_tendsto {ι κ : Type*} [Fintype ι] [Fintype κ] (q : ℝ) (hq : 0<q) (hq1 : 1≤q) (n : ℕ)
    (tmE : ι → Bool) (lE : ι → ℕ) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (lE i)) (cE : ι → ℂ)
    (tmH : κ → Bool) (lH : κ → ℕ) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (lH j)) (cH : κ → ℂ) :
    Tendsto (fun s : ℕ => ∫ u : Plane in annSection (SourcePairedGeometry.physicalData q hq n s).R
        (SourcePairedGeometry.physicalData q hq n s).X, ‖crossProduct
      (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i)
        (MaxwellPlaneTail.planePoint u))
      (conjugate (∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j }
        (PH j) (MaxwellPlaneTail.planePoint u))) 2‖) atTop (𝓝 0) := by
  obtain ⟨s1,C,hC,hb⟩ := SourceAnnulusStateBounds.band_annulus_flux_bound q hq hq1 n tmE lE PE hE cE tmH lH PH hH cH
  let W := RadialFiniteLimit.width (RadialPairedFamily.tm q hq n)
  have hup : Tendsto (fun s : ℕ => C*diskConstant*W/(RadialPhaseLimit.radius s)^2) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := C*diskConstant*W)).div_atTop
      ((tendsto_pow_atTop two_ne_zero).comp RadialPhaseLimit.radius_tendsto)
  apply squeeze_zero' (Eventually.of_forall (fun s => integral_nonneg (fun u => norm_nonneg _))) _ hup
  filter_upwards [eventually_ge_atTop s1] with s hs
  let R := (SourcePairedGeometry.physicalData q hq n s).R
  let X := (SourcePairedGeometry.physicalData q hq n s).X
  have hRpos : 0<R := (SourcePairedGeometry.physicalData q hq n s).hR
  have hXR : X-R=W := by
    show RadialPhaseLimit.radius s+W-RadialPhaseLimit.radius s=W
    ring
  have hRX : R ≤ X := by
    have : 0 ≤ W := RadialFiniteLimit.width_nonnegative _
    linarith
  have hEm : AEStronglyMeasurable (fun u : Plane =>
      ∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i)
        (MaxwellPlaneTail.planePoint u)) (volume.restrict (annSection R X)) := by
    have : ∀ i, AEStronglyMeasurable (fun u : Plane => cE i • modeElectric (tmE i)
        { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i) (MaxwellPlaneTail.planePoint u))
        (volume.restrict (annSection R X)) := fun i => (modeElectric_aesm (tmE i) _ (PE i) (hE i)).const_smul (cE i)
    exact Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => this i)
  have hHm : AEStronglyMeasurable (fun u : Plane =>
      ∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j)
        (MaxwellPlaneTail.planePoint u)) (volume.restrict (annSection R X)) := by
    have : ∀ j, AEStronglyMeasurable (fun u : Plane => cH j • modeMagnetic (tmH j)
        { SourcePairedGeometry.physicalData q hq n s with l := lH j } (PH j) (MaxwellPlaneTail.planePoint u))
        (volume.restrict (annSection R X)) := fun j => (modeMagnetic_aesm (tmH j) _ (PH j) (hH j)).const_smul (cH j)
    exact Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => this j)
  have hFm : AEStronglyMeasurable (fun u : Plane => crossProduct
      (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i)
        (MaxwellPlaneTail.planePoint u))
      (conjugate (∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j }
        (PH j) (MaxwellPlaneTail.planePoint u))) 2) (volume.restrict (annSection R X)) := by
    simp only [SourceRemotePlaneFlux.cross_two,conjugate]
    have hEi (i : Fin 3) := (continuous_apply i).comp_aestronglyMeasurable hEm
    have hHi (i : Fin 3) := Complex.continuous_conj.comp_aestronglyMeasurable
      ((continuous_apply i).comp_aestronglyMeasurable hHm)
    exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))
  have hb' : ∀ u : Plane, R<‖u‖ → ‖u‖ ≤ X → ‖crossProduct
      (∑ i, cE i • modeElectric (tmE i) { SourcePairedGeometry.physicalData q hq n s with l := lE i } (PE i)
        (MaxwellPlaneTail.planePoint u))
      (conjugate (∑ j, cH j • modeMagnetic (tmH j) { SourcePairedGeometry.physicalData q hq n s with l := lH j }
        (PH j) (MaxwellPlaneTail.planePoint u))) 2‖ ≤ C/‖u‖^3 := by
    intro u hu1 hu2
    have := hb s hs (MaxwellPlaneTail.planePoint u) (SourceRemotePlaneTail.planePoint_two u)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hu1)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hu2)
    rwa [MaxwellPlaneTail.planePoint_norm] at this
  have hres := (annulus_integral_le _ C R X hC hRpos hRX hFm hb').2
  rw [hXR] at hres
  exact hres

end OQ14.SourceAnnulusPlaneFlux
#print axioms OQ14.SourceAnnulusPlaneFlux.section_measurable
#print axioms OQ14.SourceAnnulusPlaneFlux.diskConstant_nonneg
#print axioms OQ14.SourceAnnulusPlaneFlux.annulus_integral_le
#print axioms OQ14.SourceAnnulusPlaneFlux.inverseSigma_measurable
#print axioms OQ14.SourceAnnulusPlaneFlux.electric_aesm
#print axioms OQ14.SourceAnnulusPlaneFlux.magnetic_aesm
#print axioms OQ14.SourceAnnulusPlaneFlux.modeElectric_aesm
#print axioms OQ14.SourceAnnulusPlaneFlux.modeMagnetic_aesm
#print axioms OQ14.SourceAnnulusPlaneFlux.band_annulus_flux_tendsto
