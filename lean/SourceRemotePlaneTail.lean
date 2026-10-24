import SourceRemotePlaneFluxTE
import MaxwellPlaneTail
import PlaneInverseCube

/-! Integrated plane tails: an inverse-cube pointwise bound gives a vanishing integrated absolute flux
outside a large disk, and the single-mode exterior flux density of the layered source (TM and TE) has
vanishing whole-plane tail. Single mode, exterior only. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRemotePlaneTail
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.ModalAlgebra OQ14.PlaneInverseCube OQ14.SourceRadiation
open scoped Topology

theorem tail_integral_small (F : Plane → ℂ) (C r0 : ℝ)
    (hF : AEStronglyMeasurable F (volume.restrict {q : Plane | r0<‖q‖}))
    (hb : ∀ q : Plane, r0<‖q‖ → ‖F q‖ ≤ C/‖q‖^3) :
    (∀ R : ℝ, 2*max r0 1 ≤ R → IntegrableOn (fun q => ‖F q‖) {q : Plane | R ≤ ‖q‖}) ∧
    Tendsto (fun R : ℝ => ∫ q : Plane in {q : Plane | R ≤ ‖q‖}, ‖F q‖) atTop (𝓝 0) := by
  have hT0 : 0<max r0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have key (R : ℝ) (hR : 2*max r0 1 ≤ R) :
      IntegrableOn F {q : Plane | R/2<‖q‖} ∧
        (∫ q : Plane in {q : Plane | R/2<‖q‖}, ‖F q‖) ≤ C*diskConstant/(R/2) := by
    have hTR : max r0 1 ≤ R/2 := by linarith
    have hT : 0<R/2 := lt_of_lt_of_le hT0 hTR
    have hsub : {q : Plane | R/2<‖q‖} ⊆ {q : Plane | r0<‖q‖} := by
      intro q hq
      exact lt_of_le_of_lt ((le_max_left _ _).trans hTR) hq
    have hF' := hF.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hb' : ∀ q : Plane, R/2<‖q‖ → ‖F q‖ ≤ C/‖q‖^3 :=
      fun q hq => hb q (lt_of_le_of_lt ((le_max_left _ _).trans hTR) hq)
    exact ⟨tail_integrable (R/2) C hT hF' hb',tail_integral_bound (R/2) C hT hF' hb'⟩
  have hsubset (R : ℝ) (hR : 2*max r0 1 ≤ R) : {q : Plane | R ≤ ‖q‖} ⊆ {q : Plane | R/2<‖q‖} := by
    have hRp : 0<R := lt_of_lt_of_le (mul_pos two_pos hT0) hR
    intro q hq
    exact lt_of_lt_of_le (show R/2<R by linarith) hq
  refine ⟨?_,?_⟩
  · intro R hR
    exact ((key R hR).1.mono_set (hsubset R hR)).norm
  · have hup : Tendsto (fun R : ℝ => C*diskConstant/(R/2)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := C*diskConstant)).div_atTop (tendsto_id.atTop_div_const (two_pos))
      simpa using this
    apply squeeze_zero' (Eventually.of_forall (fun R => integral_nonneg (fun q => norm_nonneg _))) _ hup
    filter_upwards [eventually_ge_atTop (2*max r0 1)] with R hR
    refine (setIntegral_mono_set ((key R hR).1.norm) (Eventually.of_forall (fun q => norm_nonneg _))
      (Eventually.of_forall (hsubset R hR))).trans (key R hR).2

theorem electric_continuousOn (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ContinuousOn (SourceUnclippedMaxwell.electric d P) {x : Space | d.X<‖x‖} := by
  intro x hx
  have hx' : d.X<‖x‖ := hx
  have hrpos : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx'
  have hz0 : ((‖x‖ : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hn : ContinuousAt (fun y : Space => ((‖y‖ : ℝ) : ℂ)) x :=
    (Complex.continuous_ofReal.comp continuous_norm).continuousAt
  have hP : ContinuousAt (fun y : Space => p d.l ((‖y‖ : ℝ) : ℂ)) x :=
    ContinuousAt.comp (g := ModalAlgebra.hankelPoly d.l I) (f := fun y : Space => ((‖y‖ : ℝ) : ℂ)) (x := x)
      (ModalAlgebra.hankelPoly_hasDerivAt d.l I _ hz0).continuousAt hn
  have hPD : ContinuousAt (fun y : Space => pD d.l ((‖y‖ : ℝ) : ℂ)) x :=
    ContinuousAt.comp (g := ModalAlgebra.hankelPolyD d.l I) (f := fun y : Space => ((‖y‖ : ℝ) : ℂ)) (x := x)
      (ModalAlgebra.hankelPolyD_hasDerivAt d.l I _ hz0).continuousAt hn
  have hc1 : ContinuousAt (fun y : Space => Complex.exp (I*((‖y‖ : ℝ) : ℂ))*((‖y‖ : ℝ) : ℂ)⁻¹) x :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_norm))).continuousAt.mul
      (hn.inv₀ hz0)
  have hs1 : ContinuousAt (fun y : Space => (((‖y‖ : ℝ) : ℂ)^(d.l+1))⁻¹) x :=
    (hn.pow _).inv₀ (pow_ne_zero _ hz0)
  have hA : ContinuousAt (fun y : Space => amplitude d*phase d.l*(I*p d.l ((‖y‖ : ℝ) : ℂ)+pD d.l ((‖y‖ : ℝ) : ℂ))) x :=
    continuousAt_const.mul ((continuousAt_const.mul hP).add hPD)
  have hB : ContinuousAt (fun y : Space => amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*
      (p d.l ((‖y‖ : ℝ) : ℂ)/((‖y‖ : ℝ) : ℂ))) x :=
    continuousAt_const.mul (hP.div hn hz0)
  have hpol := (HarmonicRadiationFactors.poloidal_continuous P).continuousAt (x := x)
  have hrad := (HarmonicRadiationFactors.radial_continuous P).continuousAt (x := x)
  have hF : ContinuousAt (fun y : Space => (Complex.exp (I*((‖y‖ : ℝ) : ℂ))*((‖y‖ : ℝ) : ℂ)⁻¹) •
      ((amplitude d*phase d.l*(I*p d.l ((‖y‖ : ℝ) : ℂ)+pD d.l ((‖y‖ : ℝ) : ℂ))) •
        ((((‖y‖ : ℝ) : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.poloidal P y)+
      (amplitude d*phase d.l*((d.l : ℂ)*(d.l+1))*(p d.l ((‖y‖ : ℝ) : ℂ)/((‖y‖ : ℝ) : ℂ))) •
        ((((‖y‖ : ℝ) : ℂ)^(d.l+1))⁻¹ • HarmonicRadiationFactors.radial P y))) x :=
    hc1.smul ((hA.smul (hs1.smul hpol)).add (hB.smul (hs1.smul hrad)))
  apply (hF.congr_of_eventuallyEq _).continuousWithinAt
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx'] with y hy
  have hy' : d.X<‖y‖ := hy
  have hr : 0<‖y‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hy'
  have hr0 : ((‖y‖ : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hun : Complex.exp (I*(‖y‖ : ℂ))*(‖y‖ : ℂ)⁻¹*(Complex.exp (-I*(‖y‖ : ℂ))*(‖y‖ : ℂ))=1 := by
    have he : Complex.exp (I*(‖y‖ : ℂ))*Complex.exp (-I*(‖y‖ : ℂ))=1 := by
      rw [← Complex.exp_add]; simp
    calc _ = (Complex.exp (I*(‖y‖ : ℂ))*Complex.exp (-I*(‖y‖ : ℂ)))*((‖y‖ : ℂ)⁻¹*(‖y‖ : ℂ)) := by ring
      _ = 1 := by rw [he,inv_mul_cancel₀ hr0,one_mul]
  have hE : SourceUnclippedMaxwell.electric d P y=
      (Complex.exp (I*(‖y‖ : ℂ))*(‖y‖ : ℂ)⁻¹) • SourceFarAmplitude.electricWeighted d P y := by
    unfold SourceFarAmplitude.electricWeighted
    rw [smul_smul,hun,one_smul]
  rw [hE,SourceFarAmplitude.electric_exterior d P hp y hy']

theorem magnetic_continuousOn (d : Data) (P : Poly) :
    ContinuousOn (SourceUnclippedMaxwell.magnetic d P) {x : Space | d.X<‖x‖} := by
  intro x hx
  have hx' : d.X<‖x‖ := hx
  have hrpos : 0<‖x‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx'
  have hz0 : ((‖x‖ : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hrpos.ne'
  have hn : ContinuousAt (fun y : Space => ((‖y‖ : ℝ) : ℂ)) x :=
    (Complex.continuous_ofReal.comp continuous_norm).continuousAt
  have hP : ContinuousAt (fun y : Space => p d.l ((‖y‖ : ℝ) : ℂ)) x :=
    ContinuousAt.comp (g := ModalAlgebra.hankelPoly d.l I) (f := fun y : Space => ((‖y‖ : ℝ) : ℂ)) (x := x)
      (ModalAlgebra.hankelPoly_hasDerivAt d.l I _ hz0).continuousAt hn
  have hs2 : ContinuousAt (fun y : Space => (((‖y‖ : ℝ) : ℂ)^d.l)⁻¹) x :=
    (hn.pow _).inv₀ (pow_ne_zero _ hz0)
  have hT := (HarmonicRadiationGeometry.angularToroidal_continuous P).continuousAt (x := x)
  have hc1 : ContinuousAt (fun y : Space => Complex.exp (I*((‖y‖ : ℝ) : ℂ))*((‖y‖ : ℝ) : ℂ)⁻¹) x :=
    (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_norm))).continuousAt.mul
      (hn.inv₀ hz0)
  have hF : ContinuousAt (fun y : Space => (Complex.exp (I*((‖y‖ : ℝ) : ℂ))*((‖y‖ : ℝ) : ℂ)⁻¹) •
      ((-I*amplitude d*phase d.l*p d.l ((‖y‖ : ℝ) : ℂ)) •
      ((((‖y‖ : ℝ) : ℂ)^d.l)⁻¹ • DebyeRadialTrace.angularToroidal P y))) x :=
    hc1.smul ((continuousAt_const.mul hP).smul (hs2.smul hT))
  apply (hF.congr_of_eventuallyEq _).continuousWithinAt
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx'] with y hy
  have hy' : d.X<‖y‖ := hy
  have hr : 0<‖y‖ := (d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hy'
  have hr0 : ((‖y‖ : ℝ) : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hun : Complex.exp (I*(‖y‖ : ℂ))*(‖y‖ : ℂ)⁻¹*(Complex.exp (-I*(‖y‖ : ℂ))*(‖y‖ : ℂ))=1 := by
    have he : Complex.exp (I*(‖y‖ : ℂ))*Complex.exp (-I*(‖y‖ : ℂ))=1 := by
      rw [← Complex.exp_add]; simp
    calc _ = (Complex.exp (I*(‖y‖ : ℂ))*Complex.exp (-I*(‖y‖ : ℂ)))*((‖y‖ : ℂ)⁻¹*(‖y‖ : ℂ)) := by ring
      _ = 1 := by rw [he,inv_mul_cancel₀ hr0,one_mul]
  have hH : SourceUnclippedMaxwell.magnetic d P y=
      (Complex.exp (I*(‖y‖ : ℂ))*(‖y‖ : ℂ)⁻¹) • SourceFarAmplitude.magneticWeighted d P y := by
    unfold SourceFarAmplitude.magneticWeighted
    rw [smul_smul,hun,one_smul]
  rw [hH,SourceFarAmplitude.magnetic_exterior d P y hy']

theorem planePoint_two (q : Plane) : MaxwellPlaneTail.planePoint q 2=0 := by
  simp [MaxwellPlaneTail.planePoint]

theorem flux_continuousOn (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ContinuousOn (fun q : Plane => crossProduct
      (SourceUnclippedMaxwell.electric d P (MaxwellPlaneTail.planePoint q))
      (conjugate (SourceUnclippedMaxwell.magnetic d P (MaxwellPlaneTail.planePoint q))) 2)
      {q : Plane | d.X<‖q‖} := by
  have hmaps : MapsTo MaxwellPlaneTail.planePoint {q : Plane | d.X<‖q‖} {x : Space | d.X<‖x‖} := by
    intro q hq
    change d.X<‖MaxwellPlaneTail.planePoint q‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hq
  have hE := (electric_continuousOn d P hp).comp MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps
  have hH := (magnetic_continuousOn d P).comp MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps
  have hEi (i : Fin 3) : ContinuousOn (fun q : Plane =>
      SourceUnclippedMaxwell.electric d P (MaxwellPlaneTail.planePoint q) i) {q : Plane | d.X<‖q‖} :=
    continuousOn_pi.mp hE i
  have hHi (i : Fin 3) : ContinuousOn (fun q : Plane =>
      (starRingEnd ℂ) (SourceUnclippedMaxwell.magnetic d P (MaxwellPlaneTail.planePoint q) i)) {q : Plane | d.X<‖q‖} :=
    Complex.continuous_conj.comp_continuousOn (continuousOn_pi.mp hH i)
  simp only [SourceRemotePlaneFlux.cross_two,conjugate]
  exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))

theorem single_mode_tail_TM (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    Tendsto (fun R : ℝ => ∫ q : Plane in {q : Plane | R ≤ ‖q‖}, ‖crossProduct
      (SourceUnclippedMaxwell.electric d P (MaxwellPlaneTail.planePoint q))
      (conjugate (SourceUnclippedMaxwell.magnetic d P (MaxwellPlaneTail.planePoint q))) 2‖) atTop (𝓝 0) := by
  obtain ⟨r0,C,hC,hb⟩ := SourceRemotePlaneFlux.plane_flux_bound d P hp
  have hcont := flux_continuousOn d P hp
  refine (tail_integral_small _ C (max (max r0 d.X) 1) ?_ ?_).2
  · apply ContinuousOn.aestronglyMeasurable _ (isOpen_lt continuous_const continuous_norm).measurableSet
    apply hcont.mono
    intro q hq
    change max (max r0 d.X) 1<‖q‖ at hq
    exact lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hq
  · intro q hq
    have h1 : r0<‖q‖ := lt_of_le_of_lt ((le_max_left _ _).trans ((le_max_left _ _).trans (le_refl _))) hq
    have h2 : d.X<‖q‖ := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hq
    have := hb (MaxwellPlaneTail.planePoint q) (planePoint_two q)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact h1.le)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact h2)
    rwa [MaxwellPlaneTail.planePoint_norm] at this

theorem single_mode_tail_TE (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    Tendsto (fun R : ℝ => ∫ q : Plane in {q : Plane | R ≤ ‖q‖}, ‖crossProduct
      (SourceGeneralMaxwell.teElectric d P (MaxwellPlaneTail.planePoint q))
      (conjugate (SourceGeneralMaxwell.teMagnetic d P (MaxwellPlaneTail.planePoint q))) 2‖) atTop (𝓝 0) := by
  have h := single_mode_tail_TM d P hp
  have hn (z : ℂ) : ‖(starRingEnd ℂ) z‖=‖z‖ := by simp
  simp only [SourceRemotePlaneFluxTE.te_flux_eq_conj,hn]
  exact h

end OQ14.SourceRemotePlaneTail
#print axioms OQ14.SourceRemotePlaneTail.tail_integral_small
#print axioms OQ14.SourceRemotePlaneTail.electric_continuousOn
#print axioms OQ14.SourceRemotePlaneTail.magnetic_continuousOn
#print axioms OQ14.SourceRemotePlaneTail.planePoint_two
#print axioms OQ14.SourceRemotePlaneTail.flux_continuousOn
#print axioms OQ14.SourceRemotePlaneTail.single_mode_tail_TM
#print axioms OQ14.SourceRemotePlaneTail.single_mode_tail_TE
