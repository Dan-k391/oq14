import BackgroundModeTE
import ChannelMaterialThroughput

/-! Identification of the material objects.  The paired-shell susceptibility `SourcePairedInclusion.shell`,
the TM coefficient `SourceMaterialCoefficient.coefficient` of the physical stack and the TE (permeability)
coefficient `SourceMuMaterial.coefficient` of its TE data have the same value function.  Every object of the
volume pipeline (square-root multiplier, volume block, actual solution, scattered and total fields, weighted
data) is built from the value function alone, so the background-mode responses of `BackgroundModeResponse`
and `BackgroundModeTE` transfer to the shell coefficient used by the closure theorem and the channel
assembly. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.BackgroundShellCoefficient
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.BackgroundModeMaxwell OQ14.BackgroundModeResponse
  OQ14.BackgroundModeTE OQ14.BackgroundCoreTransmission OQ14.SourceRadialSystem
open scoped Topology

abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2

/-! ### Congruence of the volume pipeline in the value function -/

theorem sqrtMultiplier_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) :
    StaticCoefficient.sqrtMultiplier c₁=StaticCoefficient.sqrtMultiplier c₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [StaticCoefficient.sqrtMultiplier_ae c₁ f,
    StaticCoefficient.sqrtMultiplier_ae c₂ f] with x h1 h2
  rw [h1,h2,h]

theorem volumeBlock_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) (k R : ℝ) :
    DynamicVolume.volumeBlock c₁ k R=DynamicVolume.volumeBlock c₂ k R := by
  unfold DynamicVolume.volumeBlock StaticNewton.volumeBlock StaticNewton.response
    DynamicVolume.weightedRemainder
  rw [sqrtMultiplier_congr_value h]

theorem solution_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) (k R : ℝ) (f : VectorL2) :
    MaterialField.solution c₁ k R f=MaterialField.solution c₂ k R f := by
  unfold MaterialField.solution
  rw [volumeBlock_congr_value h]

theorem source_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) (u : VectorL2) :
    DynamicVolume.source c₁ u=DynamicVolume.source c₂ u := by
  funext j y
  unfold DynamicVolume.source
  rw [h]

theorem scattered_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) (k : ℝ) (u : VectorL2) :
    MaterialField.scattered c₁ k u=MaterialField.scattered c₂ k u := by
  unfold MaterialField.scattered
  rw [sqrtMultiplier_congr_value h,source_congr_value h]

theorem total_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) (k : ℝ) (u : VectorL2)
    (incident : Field) : MaterialField.total c₁ k u incident=MaterialField.total c₂ k u incident := by
  unfold MaterialField.total
  rw [scattered_congr_value h]

/-- The weighted incident datum depends on the coefficient through its value function only. -/
theorem incident_datum_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value) (R : ℝ) (incident : Field)
    (hc₁ : ∀ x : Space,x∉closedBall 0 R → c₁.value (VectorFourier.coordinateMap x)=0)
    (hc₂ : ∀ x : Space,x∉closedBall 0 R → c₂.value (VectorFourier.coordinateMap x)=0)
    (hm : ∀ i,MemLp (fun x => incident x i) 2 (volume.restrict (closedBall 0 R))) :
    IncidentLocalization.datum c₁ R incident hc₁ hm=IncidentLocalization.datum c₂ R incident hc₂ hm := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  filter_upwards [IncidentLocalization.datum_actual c₁ R incident hc₁ hm i,
    IncidentLocalization.datum_actual c₂ R incident hc₂ hm i] with x h1 h2
  rw [h1,h2]
  simp only [IncidentLocalization.weighted,h]

/-- The restricted-TE datum depends on the coefficient through its value function only (the support data enter
through proofs). -/
theorem datum_congr_value {c₁ c₂ : Coefficient} (h : c₁.value=c₂.value)
    (d₁ : BoundedMaterialKernel.SupportData c₁) (d₂ : BoundedMaterialKernel.SupportData c₂)
    (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    RestrictedTEMaterial.datum c₁ d₁ A=RestrictedTEMaterial.datum c₂ d₂ A := by
  apply RestrictedTEDatumLinear.physical_ext
  intro i
  filter_upwards [RestrictedTEMaterial.datum_actual c₁ d₁ A i,
    RestrictedTEMaterial.datum_actual c₂ d₂ A i] with x h1 h2
  rw [h1,h2,h]

/-! ### The value functions agree -/

theorem tm_coefficient_value (q : ℝ) (hq : 1≤q) (n r l : ℕ) :
    (SourceMaterialCoefficient.coefficient (physicalTM q (zero_lt_one.trans_le hq) n r l) (q^2)
      (one_le_sq' q hq) (SourcePairedGeometry.physical_material_bounds q (zero_lt_one.trans_le hq) hq n r)).value=
      (SourcePairedInclusion.shell q hq n r).value := rfl

theorem realSigma_te_dual (q : ℝ) (hq : 0<q) (n s : ℕ) (t : ℝ) :
    SourceMaterialCoefficient.realSigma (SourceMuMaterial.dualData (physicalTE q hq n s)) t=
      SourceMaterialCoefficient.realSigma (SourcePairedGeometry.physicalData q hq n s) t := by
  have h1 := SourceMaterialCoefficient.sigma_eq (SourceMuMaterial.dualData (physicalTE q hq n s)) t
  have h2 := SourceMaterialCoefficient.sigma_eq (SourcePairedGeometry.physicalData q hq n s) t
  have h3 : sigma (SourceMuMaterial.dualData (physicalTE q hq n s)) t=
      sigma (SourcePairedGeometry.physicalData q hq n s) t := by
    rw [SourceMuMaterial.sigma_dual]
    exact SourceDielectricModes.te_mu _ (SourcePairedGeometry.physical_dispersion q hq n s) 0 t
  exact_mod_cast (h1.symm.trans (h3.trans h2))

theorem te_coefficient_value (q : ℝ) (hq : 1≤q) (n r : ℕ) :
    (SourceMuMaterial.coefficient (physicalTE q (zero_lt_one.trans_le hq) n r) (q^2) (one_le_sq' q hq)
      (physicalTE_parameters q (zero_lt_one.trans_le hq) hq n r)).value=
      (SourcePairedInclusion.shell q hq n r).value := by
  funext ξ
  change SourceMaterialCoefficient.realSigma (SourceMuMaterial.dualData (physicalTE q (zero_lt_one.trans_le hq) n r))
      ‖VectorFourier.coordinateMap.symm ξ‖-1=_
  rw [realSigma_te_dual]
  rfl

/-! ### Responses for the shell coefficient -/

/-- Support data of the shell coefficient at the enclosing radius (the object used in the channel assembly). -/
abbrev shellSupport (q : ℝ) (hq : 1≤q) (n r : ℕ) : BoundedMaterialKernel.SupportData
    (SourcePairedInclusion.shell q hq n r) :=
  ChannelMaterialThroughput.supportOfRadius _ (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.shell_support q hq n r)

theorem te_support_radius (q : ℝ) (hq : 1≤q) (n r : ℕ) :
    (shellSupport q hq n r).radius=(physicalTE q (zero_lt_one.trans_le hq) n r).X := rfl

/-- **TE response of the shell coefficient.**  The total field of the actual shell solution for the restricted-TE
datum of the finite coefficient vector `A` (support data `supportOfRadius` of the shell at radius
`(data q hq n r).X`), with incident field `RestrictedTEPlaneLocal.electric A`, is almost everywhere the TE background
field of the family of regular modes over the physical TE stack. -/
theorem shell_te_response (q : ℝ) (hq : 1≤q) (n r : ℕ) (A : SymmetricHarmonicJets.Index →₀ ℂ) :
    MaterialField.total (SourcePairedInclusion.shell q hq n r) 1
      (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
        (RestrictedTEMaterial.datum (SourcePairedInclusion.shell q hq n r) (shellSupport q hq n r) A))
      (RestrictedTEPlaneLocal.electric A)=ᵐ[volume]
      famBackground (physicalTE q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A) (fun q => q.val.1)
        RestrictedTEIncoming.polynomial := by
  have hv := te_coefficient_value q hq n r
  have hresp := physicalTE_response q (zero_lt_one.trans_le hq) hq n r A
  rw [← total_congr_value hv.symm,← solution_congr_value hv.symm,
    ← datum_congr_value hv.symm (shellSupport q hq n r)
      (teSupportData _ (physicalTE q (zero_lt_one.trans_le hq) n r).X (SourceTEWeightedDatum.material_outer _ _
        (SourceMuMaterial.value_complex (physicalTE q (zero_lt_one.trans_le hq) n r) (q^2) (one_le_sq' q hq)
          (physicalTE_parameters q (zero_lt_one.trans_le hq) hq n r))))] at hresp
  exact hresp

/-- The core field of the shell response (TE): the regular TE field of `A` rescaled degreewise by the physical TE
transmission over two. -/
theorem shell_te_core (q : ℝ) (hq : 1≤q) (n r : ℕ) (A : SymmetricHarmonicJets.Index →₀ ℂ) (x : Space)
    (hx : x≠0) (hR : ‖x‖≤RadialPhaseLimit.radius r) :
    famBackground (physicalTE q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A) (fun q => q.val.1)
        RestrictedTEIncoming.polynomial x=
      RestrictedTEPlaneLocal.electric (scaledCoeff A (fun l => stackTransmission l
        (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n) (RadialPhaseLimit.radius r)
        (RadialPhaseLimit.radius_pos r)/2)) x := by
  rw [te_finite_core (physicalTE q (zero_lt_one.trans_le hq) n r) A x hx hR]
  have e : (fun l : ℕ => transmission l (physicalTE q (zero_lt_one.trans_le hq) n r).gs
      (physicalTE q (zero_lt_one.trans_le hq) n r).R (physicalTE q (zero_lt_one.trans_le hq) n r).X
      (physicalTE q (zero_lt_one.trans_le hq) n r).hR/2)=
      fun l => stackTransmission l (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n)
        (RadialPhaseLimit.radius r) (RadialPhaseLimit.radius_pos r)/2 := by
    funext l
    rw [physicalTE_transmission]
  rw [e]

/-- The limit of the core field as the shell index tends to infinity. -/
theorem shell_te_core_tendsto (q : ℝ) (hq : 1≤q) (n : ℕ) (A : SymmetricHarmonicJets.Index →₀ ℂ)
    (x : Space) (hx : x≠0) :
    Tendsto (fun r : ℕ => famBackground (physicalTE q (zero_lt_one.trans_le hq) n r) A.support (teCoeff A)
        (fun q => q.val.1) RestrictedTEIncoming.polynomial x) atTop
      (𝓝 (RestrictedTEPlaneLocal.electric
        (scaledCoeff A (fun l => limitingTransmission l (RadialPairedFamily.te q (zero_lt_one.trans_le hq) n)/2)) x)) :=
  physicalTE_core_tendsto q (zero_lt_one.trans_le hq) n A x hx

/-- **TM response of the shell coefficient.** -/
theorem shell_tm_response (q : ℝ) (hq : 1≤q) (n r l : ℕ) (P : HarmonicPolynomial.Poly)
    (hp : P.IsHomogeneous l) (hh : HarmonicPolynomial.formalLaplacian P=0) :
    MaterialField.total (SourcePairedInclusion.shell q hq n r) 1
      (MaterialField.solution (SourcePairedInclusion.shell q hq n r) 1 (SourcePairedInclusion.data q hq n r).X
        (IncidentLocalization.datum (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (SolidMaxwellProfiles.electric l P)
          (SourcePairedInclusion.shell_support q hq n r)
          (fun i => SourceLocalBounds.continuous_memLp_ball _
            (SolidMaxwellProfiles.electric_smooth l P i).continuous _)))
      (SolidMaxwellProfiles.electric l P)=ᵐ[volume]
      backgroundElectric (physicalTM q (zero_lt_one.trans_le hq) n r l) P := by
  have hv := tm_coefficient_value q hq n r l
  have hresp := physicalTM_response q (zero_lt_one.trans_le hq) hq n r l P hp hh
  unfold incidentDatum at hresp
  rw [← total_congr_value hv.symm,← solution_congr_value hv.symm,
    ← incident_datum_congr_value hv.symm (physicalTM q (zero_lt_one.trans_le hq) n r l).X _
      (fun x hx => SourcePairedInclusion.shell_support q hq n r x hx) _ _] at hresp
  exact hresp

end OQ14.BackgroundShellCoefficient
#print axioms OQ14.BackgroundShellCoefficient.sqrtMultiplier_congr_value
#print axioms OQ14.BackgroundShellCoefficient.volumeBlock_congr_value
#print axioms OQ14.BackgroundShellCoefficient.solution_congr_value
#print axioms OQ14.BackgroundShellCoefficient.source_congr_value
#print axioms OQ14.BackgroundShellCoefficient.scattered_congr_value
#print axioms OQ14.BackgroundShellCoefficient.total_congr_value
#print axioms OQ14.BackgroundShellCoefficient.incident_datum_congr_value
#print axioms OQ14.BackgroundShellCoefficient.datum_congr_value
#print axioms OQ14.BackgroundShellCoefficient.tm_coefficient_value
#print axioms OQ14.BackgroundShellCoefficient.realSigma_te_dual
#print axioms OQ14.BackgroundShellCoefficient.te_coefficient_value
#print axioms OQ14.BackgroundShellCoefficient.te_support_radius
#print axioms OQ14.BackgroundShellCoefficient.shell_te_response
#print axioms OQ14.BackgroundShellCoefficient.shell_te_core
#print axioms OQ14.BackgroundShellCoefficient.shell_te_core_tendsto
#print axioms OQ14.BackgroundShellCoefficient.shell_tm_response
