import SourcePairedPlaneMagnetic

/-! The physical identification of the assembled plane fields of the finite paired shells with the total
fields of the combined shell-plus-inclusion material solution: the shell sandwich of an inclusion source
is the Bochner superposition of the free dipole data, the shell reaction fields are the electric and
magnetic fields of the shell polarization of the induced shell solution, the combined solution splits
into the shell response to the shell datum and the effective inclusion solution of the effective datum,
and the total fields of the combined solution are the assembled plane fields; with the compact
convergence theorems this gives uniform convergence of the combined total fields to the parity device
fields under convergent effective data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourcePairedPlaneIdentification
open MeasureTheory Set Metric Filter OQ14.Maxwell
open OQ14.SourcePairedPlaneMagnetic
open scoped Topology InnerProductSpace
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

/-! ### Additivity of the weighted source and the generic bounded response functional -/

theorem source_add_ae (c : Coefficient) (u v : VectorL2) (j : Fin 3) :
    DynamicVolume.source c (u + v) j =ᵐ[volume]
      fun y => DynamicVolume.source c u j y + DynamicVolume.source c v j y := by
  filter_upwards [VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_add u v)]
    with y hy
  have hadd : ∀ a b : VectorFourier.Vector, (a + b) j = a j + b j := fun a b => rfl
  simp only [DynamicVolume.source]
  rw [hy]
  simp only [Pi.add_apply]
  rw [hadd]
  ring

theorem source_smul_ae (c : Coefficient) (z : ℂ) (u : VectorL2) (j : Fin 3) :
    DynamicVolume.source c (z • u) j =ᵐ[volume] fun y => z * DynamicVolume.source c u j y := by
  filter_upwards [VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae (Lp.coeFn_smul z u)]
    with y hy
  have hs : ∀ a : VectorFourier.Vector, (z • a) j = z * a j := fun a => rfl
  simp only [DynamicVolume.source]
  rw [hy]
  simp only [Pi.smul_apply]
  rw [hs]
  ring

section Functional
variable (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (K : Space → ℂ) (hK : Measurable K)
  (x : Space) (B : ℝ) (hB : ∀ y ∈ d.carrier, ‖K (x - y)‖ ≤ B)
include d hK hB

theorem response_integrand_integrable (w : VectorL2) (j : Fin 3) :
    Integrable (fun y => DynamicVolume.source c w j y * K (x - y)) :=
  ScalarRadiation.source_integrand_integrable K _ hK
    (DynamicVolume.source_integrable c w d.radius d.ballZero j) x B
    (fun y hy => hB y (SourcePairedPlaneCompact.source_mem_carrier c d w j y hy))

/-- The bounded linear functional `w ↦ ∫ y, source c w j y * K (x - y)` for a measurable kernel that is
bounded on the carrier. -/
def kernelFunctional (hB0 : 0 ≤ B) (j : Fin 3) : VectorL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun w => KernelConvolution.response K (DynamicVolume.source c w j) x
      map_add' := fun u v => by
        unfold KernelConvolution.response
        rw [← integral_add (response_integrand_integrable c d K hK x B hB u j)
          (response_integrand_integrable c d K hK x B hB v j)]
        apply integral_congr_ae
        filter_upwards [source_add_ae c u v j] with y hy
        rw [hy]
        ring
      map_smul' := fun z u => by
        unfold KernelConvolution.response
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [source_smul_ae c z u j] with y hy
        rw [hy]
        ring }
    (B * (Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)))
    (fun w => by
      have h1 := ScalarRadiation.response_norm_bound K _ hK
        (DynamicVolume.source_integrable c w d.radius d.ballZero j) x B
        (fun y hy => hB y (SourcePairedPlaneCompact.source_mem_carrier c d w j y hy))
      have h2 := SourcePairedReactionField.source_mass' c d w j
      calc ‖KernelConvolution.response K (DynamicVolume.source c w j) x‖
          ≤ B * ∫ y, ‖DynamicVolume.source c w j y‖ := h1
        _ ≤ B * ((Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)) * ‖w‖) :=
          mul_le_mul_of_nonneg_left h2 hB0
        _ = B * (Real.sqrt c.bound * Real.sqrt (volume.real d.carrier)) * ‖w‖ := by ring)

theorem kernelFunctional_apply (hB0 : 0 ≤ B) (j : Fin 3) (w : VectorL2) :
    kernelFunctional c d K hK x B hB hB0 j w =
      KernelConvolution.response K (DynamicVolume.source c w j) x := rfl

end Functional

/-! ### The magnetic evaluation functional in the source-free core -/

theorem magneticDyadic_bound (z : Space) (d' : ℝ) (hd : 0 < d') (hz : d' / 2 ≤ ‖z‖) (i j : Fin 3) :
    ‖SphereMagneticKernel.magneticDyadic 1 z i j‖ ≤ 2 * NewtonStripMaxwell.gradientBound 1 d' := by
  unfold SphereMagneticKernel.magneticDyadic
  have g1 := NewtonStripMaxwell.gradient_bound 1 d' hd z hz (WeakCurl.next i)
  have g2 := NewtonStripMaxwell.gradient_bound 1 d' hd z hz (WeakCurl.previous i)
  have hI : ‖-(Complex.I * ((1 : ℝ) : ℂ))‖ = 1 := by simp
  have e1 : ‖(if WeakCurl.previous i = j then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  have e2 : ‖(if WeakCurl.next i = j then (1 : ℂ) else 0)‖ ≤ 1 := by split_ifs <;> simp
  rw [norm_mul, hI, one_mul]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have n1 := mul_le_mul g1 e1 (norm_nonneg _) (by linarith [norm_nonneg (GreenKernel.phiGradient 1 z (WeakCurl.next i))])
  have n2 := mul_le_mul g2 e2 (norm_nonneg _) (by linarith [norm_nonneg (GreenKernel.phiGradient 1 z (WeakCurl.previous i))])
  linarith

theorem measurable_magneticDyadic (i j : Fin 3) :
    Measurable (fun z : Space => SphereMagneticKernel.magneticDyadic 1 z i j) := by
  unfold SphereMagneticKernel.magneticDyadic
  exact measurable_const.mul (((KernelGradient.gradient_measurable 1 (WeakCurl.next i)).mul measurable_const).sub
    ((KernelGradient.gradient_measurable 1 (WeakCurl.previous i)).mul measurable_const))

/-- The bounded functional `w ↦ MagneticResponse.magnetic 1 (source cs w) x i` on the weighted vectors,
for `x` at positive distance from the support. -/
def magneticEvaluation (cs : Coefficient) (d : BoundedMaterialKernel.SupportData cs) (x : Space) (B : ℝ)
    (hB0 : 0 ≤ B) (hB : ∀ y ∈ d.carrier, ∀ i j : Fin 3, ‖SphereMagneticKernel.magneticDyadic 1 (x - y) i j‖ ≤ B)
    (i : Fin 3) : VectorL2 →L[ℂ] ℂ :=
  ∑ j : Fin 3, kernelFunctional cs d (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
    (measurable_magneticDyadic i j) x B (fun y hy => hB y hy i j) hB0 j

theorem magneticEvaluation_apply (cs : Coefficient) (d : BoundedMaterialKernel.SupportData cs) (x : Space)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ y ∈ d.carrier, ∀ i j : Fin 3, ‖SphereMagneticKernel.magneticDyadic 1 (x - y) i j‖ ≤ B)
    (i : Fin 3) (w : VectorL2) :
    magneticEvaluation cs d x B hB0 hB i w = MagneticResponse.magnetic 1 (DynamicVolume.source cs w) x i := by
  rw [magnetic_eq_sum]
  simp only [magneticEvaluation, ContinuousLinearMap.sum_apply, kernelFunctional_apply]
  rfl

/-! ### The shell reaction fields are the fields of the shell polarization of the induced solution -/

/-- The shell reaction field of an inclusion vector is the literal electric field of the shell polarization
of the shell solution driven by the sandwich `Ss T Si v`, at every point of the core. -/
theorem reactionField_eq_free (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (x : Space) (hx : ‖x‖ < Rin) (i : Fin 3) :
    SourcePairedReactionField.reactionField cs ci R Rin X v x i =
      ExteriorContinuity.electric 1 (DynamicVolume.source cs
        (Ring.inverse (DynamicVolume.volumeBlock cs 1 R)
          (StaticCoefficient.sqrtMultiplier cs
            (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci v))))) x i := by
  have hf := ShellReactionIdentification.weighted_kernel_functional cs ci b Rin X R hbR hRX hXR hcs hci v
    ((CoreMaterialEvaluation.evaluation cs Rin X hcs x hx i).comp
      (Ring.inverse (DynamicVolume.volumeBlock cs 1 R)))
  simp only [ContinuousLinearMap.comp_apply] at hf
  have h1 : (∑ j : Fin 3, ∫ y : Space, ShellReactionIdentification.reactionKernel cs R Rin X x y i j *
        DynamicVolume.source ci v j y) =
      ∑ j : Fin 3, ∫ y : Space, DynamicVolume.source ci v j y * CoreMaterialEvaluation.evaluation cs Rin X hcs x hx i
        (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) (ShellReactionIdentification.freeDatum cs Rin X y j)) := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards with y
    rw [ShellReactionIdentification.reactionKernel_eq_evaluation cs R Rin X hcs x y hx i j, mul_comm]
  unfold SourcePairedReactionField.reactionField
  rw [h1, ← hf, CoreMaterialEvaluation.evaluation_actual]
  rfl

/-- The magnetic dyadic is uniformly bounded on the annulus for an observation point in the core. -/
theorem magnetic_annulus_bound (cs : Coefficient) (Rin X : ℝ)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (x : Space) (hx : ‖x‖ < Rin) :
    ∀ y ∈ (CoreMaterialEvaluation.supportData cs Rin X hcs).carrier, ∀ i j : Fin 3,
      ‖SphereMagneticKernel.magneticDyadic 1 (x - y) i j‖ ≤
        2 * NewtonStripMaxwell.gradientBound 1 (2 * (Rin - ‖x‖)) := by
  have hδ : 0 < Rin - ‖x‖ := sub_pos.mpr hx
  intro y hy i j
  apply magneticDyadic_bound (x - y) _ (by linarith)
  have hyn : Rin ≤ ‖y‖ := by simpa only [mem_ball, dist_zero_right, not_lt] using hy.2
  have := norm_sub_norm_le y x
  rw [norm_sub_rev] at this
  linarith

theorem magnetic_annulus_bound_nonneg (Rin : ℝ) (x : Space) (hx : ‖x‖ < Rin) :
    0 ≤ 2 * NewtonStripMaxwell.gradientBound 1 (2 * (Rin - ‖x‖)) := by
  have hδ : 0 < Rin - ‖x‖ := sub_pos.mpr hx
  unfold NewtonStripMaxwell.gradientBound
  positivity

/-- The shell magnetic reaction field of an inclusion vector is the magnetic field of the same shell
polarization, at every point of the core. -/
theorem magneticReactionField_eq_free (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (x : Space) (hx : ‖x‖ < Rin) (i : Fin 3) :
    magneticReactionField cs ci R Rin X v x i =
      MagneticResponse.magnetic 1 (DynamicVolume.source cs
        (Ring.inverse (DynamicVolume.volumeBlock cs 1 R)
          (StaticCoefficient.sqrtMultiplier cs
            (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci v))))) x i := by
  have hB := magnetic_annulus_bound cs Rin X hcs x hx
  have hB0 := magnetic_annulus_bound_nonneg Rin x hx
  have hf := ShellReactionIdentification.weighted_kernel_functional cs ci b Rin X R hbR hRX hXR hcs hci v
    ((magneticEvaluation cs (CoreMaterialEvaluation.supportData cs Rin X hcs) x _ hB0 hB i).comp
      (Ring.inverse (DynamicVolume.volumeBlock cs 1 R)))
  simp only [ContinuousLinearMap.comp_apply] at hf
  have h1 : (∑ j : Fin 3, ∫ y : Space, magneticReactionKernel cs R Rin X x y i j *
        DynamicVolume.source ci v j y) =
      ∑ j : Fin 3, ∫ y : Space, DynamicVolume.source ci v j y *
        magneticEvaluation cs (CoreMaterialEvaluation.supportData cs Rin X hcs) x _ hB0 hB i
          (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) (ShellReactionIdentification.freeDatum cs Rin X y j)) := by
    apply Finset.sum_congr rfl
    intro j _
    apply integral_congr_ae
    filter_upwards with y
    rw [mul_comm, magneticEvaluation_apply]
    rw [← magneticReactionKernel_eq_magnetic]
  unfold magneticReactionField
  rw [h1, ← hf, magneticEvaluation_apply]


/-! ### The dipole superposition: the sandwich `Ss T Si` is the Bochner integral of the free data -/

/-- The free dipole datum of the shell depends continuously on the dipole position inside the core. -/
theorem freeDatum_continuousOn (cs : Coefficient) (b Rin X : ℝ) (hbR : b < Rin) (j : Fin 3) :
    ContinuousOn (fun y => ShellReactionIdentification.freeDatum cs Rin X y j) (closedBall (0 : Space) b) := by
  rw [continuousOn_iff_continuous_restrict]
  have hne (y : closedBall (0 : Space) b) (x : WeightedAnnulusDatum.annulus Rin X) :
      (x : Space) - (y : Space) ≠ 0 := by
    intro h0
    have h1 : (x : Space) = (y : Space) := sub_eq_zero.mp h0
    have hx : Rin ≤ ‖(x : Space)‖ := FreeDyadicMaterialData.annulus_inner Rin X x
    have hy : ‖(y : Space)‖ ≤ b := mem_closedBall_zero_iff.mp y.property
    rw [h1] at hx
    linarith
  let Φ : Fin 3 → C(closedBall (0 : Space) b × WeightedAnnulusDatum.annulus Rin X, ℂ) := fun i =>
    ⟨fun p => DyadicKernel.dyadic 1 ((p.2 : Space) - (p.1 : Space)) i j, by
      apply continuous_iff_continuousAt.mpr
      intro p
      have h := ExteriorContinuity.dyadic_continuousAt 1 i j ((p.2 : Space) - (p.1 : Space)) (hne p.1 p.2)
      exact h.comp (f := fun q : closedBall (0 : Space) b × WeightedAnnulusDatum.annulus Rin X =>
        (q.2 : Space) - (q.1 : Space))
        ((continuous_subtype_val.comp continuous_snd).sub
          (continuous_subtype_val.comp continuous_fst)).continuousAt⟩
  have hcont : Continuous (fun y : closedBall (0 : Space) b => ∑ i : Fin 3,
      DynamicConvolution.insert i (WeightedAnnulusDatum.scalarMap cs Rin X (ContinuousMap.curry (Φ i) y))) :=
    continuous_finset_sum _ (fun i _ =>
      ((DynamicConvolution.insert i).comp (WeightedAnnulusDatum.scalarMap cs Rin X)).continuous.comp
        (ContinuousMap.curry (Φ i)).continuous)
  refine hcont.congr (fun y => ?_)
  have hy : ‖(y : Space)‖ < Rin := (mem_closedBall_zero_iff.mp y.property).trans_lt hbR
  change _ = ShellReactionIdentification.freeDatum cs Rin X (y : Space) j
  unfold ShellReactionIdentification.freeDatum
  rw [dif_pos hy]
  unfold FreeDyadicMaterialData.datum
  apply Finset.sum_congr rfl
  intro i _
  congr 2

/-- The weighted free dipole data are Bochner integrable against a source supported in the core. -/
theorem freeDatum_integrable (cs ci : Coefficient) (b Rin : ℝ) (X : ℝ) (hbR : b < Rin)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (j : Fin 3) :
    Integrable (fun y => DynamicVolume.source ci v j y • ShellReactionIdentification.freeDatum cs Rin X y j) := by
  have hs : Integrable (DynamicVolume.source ci v j) := DynamicVolume.source_integrable ci v b hci j
  have hon : IntegrableOn (fun y => DynamicVolume.source ci v j y •
      ShellReactionIdentification.freeDatum cs Rin X y j) (closedBall (0 : Space) b) :=
    hs.integrableOn.smul_continuousOn (freeDatum_continuousOn cs b Rin X hbR j) (isCompact_closedBall 0 b)
  rw [← integrableOn_iff_integrable_of_support_subset (s := closedBall (0 : Space) b)]
  · exact hon
  · intro y hy
    by_contra hn
    apply hy
    simp [DynamicVolume.source_zero ci v b hci j y hn]

/-- The sandwich `Ss T Si v` of an inclusion source is the Bochner integral in `VectorL2` of the free
dipole data of the shell weighted by the source of `v`. -/
theorem freeDatum_integral (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) :
    StaticCoefficient.sqrtMultiplier cs
        (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci v)) =
      ∫ y : Space, ∑ j : Fin 3, DynamicVolume.source ci v j y •
        ShellReactionIdentification.freeDatum cs Rin X y j := by
  apply ext_inner_left ℂ
  intro h
  have hint (j : Fin 3) := freeDatum_integrable cs ci b Rin X hbR hci v j
  have hI : Integrable (fun y : Space => ∑ j : Fin 3, DynamicVolume.source ci v j y •
      ShellReactionIdentification.freeDatum cs Rin X y j) :=
    integrable_finset_sum _ (fun j _ => hint j)
  have hf := ShellReactionIdentification.weighted_kernel_functional cs ci b Rin X R hbR hRX hXR hcs hci v
    (innerSL ℂ h)
  have e1 : ⟪h, StaticCoefficient.sqrtMultiplier cs
      (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci v))⟫_ℂ =
      (innerSL ℂ h) (StaticCoefficient.sqrtMultiplier cs
        (ShellInclusionVolume.kernel 1 R (StaticCoefficient.sqrtMultiplier ci v))) := rfl
  have e2 : ⟪h, ∫ y : Space, ∑ j : Fin 3, DynamicVolume.source ci v j y •
      ShellReactionIdentification.freeDatum cs Rin X y j⟫_ℂ =
      (innerSL ℂ h) (∫ y : Space, ∑ j : Fin 3, DynamicVolume.source ci v j y •
        ShellReactionIdentification.freeDatum cs Rin X y j) := rfl
  rw [e1, e2, hf, ← ContinuousLinearMap.integral_comp_comm (innerSL ℂ h) hI]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [integral_finset_sum]
  intro j _
  have := (innerSL ℂ h).integrable_comp (hint j)
  simpa only [map_smul, smul_eq_mul] using this

/-! ### The block decomposition of the combined solution -/

section Blocks
variable (cs ci : Coefficient) (X : ℝ)

/-- The shell part of a combined solution `u` with shell datum `fs`: `fs + Ss T (Ss u + Si u)`. -/
def shellPart (fs u : VectorL2) : VectorL2 :=
  fs + StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 X
    (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u))

/-- The inclusion part of a combined solution `u` with inclusion datum `fi`: `fi + Si T (Ss u + Si u)`. -/
def inclPart (fi u : VectorL2) : VectorL2 :=
  fi + StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 X
    (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u))

variable {cs ci X}

theorem combined_equation (hd : ShellInclusionVolume.Disjoint cs ci) (u f : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = f) :
    u - (StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 X
        (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u)) +
      StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 X
        (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u))) = f := by
  rw [ShellInclusionVolume.combined_eq cs ci 1 X hd] at hCu
  rw [← hCu]
  simp only [ShellInclusionBlocks.combined, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply]

/-- A solution of the combined equation splits into its shell part and its inclusion part. -/
theorem solution_split (hd : ShellInclusionVolume.Disjoint cs ci) (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi) :
    u = shellPart cs ci X fs u + inclPart cs ci X fi u := by
  have h := combined_equation hd u _ hCu
  unfold shellPart inclPart
  rw [sub_eq_iff_eq_add] at h
  refine h.trans ?_
  abel

theorem Ss_inclPart (hd : ShellInclusionVolume.Disjoint cs ci) (fi u : VectorL2)
    (hfi : StaticCoefficient.sqrtMultiplier cs fi = 0) :
    StaticCoefficient.sqrtMultiplier cs (inclPart cs ci X fi u) = 0 := by
  unfold inclPart
  rw [map_add, hfi, zero_add]
  have := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (ShellInclusionVolume.kernel 1 X
    (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u)))
    (ShellInclusionVolume.sqrtMultiplier_mul_zero cs ci hd)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this

theorem Si_shellPart (hd : ShellInclusionVolume.Disjoint cs ci) (fs u : VectorL2)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) :
    StaticCoefficient.sqrtMultiplier ci (shellPart cs ci X fs u) = 0 := by
  unfold shellPart
  rw [map_add, hfs, zero_add]
  have := congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (ShellInclusionVolume.kernel 1 X
    (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u)))
    (ShellInclusionVolume.sqrtMultiplier_mul_zero ci cs hd.symm)
  simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply] using this

theorem Ss_solution (hd : ShellInclusionVolume.Disjoint cs ci) (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi)
    (hfi : StaticCoefficient.sqrtMultiplier cs fi = 0) :
    StaticCoefficient.sqrtMultiplier cs u = StaticCoefficient.sqrtMultiplier cs (shellPart cs ci X fs u) := by
  conv_lhs => rw [solution_split hd u fs fi hCu]
  rw [map_add, Ss_inclPart hd fi u hfi, add_zero]

theorem Si_solution (hd : ShellInclusionVolume.Disjoint cs ci) (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) :
    StaticCoefficient.sqrtMultiplier ci u = StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u) := by
  conv_lhs => rw [solution_split hd u fs fi hCu]
  rw [map_add, Si_shellPart hd fs u hfs, zero_add]

/-- The shell part solves the shell equation driven by the shell datum and the inclusion sandwich. -/
theorem shellPart_equation (hd : ShellInclusionVolume.Disjoint cs ci) (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi)
    (hfi : StaticCoefficient.sqrtMultiplier cs fi = 0)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) :
    DynamicVolume.volumeBlock cs 1 X (shellPart cs ci X fs u) =
      fs + StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 X
        (StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u))) := by
  have hP : StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u =
      StaticCoefficient.sqrtMultiplier cs (shellPart cs ci X fs u) +
        StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u) := by
    rw [Ss_solution hd u fs fi hCu hfi, Si_solution hd u fs fi hCu hfs]
  have hus : shellPart cs ci X fs u = fs + StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 X
      (StaticCoefficient.sqrtMultiplier cs (shellPart cs ci X fs u) +
        StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u))) := by
    show fs + StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 X
      (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u)) = _
    rw [hP]
  rw [ShellInclusionVolume.shell_eq cs 1 X]
  simp only [ShellInclusionBlocks.shell, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply]
  generalize shellPart cs ci X fs u = us at hus ⊢
  generalize inclPart cs ci X fi u = ui at hus ⊢
  have e := hus
  simp only [map_add] at e
  rw [sub_eq_iff_eq_add]
  refine e.trans ?_
  abel

theorem shellPart_eq (hd : ShellInclusionVolume.Disjoint cs ci)
    (hs : IsUnit (DynamicVolume.volumeBlock cs 1 X)) (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi)
    (hfi : StaticCoefficient.sqrtMultiplier cs fi = 0)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) :
    shellPart cs ci X fs u = Ring.inverse (DynamicVolume.volumeBlock cs 1 X)
      (fs + StaticCoefficient.sqrtMultiplier cs (ShellInclusionVolume.kernel 1 X
        (StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u)))) := by
  rw [← shellPart_equation hd u fs fi hCu hfi hfs]
  exact (congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (shellPart cs ci X fs u))
    (Ring.inverse_mul_cancel _ hs)).symm

/-- The inclusion part solves the effective equation with the effective datum
`fi + Si T Ss r fs`. -/
theorem inclPart_equation (hd : ShellInclusionVolume.Disjoint cs ci)
    (hs : IsUnit (DynamicVolume.volumeBlock cs 1 X)) (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi)
    (hfi : StaticCoefficient.sqrtMultiplier cs fi = 0)
    (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0) :
    ShellInclusionBlocks.effective (StaticCoefficient.sqrtMultiplier cs) (StaticCoefficient.sqrtMultiplier ci)
        (ShellInclusionVolume.kernel 1 X) (inclPart cs ci X fi u) =
      fi + StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 X
        (StaticCoefficient.sqrtMultiplier cs (Ring.inverse (DynamicVolume.volumeBlock cs 1 X) fs))) := by
  have hP : StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u =
      StaticCoefficient.sqrtMultiplier cs (shellPart cs ci X fs u) +
        StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u) := by
    rw [Ss_solution hd u fs fi hCu hfi, Si_solution hd u fs fi hCu hfs]
  have hus := shellPart_eq hd hs u fs fi hCu hfi hfs
  have hui : inclPart cs ci X fi u = fi + StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 X
      (StaticCoefficient.sqrtMultiplier cs (shellPart cs ci X fs u) +
        StaticCoefficient.sqrtMultiplier ci (inclPart cs ci X fi u))) := by
    show fi + StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 X
      (StaticCoefficient.sqrtMultiplier cs u + StaticCoefficient.sqrtMultiplier ci u)) = _
    rw [hP]
  generalize inclPart cs ci X fi u = ui at hui hus ⊢
  generalize shellPart cs ci X fs u = us at hui hus
  subst hus
  have hg := ShellInclusionReaction.green_eq cs 1 X
  have e := hui
  simp only [map_add] at e
  simp only [ShellInclusionBlocks.effective, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.one_apply, hg, ContinuousLinearMap.add_apply, ShellInclusionReaction.scatteredGreen,
    map_add]
  rw [sub_eq_iff_eq_add]
  refine e.trans ?_
  abel

end Blocks

/-! ### Data of an incident field and the effective datum -/

/-- `h` is the weighted datum of the field `F` for the coefficient `c`: almost everywhere
`h = sqrt c * F`. -/
def IsDatum (c : Coefficient) (F : Maxwell.Field) (h : VectorL2) : Prop :=
  ∀ i : Fin 3, (fun x : Space => h (VectorFourier.coordinateMap x) i) =ᵐ[volume]
    fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * F x i

theorem IsDatum.unique {c : Coefficient} {F : Maxwell.Field} {h h' : VectorL2} (hh : IsDatum c F h)
    (hh' : IsDatum c F h') : h = h' :=
  HalfTurnVectorAction.vector_ext_pt h h' (fun i => (hh i).trans (hh' i).symm)

/-- The data of the shell and of the inclusion add up to the datum of the combined coefficient. -/
theorem isDatum_add (cs ci : Coefficient) (hd : ShellInclusionVolume.Disjoint cs ci) (F : Maxwell.Field)
    (fs fi : VectorL2) (hfs : IsDatum cs F fs) (hfi : IsDatum ci F fi) :
    IsDatum (ShellInclusionVolume.add cs ci) F (fs + fi) := by
  intro i
  filter_upwards [hfs i, hfi i, VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add fs fi)] with x h1 h2 h3
  have hadd : ∀ a b : VectorFourier.Vector, (a + b) i = a i + b i := fun a b => rfl
  have h := ShellInclusionVolume.sqrt_add_of_disjoint (cs.value (VectorFourier.coordinateMap x))
    (ci.value (VectorFourier.coordinateMap x)) (hd (VectorFourier.coordinateMap x))
  change (fs + fi) (VectorFourier.coordinateMap x) i =
    ((Real.sqrt (cs.value (VectorFourier.coordinateMap x) + ci.value (VectorFourier.coordinateMap x)) : ℝ) : ℂ) *
      F x i
  rw [h3]
  simp only [Pi.add_apply]
  rw [hadd, h1, h2, h]
  push_cast
  ring

theorem sqrtMultiplier_isDatum_zero (cs ci : Coefficient) (hd : ShellInclusionVolume.Disjoint cs ci)
    (F : Maxwell.Field) (h : VectorL2) (hh : IsDatum ci F h) :
    StaticCoefficient.sqrtMultiplier cs h = 0 := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  filter_upwards [HalfTurnVectorAction.sqrt_pt cs h i, hh i,
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_zero VectorFourier.Vector 2 volume)] with x h1 h2 h3
  rw [h1, h3]
  change (Real.sqrt (cs.value (VectorFourier.coordinateMap x)) : ℂ) * h (VectorFourier.coordinateMap x) i = _
  rw [h2]
  rcases hd (VectorFourier.coordinateMap x) with h0 | h0
  · simp [h0]
  · simp [h0]

theorem source_add_disjoint (cs ci : Coefficient) (hd : ShellInclusionVolume.Disjoint cs ci) (u : VectorL2)
    (j : Fin 3) (y : Space) :
    DynamicVolume.source (ShellInclusionVolume.add cs ci) u j y =
      DynamicVolume.source cs u j y + DynamicVolume.source ci u j y := by
  unfold DynamicVolume.source
  have h := ShellInclusionVolume.sqrt_add_of_disjoint (cs.value (VectorFourier.coordinateMap y))
    (ci.value (VectorFourier.coordinateMap y)) (hd (VectorFourier.coordinateMap y))
  change ((Real.sqrt (cs.value (VectorFourier.coordinateMap y) + ci.value (VectorFourier.coordinateMap y)) : ℝ) : ℂ) *
    u (VectorFourier.coordinateMap y) j = _
  rw [h]
  push_cast
  ring

theorem source_congr_of_sqrt (c : Coefficient) (u v : VectorL2)
    (h : StaticCoefficient.sqrtMultiplier c u = StaticCoefficient.sqrtMultiplier c v) (j : Fin 3) :
    DynamicVolume.source c u j =ᵐ[volume] DynamicVolume.source c v j := by
  filter_upwards [StaticNewton.material_source_ae c u j, StaticNewton.material_source_ae c v j] with y h1 h2
  have : NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c u) j y =
      NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c v) j y := by rw [h]
  exact h1.symm.trans (this.trans h2)

/-- The effective datum `fi + Si T Ss r fs` of the effective inclusion equation. -/
def effectiveDatum (cs ci : Coefficient) (R : ℝ) (fs fi : VectorL2) : VectorL2 :=
  fi + StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 R
    (StaticCoefficient.sqrtMultiplier cs (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs)))

/-- The electric background: the incident field plus the response of the shell polarization induced by
the incident shell datum alone. -/
def backgroundElectric (cs : Coefficient) (R : ℝ) (inc : Maxwell.Field) (fs : VectorL2) : Maxwell.Field :=
  fun x i => inc x i + ExteriorContinuity.electric 1 (DynamicVolume.source cs
    (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs)) x i

/-- The magnetic background. -/
def backgroundMagnetic (cs : Coefficient) (R : ℝ) (inc : Maxwell.Field) (fs : VectorL2) : Maxwell.Field :=
  fun x i => inc x i + MagneticResponse.magnetic 1 (DynamicVolume.source cs
    (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs)) x i

/-- The effective datum is the weighted datum of the electric background field on the inclusion. -/
theorem effectiveDatum_isDatum (cs ci : Coefficient) (b Rin X R : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hXR : X ≤ R)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (inc : Maxwell.Field) (fs fi : VectorL2) (hfi : IsDatum ci inc fi) :
    IsDatum ci (backgroundElectric cs R inc fs) (effectiveDatum cs ci R fs fi) := by
  intro i
  filter_upwards [hfi i,
    VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
      (Lp.coeFn_add fi (StaticCoefficient.sqrtMultiplier ci (ShellInclusionVolume.kernel 1 R
        (StaticCoefficient.sqrtMultiplier cs (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs))))),
    HalfTurnVectorAction.sqrt_pt ci (ShellInclusionVolume.kernel 1 R
        (StaticCoefficient.sqrtMultiplier cs (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs))) i,
    NewtonL2.physicalCoordinate_ae (ShellInclusionVolume.kernel 1 R
        (StaticCoefficient.sqrtMultiplier cs (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs))) i,
    ShellReactionIdentification.kernel_core_ae cs Rin X R hRX hXR hcs
      (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) fs) i] with x h1 h2 h3 h4 h5
  have hadd : ∀ a b : VectorFourier.Vector, (a + b) i = a i + b i := fun a b => rfl
  change (effectiveDatum cs ci R fs fi) (VectorFourier.coordinateMap x) i = _
  unfold effectiveDatum
  rw [h2]
  simp only [Pi.add_apply]
  rw [hadd, h1, h3]
  change _ + (Real.sqrt (ci.value (VectorFourier.coordinateMap x)) : ℂ) * _ = _
  rw [← h4]
  by_cases hx : ‖x‖ < Rin
  · rw [h5 hx, CoreMaterialEvaluation.evaluation_actual]
    unfold backgroundElectric ExteriorContinuity.electric KernelConvolution.response
    ring
  · have hc : ci.value (VectorFourier.coordinateMap x) = 0 := by
      apply hci
      intro hmem
      exact hx ((mem_closedBall_zero_iff.mp hmem).trans_lt hbR)
    simp [hc]


/-! ### The total field of the combined solution is the assembled plane field -/

theorem response_sum_split (K : Fin 3 → Space → ℂ) (x : Space) (c1 c2 c : Coefficient) (u u1 u2 : VectorL2)
    (hsrc : ∀ j, DynamicVolume.source c u j =ᵐ[volume]
      fun y => DynamicVolume.source c1 u1 j y + DynamicVolume.source c2 u2 j y)
    (h1 : ∀ j, Integrable (fun y => DynamicVolume.source c1 u1 j y * K j (x - y)))
    (h2 : ∀ j, Integrable (fun y => DynamicVolume.source c2 u2 j y * K j (x - y))) :
    ∑ j : Fin 3, KernelConvolution.response (K j) (DynamicVolume.source c u j) x =
      ∑ j : Fin 3, KernelConvolution.response (K j) (DynamicVolume.source c1 u1 j) x +
        ∑ j : Fin 3, KernelConvolution.response (K j) (DynamicVolume.source c2 u2 j) x := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold KernelConvolution.response
  rw [← integral_add (h1 j) (h2 j)]
  apply integral_congr_ae
  filter_upwards [hsrc j] with y hy
  rw [hy]
  ring

theorem combined_source_split {cs ci : Coefficient} {X : ℝ} (hd : ShellInclusionVolume.Disjoint cs ci)
    (u fs fi : VectorL2)
    (hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add cs ci) 1 X u = fs + fi)
    (hfi : StaticCoefficient.sqrtMultiplier cs fi = 0) (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0)
    (j : Fin 3) :
    DynamicVolume.source (ShellInclusionVolume.add cs ci) u j =ᵐ[volume]
      fun y => DynamicVolume.source cs (shellPart cs ci X fs u) j y +
        DynamicVolume.source ci (inclPart cs ci X fi u) j y := by
  filter_upwards [source_congr_of_sqrt cs u _ (Ss_solution hd u fs fi hCu hfi) j,
    source_congr_of_sqrt ci u _ (Si_solution hd u fs fi hCu hfs) j] with y h1 h2
  rw [source_add_disjoint cs ci hd u j y, h1, h2]

/-- The continuous representative of the total electric field of the combined solution with datum `f`:
the incident field plus the literal dyadic integral of the combined polarization. -/
def continuousTotalElectric (c : Coefficient) (R : ℝ) (inc : Maxwell.Field) (f : VectorL2) : Maxwell.Field :=
  fun x i => inc x i + ExteriorContinuity.electric 1 (DynamicVolume.source c
    (MaterialField.solution c 1 R f)) x i

/-- The continuous representative of the total magnetic field of the combined solution. -/
def continuousTotalMagnetic (c : Coefficient) (R : ℝ) (inc : Maxwell.Field) (f : VectorL2) : Maxwell.Field :=
  fun x i => inc x i + MagneticResponse.magnetic 1 (DynamicVolume.source c
    (MaterialField.solution c 1 R f)) x i

theorem shell_hcs (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) :
    ∀ y : Space, y ∉ closedBall (0 : Space) (SourcePairedInclusion.data q hq n r).X \
        ball (0 : Space) (SourcePairedInclusion.data q hq n r).R →
      (SourcePairedInclusion.shell q hq n r).value (VectorFourier.coordinateMap y) = 0 := by
  intro y hy
  by_cases h1 : y ∈ closedBall (0 : Space) (SourcePairedInclusion.data q hq n r).X
  · by_cases h2 : y ∈ ball (0 : Space) (SourcePairedInclusion.data q hq n r).R
    · exact SourcePairedInclusion.shell_inner q hq n r y (mem_ball_zero_iff.mp h2).le
    · exact absurd ⟨h1, h2⟩ hy
  · exact SourcePairedInclusion.shell_support q hq n r y h1

/-- The assembled electric plane field with the shell reaction field replaced by the literal field of the
shell polarization of the induced shell solution. -/
theorem pairedPlaneElectric_eq_free (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (inc : Maxwell.Field) (x : Space) (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R)
    (i : Fin 3) :
    SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci v inc x i =
      inc x i + ExteriorContinuity.electric 1 (DynamicVolume.source ci v) x i +
        ExteriorContinuity.electric 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r)
          (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
            (SourcePairedInclusion.data q hq n r).X)
            (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
              (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
                (StaticCoefficient.sqrtMultiplier ci v))))) x i := by
  unfold SourcePairedPlaneCompact.pairedPlaneElectric
  rw [reactionField_eq_free (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.data q hq n r).X hb (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
    (shell_hcs q hq n r) hci v x hx i]

/-- The assembled magnetic plane field with the shell magnetic reaction field replaced by the literal
magnetic field of the shell polarization of the induced shell solution. -/
theorem pairedPlaneMagnetic_eq_free (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
    (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (v : VectorL2) (inc : Maxwell.Field) (x : Space) (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R)
    (i : Fin 3) :
    SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci v inc x i =
      inc x i + MagneticResponse.magnetic 1 (DynamicVolume.source ci v) x i +
        MagneticResponse.magnetic 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r)
          (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
            (SourcePairedInclusion.data q hq n r).X)
            (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
              (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
                (StaticCoefficient.sqrtMultiplier ci v))))) x i := by
  unfold SourcePairedPlaneMagnetic.pairedPlaneMagnetic
  rw [magneticReactionField_eq_free (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.data q hq n r).X hb (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
    (shell_hcs q hq n r) hci v x hx i]

section Fields
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
  (hb : b < (SourcePairedInclusion.data q hq n r).R)
  (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
  (d : BoundedMaterialKernel.SupportData ci)
  (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b))
  (inc : Maxwell.Field) (fs fi : VectorL2)
  (hfi : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) fi = 0)
  (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0)
  (η : ℝ) (hη : 0 < η) (x : Space) (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R)
  (hxη : ∀ y ∈ d.carrier, η ≤ ‖x - y‖) (i : Fin 3)
include hb hci hE hfi hfs hη hx hxη

omit hη hx hxη in
/-- The inclusion part of the combined solution is the effective inclusion solution of the effective
datum. -/
theorem inclPart_eq_effective :
    inclPart (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X fi
        (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (SourcePairedInclusion.data q hq n r).X (fs + fi)) =
      Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
        (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
          fs fi) := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hs := SourcePairedInclusion.shell_isUnit q hq n r
  have hC := SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb.le hci hE
  have hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
      (SourcePairedInclusion.data q hq n r).X (MaterialField.solution
        (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
        (SourcePairedInclusion.data q hq n r).X (fs + fi)) = fs + fi :=
    congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fs + fi))
      (Ring.mul_inverse_cancel _ hC)
  have hEq := inclPart_equation hd hs _ fs fi hCu hfi hfs
  rw [SourcePairedInclusion.effective_eq q hq n r ci b hb.le hci] at hEq
  unfold effectiveDatum
  rw [← hEq]
  exact (congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L _)
    (Ring.inverse_mul_cancel _ hE)).symm

/-- The electric total field of the combined solution equals the assembled plane field. -/
theorem combined_total_electric_eq :
    continuousTotalElectric (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
        (SourcePairedInclusion.data q hq n r).X inc (fs + fi) x i =
      SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
        (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
          (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
            fs fi))
        (backgroundElectric (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
          inc fs) x i := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hs := SourcePairedInclusion.shell_isUnit q hq n r
  have hC := SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb.le hci hE
  obtain ⟨u, hu⟩ : ∃ u : VectorL2, u = MaterialField.solution
    (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
    (SourcePairedInclusion.data q hq n r).X (fs + fi) := ⟨_, rfl⟩
  have hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
      (SourcePairedInclusion.data q hq n r).X u = fs + fi := by
    rw [hu]
    exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fs + fi)) (Ring.mul_inverse_cancel _ hC)
  have hui := inclPart_eq_effective q hq n r ci b hb hci hE fs fi hfi hfs
  rw [← hu] at hui
  obtain ⟨ui, hui_def⟩ : ∃ ui : VectorL2, ui = inclPart (SourcePairedInclusion.shell q hq n r) ci
    (SourcePairedInclusion.data q hq n r).X fi u := ⟨_, rfl⟩
  obtain ⟨us, hus_def⟩ : ∃ us : VectorL2, us = shellPart (SourcePairedInclusion.shell q hq n r) ci
    (SourcePairedInclusion.data q hq n r).X fs u := ⟨_, rfl⟩
  have hus := shellPart_eq hd hs u fs fi hCu hfi hfs
  rw [← hus_def, ← hui_def] at hus
  rw [← hui_def] at hui
  have hcs := shell_hcs q hq n r
  have hRX := SourcePairedInclusion.radii_ordered q hq n r
  have hsplit := response_sum_split (fun j z => DyadicKernel.dyadic 1 z i j) x _ _ _ u us ui
    (fun j => by
      have := combined_source_split hd u fs fi hCu hfi hfs j
      rw [← hus_def, ← hui_def] at this
      exact this)
    (fun j => CoreMaterialEvaluation.actual_integrand_integrable
      (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X hcs x hx i j us)
    (fun j => response_integrand_integrable ci d (fun z => DyadicKernel.dyadic 1 z i j)
      (PlaneSourceKernel.dyadic_measurable 1 i j) x (NewtonStripMaxwell.electricBound 1 (2 * η))
      (fun y hy => NewtonStripMaxwell.electric_bound 1 (2 * η) (by linarith) (x - y)
        (by have := hxη y hy; linarith) i j) ui j)
  have hreact := reactionField_eq_free (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.data q hq n r).X hb hRX le_rfl hcs hci ui x hx i
  have hEv : CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i us =
      CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i
        (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X) fs) +
      CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i
        (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X)
          (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
            (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
              (StaticCoefficient.sqrtMultiplier ci ui)))) := by
    rw [hus, map_add, map_add]
  have eC := CoreMaterialEvaluation.evaluation_actual (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i us
  have eD := CoreMaterialEvaluation.evaluation_actual (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i
    (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X) fs)
  have eE := CoreMaterialEvaluation.evaluation_actual (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i
    (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
      (SourcePairedInclusion.data q hq n r).X)
      (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
        (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
          (StaticCoefficient.sqrtMultiplier ci ui))))
  unfold continuousTotalElectric SourcePairedPlaneCompact.pairedPlaneElectric backgroundElectric
  rw [← hu, ← hui]
  have eA : ExteriorContinuity.electric 1 (DynamicVolume.source
      (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u j) x := rfl
  rw [eA, hsplit]
  have eF : ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
      (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) us j) x =
      CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i us := by
    rw [eC]
    rfl
  have eD' : CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i
      (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
        (SourcePairedInclusion.data q hq n r).X) fs) =
      ExteriorContinuity.electric 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r)
        (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X) fs)) x i := eD
  have eE' : CoreMaterialEvaluation.evaluation (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx i
      (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
        (SourcePairedInclusion.data q hq n r).X)
        (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
          (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
            (StaticCoefficient.sqrtMultiplier ci ui)))) =
      SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X ui x i := by
    rw [hreact]
    exact eE
  rw [eF, hEv, eD', eE']
  have eB' : ExteriorContinuity.electric 1 (DynamicVolume.source ci ui) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source ci ui j) x := rfl
  rw [eB']
  ring

/-- The magnetic total field of the combined solution equals the assembled plane magnetic field (the
field `inc` is the incident magnetic field here). -/
theorem combined_total_magnetic_eq :
    continuousTotalMagnetic (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
        (SourcePairedInclusion.data q hq n r).X inc (fs + fi) x i =
      SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci
        (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
          (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
            fs fi))
        (backgroundMagnetic (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
          inc fs) x i := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hs := SourcePairedInclusion.shell_isUnit q hq n r
  have hC := SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb.le hci hE
  obtain ⟨u, hu⟩ : ∃ u : VectorL2, u = MaterialField.solution
    (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
    (SourcePairedInclusion.data q hq n r).X (fs + fi) := ⟨_, rfl⟩
  have hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
      (SourcePairedInclusion.data q hq n r).X u = fs + fi := by
    rw [hu]
    exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fs + fi)) (Ring.mul_inverse_cancel _ hC)
  have hui := inclPart_eq_effective q hq n r ci b hb hci hE fs fi hfi hfs
  rw [← hu] at hui
  obtain ⟨ui, hui_def⟩ : ∃ ui : VectorL2, ui = inclPart (SourcePairedInclusion.shell q hq n r) ci
    (SourcePairedInclusion.data q hq n r).X fi u := ⟨_, rfl⟩
  obtain ⟨us, hus_def⟩ : ∃ us : VectorL2, us = shellPart (SourcePairedInclusion.shell q hq n r) ci
    (SourcePairedInclusion.data q hq n r).X fs u := ⟨_, rfl⟩
  have hus := shellPart_eq hd hs u fs fi hCu hfi hfs
  rw [← hus_def, ← hui_def] at hus
  rw [← hui_def] at hui
  have hcs := shell_hcs q hq n r
  have hRX := SourcePairedInclusion.radii_ordered q hq n r
  have hB1 := magnetic_annulus_bound (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs x hx
  have hB10 := magnetic_annulus_bound_nonneg (SourcePairedInclusion.data q hq n r).R x hx
  have hsplit := response_sum_split (fun j z => SphereMagneticKernel.magneticDyadic 1 z i j) x _ _ _ u us ui
    (fun j => by
      have := combined_source_split hd u fs fi hCu hfi hfs j
      rw [← hus_def, ← hui_def] at this
      exact this)
    (fun j => response_integrand_integrable (SourcePairedInclusion.shell q hq n r)
      (CoreMaterialEvaluation.supportData (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs)
      (fun z => SphereMagneticKernel.magneticDyadic 1 z i j) (measurable_magneticDyadic i j) x _
      (fun y hy => hB1 y hy i j) us j)
    (fun j => response_integrand_integrable ci d (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
      (measurable_magneticDyadic i j) x (2 * NewtonStripMaxwell.gradientBound 1 (2 * η))
      (fun y hy => magneticDyadic_bound (x - y) (2 * η) (by linarith)
        (by have := hxη y hy; linarith) i j) ui j)
  have hreact := magneticReactionField_eq_free (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.data q hq n r).X hb hRX le_rfl hcs hci ui x hx i
  have hEv : magneticEvaluation (SourcePairedInclusion.shell q hq n r)
      (CoreMaterialEvaluation.supportData (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs) x _ hB10 hB1 i us =
      magneticEvaluation (SourcePairedInclusion.shell q hq n r)
        (CoreMaterialEvaluation.supportData (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs) x _ hB10 hB1 i
        (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X) fs) +
      magneticEvaluation (SourcePairedInclusion.shell q hq n r)
        (CoreMaterialEvaluation.supportData (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hcs) x _ hB10 hB1 i
        (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X)
          (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
            (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
              (StaticCoefficient.sqrtMultiplier ci ui)))) := by
    rw [hus, map_add, map_add]
  rw [magneticEvaluation_apply, magneticEvaluation_apply, magneticEvaluation_apply, ← hreact] at hEv
  unfold continuousTotalMagnetic SourcePairedPlaneMagnetic.pairedPlaneMagnetic backgroundMagnetic
  rw [← hu, ← hui]
  have eA : MagneticResponse.magnetic 1 (DynamicVolume.source
      (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
        (DynamicVolume.source (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) u j) x :=
    magnetic_eq_sum 1 _ x i
  have eF : MagneticResponse.magnetic 1 (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) us) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
        (DynamicVolume.source (SourcePairedInclusion.shell q hq n r) us j) x := magnetic_eq_sum 1 _ x i
  have eB : MagneticResponse.magnetic 1 (DynamicVolume.source ci ui) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => SphereMagneticKernel.magneticDyadic 1 z i j)
        (DynamicVolume.source ci ui j) x := magnetic_eq_sum 1 _ x i
  rw [eA, hsplit, ← eF, ← eB, hEv]
  ring

omit hη hx hxη in
/-- The block form of the combined solution: shell response of the shell datum, plus the shell
response to the inclusion sandwich of the inclusion part, plus the inclusion part, which is the
effective inclusion solution of the effective datum. -/
theorem combined_solution_blocks :
    MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
        (SourcePairedInclusion.data q hq n r).X (fs + fi) =
      (Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X) fs +
        Ring.inverse (DynamicVolume.volumeBlock (SourcePairedInclusion.shell q hq n r) 1
          (SourcePairedInclusion.data q hq n r).X)
          (StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r)
            (ShellInclusionVolume.kernel 1 (SourcePairedInclusion.data q hq n r).X
              (StaticCoefficient.sqrtMultiplier ci
                (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
                  (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
                    (SourcePairedInclusion.data q hq n r).X fs fi)))))) +
        Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
          (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
            fs fi) := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hs := SourcePairedInclusion.shell_isUnit q hq n r
  have hC := SourcePairedInclusion.combined_isUnit_of_effective q hq n r ci b hb.le hci hE
  obtain ⟨u, hu⟩ : ∃ u : VectorL2, u = MaterialField.solution
    (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
    (SourcePairedInclusion.data q hq n r).X (fs + fi) := ⟨_, rfl⟩
  have hCu : DynamicVolume.volumeBlock (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
      (SourcePairedInclusion.data q hq n r).X u = fs + fi := by
    rw [hu]
    exact congrArg (fun L : VectorL2 →L[ℂ] VectorL2 => L (fs + fi)) (Ring.mul_inverse_cancel _ hC)
  have hui := inclPart_eq_effective q hq n r ci b hb hci hE fs fi hfi hfs
  rw [← hu] at hui
  rw [← hu, solution_split hd u fs fi hCu, shellPart_eq hd hs u fs fi hCu hfi hfs, map_add, hui]

end Fields

/-! ### The almost-everywhere identification of the scattered field on the gap annulus -/

theorem physicalCoordinate_add (F G : VectorL2) (i : Fin 3) :
    NewtonL2.physicalCoordinate (F + G) i =
      NewtonL2.physicalCoordinate F i + NewtonL2.physicalCoordinate G i := by
  unfold NewtonL2.physicalCoordinate
  rw [map_add, map_add]

/-- The continuous representative of the total magnetic field is literally the pointwise total magnetic
field `MaterialMaxwell.totalMagnetic` of the combined solution. -/
theorem magnetic_total_eq (c : Coefficient) (R : ℝ) (inc : Maxwell.Field) (f : VectorL2) :
    continuousTotalMagnetic c R inc f =
      MaterialMaxwell.totalMagnetic c 1 (MaterialField.solution c 1 R f) inc := rfl

/-- On the gap annulus `b < |x| < Rin` the scattered field of the combined solution, an element of
`L2`, equals almost everywhere the literal dyadic integral of the combined polarization. -/
theorem scattered_ae_annulus (cs ci : Coefficient) (b Rin X : ℝ) (hbR : b < Rin) (hRX : Rin ≤ X)
    (hcs : ∀ y : Space, y ∉ closedBall (0 : Space) X \ ball (0 : Space) Rin →
      cs.value (VectorFourier.coordinateMap y) = 0)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hd : ShellInclusionVolume.Disjoint cs ci) (u : VectorL2) (i : Fin 3) :
    ∀ᵐ x : Space, b < ‖x‖ → ‖x‖ < Rin →
      MaterialField.scattered (ShellInclusionVolume.add cs ci) 1 u x i =
        ExteriorContinuity.electric 1 (DynamicVolume.source (ShellInclusionVolume.add cs ci) u) x i := by
  have hcsX : ∀ y : Space, y ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap y) = 0 :=
    fun y hy => hcs y (fun h => hy h.1)
  have hciX : ∀ y : Space, y ∉ closedBall (0 : Space) X → ci.value (VectorFourier.coordinateMap y) = 0 :=
    fun y hy => hci y (fun h => hy (closedBall_subset_closedBall (hbR.le.trans hRX) h))
  have hρs := fun j => DynamicVolume.source_integrable cs u X hcsX j
  have hρi := fun j => DynamicVolume.source_integrable ci u b hci j
  have hFs := StaticNewton.material_source_ae cs u
  have hFi := StaticNewton.material_source_ae ci u
  have hi_s : ∀ j y, y ∈ ball (0 : Space) Rin → DynamicVolume.source cs u j y = 0 := by
    intro j y hy
    unfold DynamicVolume.source
    rw [hcs y (fun h => h.2 hy)]
    simp
  have hint := ConicalInteriorResponse.electric_ae_interior 1 (StaticCoefficient.sqrtMultiplier cs u)
    (DynamicVolume.source cs u) hρs hFs Rin X (DynamicVolume.source_zero cs u X hcsX) hi_s
  have hext := ExteriorContinuity.electric_ae_exterior 1 (StaticCoefficient.sqrtMultiplier ci u)
    (DynamicVolume.source ci u) hρi hFi b (DynamicVolume.source_zero ci u b hci)
  have hrs : ∀ᵐ x : Space, ∀ j : Fin 3, x ∈ closedBall (0 : Space) X →
      Integrable (fun y => DyadicKernel.remainder 1 (x - y) i j * DynamicVolume.source cs u j y) :=
    ae_all_iff.mpr (fun j => DynamicVolume.remainder_source_integrable_ae cs u 1 X hcsX i j)
  have hri : ∀ᵐ x : Space, ∀ j : Fin 3, x ∈ closedBall (0 : Space) X →
      Integrable (fun y => DyadicKernel.remainder 1 (x - y) i j * DynamicVolume.source ci u j y) :=
    ae_all_iff.mpr (fun j => DynamicVolume.remainder_source_integrable_ae ci u 1 X hciX i j)
  filter_upwards [hint, hext, hrs, hri,
    Lp.coeFn_add (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier cs u)) i)
      (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier ci u)) i)]
    with x h1 h2 h3 h4 h5 hbx hxR
  have h1' := congrFun (h1 (mem_ball_zero_iff.mpr hxR)) i
  have h2' := congrFun (h2 hbx) i
  have hxX : x ∈ closedBall (0 : Space) X := mem_closedBall_zero_iff.mpr (hxR.le.trans hRX)
  have hsrc (j : Fin 3) : DynamicVolume.source (ShellInclusionVolume.add cs ci) u j =ᵐ[volume]
      fun y => DynamicVolume.source cs u j y + DynamicVolume.source ci u j y :=
    Filter.Eventually.of_forall (fun y => source_add_disjoint cs ci hd u j y)
  have hsplitR := response_sum_split (fun j z => DyadicKernel.remainder 1 z i j) x _ _
    (ShellInclusionVolume.add cs ci) u u u hsrc
    (fun j => by simpa only [mul_comm] using h3 j hxX)
    (fun j => by simpa only [mul_comm] using h4 j hxX)
  have hsplitD := response_sum_split (fun j z => DyadicKernel.dyadic 1 z i j) x _ _
    (ShellInclusionVolume.add cs ci) u u u hsrc
    (fun j => CoreMaterialEvaluation.actual_integrand_integrable cs Rin X hcs x hxR i j u)
    (fun j => NewtonExteriorResponse.source_integrand_integrable
      (fun z => DyadicKernel.dyadic 1 z i j) (DynamicVolume.source ci u j)
      (fun z hz => ExteriorContinuity.dyadic_continuousAt 1 i j z hz) (hρi j) b
      (DynamicVolume.source_zero ci u b hci j) x hbx)
  unfold MaterialField.scattered FieldResponse.electric at *
  rw [ShellInclusionVolume.sqrtMultiplier_add cs ci hd, ContinuousLinearMap.add_apply, map_add,
    physicalCoordinate_add, h5]
  change (NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier cs u)) i x +
    NewtonL2.physicalCoordinate (NewtonL2.newtonOperator (StaticCoefficient.sqrtMultiplier ci u)) i x) +
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.remainder 1 z i j)
        (DynamicVolume.source (ShellInclusionVolume.add cs ci) u j) x = _
  rw [hsplitR]
  have eE : ExteriorContinuity.electric 1 (DynamicVolume.source (ShellInclusionVolume.add cs ci) u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source (ShellInclusionVolume.add cs ci) u j) x := rfl
  rw [eE, hsplitD]
  have eS : ExteriorContinuity.electric 1 (DynamicVolume.source cs u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source cs u j) x := rfl
  have eI : ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x i =
      ∑ j : Fin 3, KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source ci u j) x := rfl
  rw [eS] at h1'
  rw [eI] at h2'
  linear_combination h1' + h2'

/-! ### The physical total fields of the combined solution -/

/-- Support data of an inclusion supported in the closed ball of radius `b`. -/
def ballSupportData (ci : Coefficient) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0) :
    BoundedMaterialKernel.SupportData ci where
  radius := b
  carrier := closedBall (0 : Space) b
  measurable := measurableSet_closedBall
  finite := (measure_closedBall_lt_top (x := (0 : Space)) (r := b)).ne
  ballZero := hci
  carrierZero := hci

section Physical
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
  (hb : b < (SourcePairedInclusion.data q hq n r).R)
  (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
  (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b))
  (inc : Maxwell.Field) (fs fi : VectorL2)
  (hfi : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) fi = 0)
  (hfs : StaticCoefficient.sqrtMultiplier ci fs = 0)
include hb hci hE hfi hfs

/-- The physical total electric field of the combined solution (the `L2` class `MaterialField.total`)
equals, almost everywhere on the gap annulus `b < |x| < Rin`, the assembled plane electric field. -/
theorem combined_total_electric_ae :
    ∀ᵐ x : Space, b < ‖x‖ → ‖x‖ < (SourcePairedInclusion.data q hq n r).R → ∀ i : Fin 3,
      MaterialField.total (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
            (SourcePairedInclusion.data q hq n r).X (fs + fi)) inc x i =
        SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
          (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
            (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
              (SourcePairedInclusion.data q hq n r).X fs fi))
          (backgroundElectric (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
            inc fs) x i := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hae := ae_all_iff.mpr (fun i : Fin 3 => scattered_ae_annulus (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X hb
    (SourcePairedInclusion.radii_ordered q hq n r) (shell_hcs q hq n r) hci hd
    (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
      (SourcePairedInclusion.data q hq n r).X (fs + fi)) i)
  filter_upwards [hae] with x hx hbx hxR i
  have hxη : ∀ y ∈ (ballSupportData ci b hci).carrier, ‖x‖ - b ≤ ‖x - y‖ := by
    intro y hy
    have hy' : ‖y‖ ≤ b := mem_closedBall_zero_iff.mp hy
    have := norm_sub_norm_le x y
    linarith
  have h := combined_total_electric_eq q hq n r ci b hb hci (ballSupportData ci b hci) hE inc fs fi hfi hfs
    (‖x‖ - b) (by linarith) x hxR hxη i
  unfold MaterialField.total
  rw [hx i hbx hxR]
  exact h

/-- The physical total magnetic field of the combined solution equals the assembled plane magnetic
field at every point of the core at positive distance from the carrier. -/
theorem combined_totalMagnetic_eq (d : BoundedMaterialKernel.SupportData ci) (η : ℝ) (hη : 0 < η)
    (x : Space) (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (hxη : ∀ y ∈ d.carrier, η ≤ ‖x - y‖)
    (i : Fin 3) :
    MaterialMaxwell.totalMagnetic (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
            (SourcePairedInclusion.data q hq n r).X (fs + fi)) inc x i =
        SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci
          (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
            (effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
              (SourcePairedInclusion.data q hq n r).X fs fi))
          (backgroundMagnetic (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
            inc fs) x i :=
  combined_total_magnetic_eq q hq n r ci b hb hci d hE inc fs fi hfi hfs η hη x hx hxη i

end Physical

/-! ### Convergence of the assembled plane fields along a convergent sequence of inclusion parts -/

section Sequences
variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) (hsym : HalfTurnVectorAction.Symmetric ci)
include hcar hsym

/-- The effective inclusion solutions with a convergent sequence of data converge to the parity
solution of the limit datum. -/
theorem effective_solutions_tendsto_parity
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
    (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n))) (h : ℕ → VectorL2) (g : VectorL2)
    (hg : HalfTurnVectorAction.U g = g) (hconv : Tendsto h atTop (𝓝 g)) :
    Tendsto (fun r : ℕ => Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) (h r)) atTop
      (𝓝 (ParityMaterialField.solution d 1 (q ^ n) g)) := by
  have h1 := SourcePairedReduction.effective_solution_tendsto q hq n ci d b hb hcar hL h g hconv
  rwa [SourcePairedWallKernelAE.limit_solution_eq_parity q hq n ci d b hb hcar hL
    (ParityMaterialField.solution d 1 (q ^ n) g) g
    (SourcePairedParityClosure.source_invariantAE_of_fixed ci hsym d (q ^ n) hu g hg)
    (SourcePairedParityClosure.parity_solution_equation ci d (q ^ n) hu g)] at h1

omit hsym in
/-- Uniform convergence of the assembled electric plane field along any sequence converging to a
vector with half-turn invariant source. -/
theorem pairedPlaneElectric_tendsto_uniform_seq (u : ℕ → VectorL2) (u0 : VectorL2)
    (hu : Tendsto u atTop (𝓝 u0))
    (hinv : HalfTurnReactionBridgeAE.InvariantAE (SourcePairedWallKernelAE.sourceField ci u0))
    (inc : Maxwell.Field) (ρ0 η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci (u r) inc x i -
        ParityPlaneFields.totalElectric 1 (q ^ n) (DynamicVolume.source ci u0) inc x i‖ ≤ ε := by
  have hA := SourcePairedReactionField.reactionField_tendsto_uniform_compact q hq n ci d b hcar ρ0 u u0 hu
    (ε / 2) (half_pos hε)
  have hB := SourcePairedPlaneCompact.free_electric_tendsto_uniform ci d η hη u u0 hu (ε / 2) (half_pos hε)
  filter_upwards [hA, hB] with r hr hfree x hx hxη i
  have e1 : ((q ^ n) ^ 2 : ℝ) = q ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have e2 : ((q ^ n)⁻¹ ^ 2 : ℝ) = (q ^ (2 * n))⁻¹ := by rw [inv_pow, e1]
  have hl := SourcePairedReactionField.limitField_eq_parity q n ci u0 d.radius d.ballZero hinv x i
  have hr' := hr x hx i
  rw [hl] at hr'
  have key : SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci (u r) inc x i -
        ParityPlaneFields.totalElectric 1 (q ^ n) (DynamicVolume.source ci u0) inc x i =
      (ExteriorContinuity.electric 1 (DynamicVolume.source ci (u r)) x i -
        ExteriorContinuity.electric 1 (DynamicVolume.source ci u0) x i) +
      (SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X (u r) x i -
        ((((q ^ (2 * n) : ℝ) : ℂ) - 1) * ParityPlaneFields.electric true 1
            (DynamicVolume.source ci u0) x i +
          ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * ParityPlaneFields.electric false 1
            (DynamicVolume.source ci u0) x i)) := by
    unfold SourcePairedPlaneCompact.pairedPlaneElectric ParityPlaneFields.totalElectric
    rw [e1, e2]
    push_cast
    ring
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hfree x hxη i) hr'
    _ = ε := by ring

omit hsym in
/-- Uniform convergence of the assembled magnetic plane field along any sequence converging to a
vector with half-turn invariant source. -/
theorem pairedPlaneMagnetic_tendsto_uniform_seq (u : ℕ → VectorL2) (u0 : VectorL2)
    (hu : Tendsto u atTop (𝓝 u0))
    (hinv : HalfTurnReactionBridgeAE.InvariantAE (SourcePairedWallKernelAE.sourceField ci u0))
    (inc : Maxwell.Field) (ρ0 η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci (u r) inc x i -
        ParityPlaneFields.totalMagnetic 1 (q ^ n) (DynamicVolume.source ci u0) inc x i‖ ≤ ε := by
  have e1 : ((q ^ n) ^ 2 : ℝ) = q ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have e2 : ((q ^ n)⁻¹ ^ 2 : ℝ) = (q ^ (2 * n))⁻¹ := by rw [inv_pow, e1]
  have c1 : (((q ^ n) ^ 2 - 1 : ℝ) : ℂ) = ((q ^ (2 * n) : ℝ) : ℂ) - 1 := by
    rw [e1, Complex.ofReal_sub, Complex.ofReal_one]
  have c2 : (((q ^ n)⁻¹ ^ 2 - 1 : ℝ) : ℂ) = (((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1 := by
    rw [e2, Complex.ofReal_sub, Complex.ofReal_one]
  have hM : ∀ ε' : ℝ, 0 < ε' → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖(fun r (x : Space) (i : Fin 3) => SourcePairedPlaneMagnetic.magneticReactionField
          (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
          (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X (u r) x i) r x i -
        ((((q ^ n) ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic true 1
            (DynamicVolume.source ci u0) x i +
          (((q ^ n)⁻¹ ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic false 1
            (DynamicVolume.source ci u0) x i)‖ ≤ ε' := by
    intro ε' hε'
    filter_upwards [SourcePairedPlaneMagnetic.magneticReactionField_tendsto_uniform_compact q hq n ci d b hcar
      ρ0 u u0 hu ε' hε'] with r hr x hx i
    rw [c1, c2, ← SourcePairedPlaneMagnetic.limitMagField_eq_parity q n ci u0 d.radius d.ballZero hinv x i]
    exact hr x hx i
  exact SourcePairedPlaneCompact.pairedPlaneMagnetic_tendsto_of_reaction ci d inc (q ^ n) u u0 hu
    (fun r x i => SourcePairedPlaneMagnetic.magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X (u r) x i) ρ0 η hη hM ε hε

end Sequences

/-! ### Convergence of the total fields of the combined paired devices -/

/-- Eventually in the shell index, the effective datum of the data of the incident field is any
sequence of weighted data of the electric background fields. -/
theorem eventually_effectiveDatum_eq (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (Einc : Maxwell.Field) (fs : ℕ → VectorL2) (fi : VectorL2) (hfi : IsDatum ci Einc fi)
    (h : ℕ → VectorL2)
    (hh : ∀ᶠ r : ℕ in atTop, IsDatum ci (backgroundElectric (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X Einc (fs r)) (h r)) :
    ∀ᶠ r : ℕ in atTop, effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (fs r) fi = h r := by
  filter_upwards [SourcePairedReduction.eventually_inner_radius q hq n b, hh] with r hbR hhr
  exact (effectiveDatum_isDatum (SourcePairedInclusion.shell q hq n r) ci b
    (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
    (SourcePairedInclusion.data q hq n r).X hbR (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
    (shell_hcs q hq n r) (SourcePairedReduction.inclusion_vanish ci d b hcar) Einc (fs r) fi hfi).unique hhr

section Convergence
variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) (hsym : HalfTurnVectorAction.Symmetric ci)
  (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
  (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n)))
  (Einc : Maxwell.Field) (fs : ℕ → VectorL2) (fi : VectorL2)
  (hfs : ∀ r : ℕ, IsDatum (SourcePairedInclusion.shell q hq n r) Einc (fs r)) (hfi : IsDatum ci Einc fi)
  (h : ℕ → VectorL2)
  (hh : ∀ᶠ r : ℕ in atTop, IsDatum ci (backgroundElectric (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).X Einc (fs r)) (h r))
  (g : VectorL2) (hg : HalfTurnVectorAction.U g = g) (hconv : Tendsto h atTop (𝓝 g))
  (ρ0 η : ℝ) (hη : 0 < η)
include hcar hsym hL hu hfs hfi hh hg hconv hη

/-- Uniform convergence on balls at positive distance from the carrier of the total electric fields of
the combined shell-plus-inclusion devices to the total electric field of the parity device with
incident field `Einf`, when the effective data converge to a half-turn fixed vector and the background
electric fields converge uniformly. -/
theorem combined_total_electric_tendsto_uniform (Einf : Maxwell.Field)
    (hbg : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) →
      ∀ i : Fin 3, ‖backgroundElectric (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X Einc (fs r) x i - Einf x i‖ ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖continuousTotalElectric (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
          (SourcePairedInclusion.data q hq n r).X Einc (fs r + fi) x i -
        ParityPlaneFields.totalElectric 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) g)) Einf x i‖ ≤ ε := by
  have hlim := effective_solutions_tendsto_parity q hq n ci d b hb hcar hsym hL hu h g hg hconv
  have hinv := SourcePairedParityClosure.source_invariantAE_of_fixed ci hsym d (q ^ n) hu g hg
  have hseq := pairedPlaneElectric_tendsto_uniform_seq q hq n ci d b hcar _ _ hlim hinv Einf ρ0 η hη
    (ε / 2) (half_pos hε)
  have hci := SourcePairedReduction.inclusion_vanish ci d b hcar
  have hbn : 0 < b := hb
  filter_upwards [hseq, hbg (ε / 2) (half_pos hε), eventually_effectiveDatum_eq q hq n ci d b hcar Einc fs fi hfi h hh,
    SourcePairedReduction.eventually_inner_radius q hq n b,
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0),
    SourcePairedReduction.eventually_effective_isUnit q hq n ci d b hb hcar hL]
    with r h1 h2 hdat hbR hρR hE x hx hxη i
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hbR.le hci
  have hfs0 : StaticCoefficient.sqrtMultiplier ci (fs r) = 0 :=
    sqrtMultiplier_isDatum_zero ci (SourcePairedInclusion.shell q hq n r) hd.symm Einc (fs r) (hfs r)
  have hfi0 : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) fi = 0 :=
    sqrtMultiplier_isDatum_zero (SourcePairedInclusion.shell q hq n r) ci hd Einc fi hfi
  have hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R := hx.trans_lt hρR
  have hid := combined_total_electric_eq q hq n r ci b hbR hci d hE Einc (fs r) fi hfi0 hfs0 η hη x hxR hxη i
  rw [hid, hdat]
  have e : SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
      (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) (h r))
      (backgroundElectric (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
        Einc (fs r)) x i =
      SourcePairedPlaneCompact.pairedPlaneElectric q hq n r ci
        (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) (h r)) Einf x i +
      (backgroundElectric (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
        Einc (fs r) x i - Einf x i) := by
    unfold SourcePairedPlaneCompact.pairedPlaneElectric
    ring
  rw [e, add_sub_right_comm]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 x hx hxη i) (h2 x hx hxη i)
    _ = ε := by ring

/-- The magnetic analogue: `Hinc` is the incident magnetic field, while the data still come from the
incident electric field `Einc`. -/
theorem combined_total_magnetic_tendsto_uniform (Hinc Hinf : Maxwell.Field)
    (hbg : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) →
      ∀ i : Fin 3, ‖backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X Hinc (fs r) x i - Hinf x i‖ ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖continuousTotalMagnetic (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
          (SourcePairedInclusion.data q hq n r).X Hinc (fs r + fi) x i -
        ParityPlaneFields.totalMagnetic 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) g)) Hinf x i‖ ≤ ε := by
  have hlim := effective_solutions_tendsto_parity q hq n ci d b hb hcar hsym hL hu h g hg hconv
  have hinv := SourcePairedParityClosure.source_invariantAE_of_fixed ci hsym d (q ^ n) hu g hg
  have hseq := pairedPlaneMagnetic_tendsto_uniform_seq q hq n ci d b hcar _ _ hlim hinv Hinf ρ0 η hη
    (ε / 2) (half_pos hε)
  have hci := SourcePairedReduction.inclusion_vanish ci d b hcar
  filter_upwards [hseq, hbg (ε / 2) (half_pos hε), eventually_effectiveDatum_eq q hq n ci d b hcar Einc fs fi hfi h hh,
    SourcePairedReduction.eventually_inner_radius q hq n b,
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop ρ0),
    SourcePairedReduction.eventually_effective_isUnit q hq n ci d b hb hcar hL]
    with r h1 h2 hdat hbR hρR hE x hx hxη i
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hbR.le hci
  have hfs0 : StaticCoefficient.sqrtMultiplier ci (fs r) = 0 :=
    sqrtMultiplier_isDatum_zero ci (SourcePairedInclusion.shell q hq n r) hd.symm Einc (fs r) (hfs r)
  have hfi0 : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) fi = 0 :=
    sqrtMultiplier_isDatum_zero (SourcePairedInclusion.shell q hq n r) ci hd Einc fi hfi
  have hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R := hx.trans_lt hρR
  have hid := combined_total_magnetic_eq q hq n r ci b hbR hci d hE Hinc (fs r) fi hfi0 hfs0 η hη x hxR hxη i
  rw [hid, hdat]
  have e : SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci
      (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) (h r))
      (backgroundMagnetic (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
        Hinc (fs r)) x i =
      SourcePairedPlaneMagnetic.pairedPlaneMagnetic q hq n r ci
        (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) (h r)) Hinf x i +
      (backgroundMagnetic (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
        Hinc (fs r) x i - Hinf x i) := by
    unfold SourcePairedPlaneMagnetic.pairedPlaneMagnetic
    ring
  rw [e, add_sub_right_comm]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (h1 x hx hxη i) (h2 x hx hxη i)
    _ = ε := by ring

end Convergence

section Canonical
variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) (hsym : HalfTurnVectorAction.Symmetric ci)
  (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
  (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n)))
  (Einc : Maxwell.Field) (fs : ℕ → VectorL2) (fi : VectorL2)
  (hfs : ∀ r : ℕ, IsDatum (SourcePairedInclusion.shell q hq n r) Einc (fs r)) (hfi : IsDatum ci Einc fi)
  (g : VectorL2) (hg : HalfTurnVectorAction.U g = g)
  (hconv : Tendsto (fun r : ℕ => effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
    (SourcePairedInclusion.data q hq n r).X (fs r) fi) atTop (𝓝 g))
  (ρ0 η : ℝ) (hη : 0 < η)
include hcar hsym hL hu hfs hfi hg hconv hη

/-- The same with the effective datum `fi + Si T Ss r fs` itself as the convergent sequence of data. -/
theorem combined_total_electric_tendsto_uniform_canonical (Einf : Maxwell.Field)
    (hbg : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) →
      ∀ i : Fin 3, ‖backgroundElectric (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X Einc (fs r) x i - Einf x i‖ ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖continuousTotalElectric (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
          (SourcePairedInclusion.data q hq n r).X Einc (fs r + fi) x i -
        ParityPlaneFields.totalElectric 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) g)) Einf x i‖ ≤ ε :=
  combined_total_electric_tendsto_uniform q hq n ci d b hb hcar hsym hL hu Einc fs fi hfs hfi
    (fun r => effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (fs r) fi)
    ((SourcePairedReduction.eventually_inner_radius q hq n b).mono (fun r hbR =>
      effectiveDatum_isDatum (SourcePairedInclusion.shell q hq n r) ci b
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
        (SourcePairedInclusion.data q hq n r).X hbR (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
        (shell_hcs q hq n r) (SourcePairedReduction.inclusion_vanish ci d b hcar) Einc (fs r) fi hfi))
    g hg hconv ρ0 η hη Einf hbg ε hε

/-- The magnetic analogue with the effective datum as the convergent sequence of data. -/
theorem combined_total_magnetic_tendsto_uniform_canonical (Hinc Hinf : Maxwell.Field)
    (hbg : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) →
      ∀ i : Fin 3, ‖backgroundMagnetic (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X Hinc (fs r) x i - Hinf x i‖ ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖continuousTotalMagnetic (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci)
          (SourcePairedInclusion.data q hq n r).X Hinc (fs r + fi) x i -
        ParityPlaneFields.totalMagnetic 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) g)) Hinf x i‖ ≤ ε :=
  combined_total_magnetic_tendsto_uniform q hq n ci d b hb hcar hsym hL hu Einc fs fi hfs hfi
    (fun r => effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (fs r) fi)
    ((SourcePairedReduction.eventually_inner_radius q hq n b).mono (fun r hbR =>
      effectiveDatum_isDatum (SourcePairedInclusion.shell q hq n r) ci b
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X
        (SourcePairedInclusion.data q hq n r).X hbR (SourcePairedInclusion.radii_ordered q hq n r) le_rfl
        (shell_hcs q hq n r) (SourcePairedReduction.inclusion_vanish ci d b hcar) Einc (fs r) fi hfi))
    g hg hconv ρ0 η hη Hinc Hinf hbg ε hε

end Canonical

end OQ14.SourcePairedPlaneIdentification
#print axioms OQ14.SourcePairedPlaneIdentification.source_add_ae
#print axioms OQ14.SourcePairedPlaneIdentification.source_smul_ae
#print axioms OQ14.SourcePairedPlaneIdentification.response_integrand_integrable
#print axioms OQ14.SourcePairedPlaneIdentification.kernelFunctional_apply
#print axioms OQ14.SourcePairedPlaneIdentification.magneticDyadic_bound
#print axioms OQ14.SourcePairedPlaneIdentification.measurable_magneticDyadic
#print axioms OQ14.SourcePairedPlaneIdentification.magneticEvaluation_apply
#print axioms OQ14.SourcePairedPlaneIdentification.reactionField_eq_free
#print axioms OQ14.SourcePairedPlaneIdentification.magnetic_annulus_bound
#print axioms OQ14.SourcePairedPlaneIdentification.magnetic_annulus_bound_nonneg
#print axioms OQ14.SourcePairedPlaneIdentification.magneticReactionField_eq_free
#print axioms OQ14.SourcePairedPlaneIdentification.freeDatum_continuousOn
#print axioms OQ14.SourcePairedPlaneIdentification.freeDatum_integrable
#print axioms OQ14.SourcePairedPlaneIdentification.freeDatum_integral
#print axioms OQ14.SourcePairedPlaneIdentification.combined_equation
#print axioms OQ14.SourcePairedPlaneIdentification.solution_split
#print axioms OQ14.SourcePairedPlaneIdentification.Ss_inclPart
#print axioms OQ14.SourcePairedPlaneIdentification.Si_shellPart
#print axioms OQ14.SourcePairedPlaneIdentification.Ss_solution
#print axioms OQ14.SourcePairedPlaneIdentification.Si_solution
#print axioms OQ14.SourcePairedPlaneIdentification.shellPart_equation
#print axioms OQ14.SourcePairedPlaneIdentification.shellPart_eq
#print axioms OQ14.SourcePairedPlaneIdentification.inclPart_equation
#print axioms OQ14.SourcePairedPlaneIdentification.IsDatum.unique
#print axioms OQ14.SourcePairedPlaneIdentification.isDatum_add
#print axioms OQ14.SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero
#print axioms OQ14.SourcePairedPlaneIdentification.source_add_disjoint
#print axioms OQ14.SourcePairedPlaneIdentification.source_congr_of_sqrt
#print axioms OQ14.SourcePairedPlaneIdentification.effectiveDatum_isDatum
#print axioms OQ14.SourcePairedPlaneIdentification.response_sum_split
#print axioms OQ14.SourcePairedPlaneIdentification.combined_source_split
#print axioms OQ14.SourcePairedPlaneIdentification.shell_hcs
#print axioms OQ14.SourcePairedPlaneIdentification.pairedPlaneElectric_eq_free
#print axioms OQ14.SourcePairedPlaneIdentification.pairedPlaneMagnetic_eq_free
#print axioms OQ14.SourcePairedPlaneIdentification.inclPart_eq_effective
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_electric_eq
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_magnetic_eq
#print axioms OQ14.SourcePairedPlaneIdentification.combined_solution_blocks
#print axioms OQ14.SourcePairedPlaneIdentification.physicalCoordinate_add
#print axioms OQ14.SourcePairedPlaneIdentification.magnetic_total_eq
#print axioms OQ14.SourcePairedPlaneIdentification.scattered_ae_annulus
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_electric_ae
#print axioms OQ14.SourcePairedPlaneIdentification.combined_totalMagnetic_eq
#print axioms OQ14.SourcePairedPlaneIdentification.effective_solutions_tendsto_parity
#print axioms OQ14.SourcePairedPlaneIdentification.pairedPlaneElectric_tendsto_uniform_seq
#print axioms OQ14.SourcePairedPlaneIdentification.pairedPlaneMagnetic_tendsto_uniform_seq
#print axioms OQ14.SourcePairedPlaneIdentification.eventually_effectiveDatum_eq
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_electric_tendsto_uniform
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_magnetic_tendsto_uniform
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_electric_tendsto_uniform_canonical
#print axioms OQ14.SourcePairedPlaneIdentification.combined_total_magnetic_tendsto_uniform_canonical
