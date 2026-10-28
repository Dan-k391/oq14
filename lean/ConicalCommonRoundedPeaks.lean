import ConicalCommonRungeNonzero
import CommonTipRounding

/-! One fixed common angular input through one common rounded material sequence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.ConicalCommonRoundedPeaks
open MeasureTheory Set Metric Filter OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

def coefficient := ConicalCommonBaseline.common p a center B hB hcontrast ha hsep

def rounded (n : ℕ) := CommonTipRounding.rounded center (coefficient p a center B hB hcontrast ha hsep) n

def electric (R k : ℝ) (n : ℕ) (I : ConicalEntireGauge.Incident k) : Maxwell.Field :=
  MaterialField.total (rounded p a center B hB hcontrast ha hsep n) k
    (ConicalMaterialRunge.solutionOperator (rounded p a center B hB hcontrast ha hsep n) k R
      (ConicalEntireGauge.restricted R I)) I.E

def magnetic (R k : ℝ) (n : ℕ) (I : ConicalEntireGauge.Incident k) : Maxwell.Field :=
  MaterialMaxwell.totalMagnetic (rounded p a center B hB hcontrast ha hsep n) k
    (ConicalMaterialRunge.solutionOperator (rounded p a center B hB hcontrast ha hsep n) k R
      (ConicalEntireGauge.restricted R I)) I.H

omit [DecidableEq ι] in
theorem support (R : ℝ) (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R) :
    ∀ n x, x ∉ closedBall (0 : Space) R → (rounded p a center B hB hcontrast ha hsep n).value (VectorFourier.coordinateMap x) = 0 :=
  fun n => CommonTipRounding.rounded_support center _ n R (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR)

omit [DecidableEq ι] in
theorem ballField_tendsto (R k : ℝ) (hR0 : 0 ≤ R)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius (coefficient p a center B hB hcontrast ha hsep).bound R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R) (I : ConicalEntireGauge.Incident k) :
    Tendsto (fun n => ConicalMaterialRunge.totalOperator (rounded p a center B hB hcontrast ha hsep n) k R
      (ConicalEntireGauge.restricted R I)) atTop
      (𝓝 (ConicalMaterialRunge.totalOperator (coefficient p a center B hB hcontrast ha hsep) k R
        (ConicalEntireGauge.restricted R I))) := by
  let g := ConicalEntireGauge.restricted R I
  let F := ConicalBallExtension.vector R g
  have hleft : ConicalBallRestriction.vector R F = g := ConicalBallRestriction.extension_leftInverse R g
  have hn (n : ℕ) : ConicalMaterialRunge.totalOperator (rounded p a center B hB hcontrast ha hsep n) k R g =
      ConicalBallRestriction.vector R (MaterialVolumeLimit.volumeField (rounded p a center B hB hcontrast ha hsep n) k R F) := by
    have h := ConicalSeparatedIllumination.total_restriction (rounded p a center B hB hcontrast ha hsep n) k R F
      (support p a center B hB hcontrast ha hsep R hR n)
    rwa [hleft] at h
  have h0 : ConicalMaterialRunge.totalOperator (coefficient p a center B hB hcontrast ha hsep) k R g =
      ConicalBallRestriction.vector R (MaterialVolumeLimit.volumeField (coefficient p a center B hB hcontrast ha hsep) k R F) := by
    have h := ConicalSeparatedIllumination.total_restriction (coefficient p a center B hB hcontrast ha hsep) k R F
      (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR)
    rwa [hleft] at h
  have hf : (fun n => ConicalMaterialRunge.totalOperator (rounded p a center B hB hcontrast ha hsep n) k R g) =
      fun n => ConicalBallRestriction.vector R (MaterialVolumeLimit.volumeField (rounded p a center B hB hcontrast ha hsep n) k R F) := funext hn
  change Tendsto (fun n => ConicalMaterialRunge.totalOperator (rounded p a center B hB hcontrast ha hsep n) k R g) atTop _
  rw [hf,h0]
  exact ((ConicalBallRestriction.vector R).continuous.tendsto _).comp
    (CommonTipRounding.volumeField_tendsto center (coefficient p a center B hB hcontrast ha hsep) k R hR0 hk F)

omit [DecidableEq ι] in
theorem rounded_maxwell (R k : ℝ) (hR0 : 0 ≤ R)
    (hk : |k| ≤ MaterialVolumeLimit.commonRadius (coefficient p a center B hB hcontrast ha hsep).bound R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (n : ℕ) (I : ConicalEntireGauge.Incident k) :
    MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (rounded p a center B hB hcontrast ha hsep n))
      (electric p a center B hB hcontrast ha hsep R k n I) (magnetic p a center B hB hcontrast ha hsep R k n I) := by
  have hsmall : |k| ≤ DynamicStaticLimit.frequencyRadius (rounded p a center B hB hcontrast ha hsep n) R :=
    hk.trans (MaterialVolumeLimit.commonRadius_le _ _ _ le_rfl)
  exact MaterialMaxwell.volume_solution_testMaxwell _ k R _ _ I.E I.H (support p a center B hB hcontrast ha hsep R hR n)
    (ConicalMaterialRunge.weighted_actual _ R _ _ (support p a center B hB hcontrast ha hsep R hR n) (ConicalEntireGauge.restricted_ae R I))
    (ConicalMaterialRunge.solution_equation _ k R hR0 hsmall _)
    (fun j => (I.smoothE j).continuous.locallyIntegrable) (fun j => (I.smoothH j).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H (fun j => (I.smoothE j).of_le (by simp))
      (fun j => (I.smoothH j).of_le (by simp)) I.maxwell)

theorem volumeField_actual (c : StaticCoefficient.Coefficient) (R k : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (I : ConicalEntireGauge.Incident k) (j : Fin 3) :
    physicalCoordinate (MaterialVolumeLimit.volumeField c k R
      (ConicalBallExtension.vector R (ConicalEntireGauge.restricted R I))) j
        =ᵐ[volume.restrict (closedBall (0 : Space) R)]
      fun x => MaterialField.total c k (ConicalMaterialRunge.solutionOperator c k R (ConicalEntireGauge.restricted R I)) I.E x j := by
  have he := ConicalSeparatedIllumination.total_restriction c k R
    (ConicalBallExtension.vector R (ConicalEntireGauge.restricted R I)) hc
  rw [ConicalBallRestriction.extension_leftInverse] at he
  have h1 := ConicalBallRestriction.vector_ae R (MaterialVolumeLimit.volumeField c k R
    (ConicalBallExtension.vector R (ConicalEntireGauge.restricted R I))) j
  rw [← he] at h1
  exact h1.symm.trans (ConicalMaterialRunge.total_ae c k R _ I.E hc (ConicalEntireGauge.restricted_ae R I) j)

omit [DecidableEq ι] in
theorem limiting_unbounded (i : ι) (R k b r : ℝ) (hR0 : 0 ≤ R) (hk : 0 < k)
    (hb0 : 0 < b) (hb : b ≤ a i) (hr0 : 0 < r) (hrb : r ≤ b)
    (hai : a i < (p i).cutoff.rIn) (hν : (p i).exponent < 1)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (d : Input) (hq : ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k b hR0 hk.ne' hb hai hfreq hR hb0 hν d ≠ 0) :
    ∃ j : Fin 3, ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (center i) r),
      ‖physicalCoordinate (MaterialVolumeLimit.volumeField (coefficient p a center B hB hcontrast ha hsep) k R
        (ConicalBallExtension.vector R (ConicalEntireGauge.restricted R (FiniteAngularHerglotz.incident k d)))) j x‖ ≤ M := by
  let I := FiniteAngularHerglotz.incident k d
  let s := ConicalCommonEntire.system p a center B hB hcontrast ha hsep i R k b hR0 hk.ne' hb hai hfreq hR I
  let E : Maxwell.Field := fun x => ConicalCommonEntire.electric p a center B hB hcontrast ha hsep R k I (center i+x)
  have hu := ConicalFixedInputTransfer.not_essentially_bounded (p i) b hν s E
    (ConicalCommonEntire.system_actual p a center B hB hcontrast ha hsep i R k b hR0 hk.ne' hb hai hfreq hR I)
    (ConicalIntrinsicCoefficient.coefficient s hb0 (hb.trans_lt hai) hν) hq
    (ConicalIntrinsicCoefficient.coefficient_spec s hb0 (hb.trans_lt hai) hν) r hr0 hrb
  obtain ⟨j,hj⟩ := ConicalVolumePeaks.coordinate_unbounded E (ball (0 : Space) r) hu
  refine ⟨j,?_⟩
  rintro ⟨M,hM⟩
  apply hj
  refine ⟨M,?_⟩
  have hM' := (ae_restrict_iff' isOpen_ball.measurableSet).mp hM
  have hA := (ae_restrict_iff' measurableSet_closedBall).mp
    (volumeField_actual (coefficient p a center B hB hcontrast ha hsep) R k
      (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR) I j)
  have ht := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae (hM'.and hA)
  filter_upwards [ae_restrict_of_ae ht, ae_restrict_mem isOpen_ball.measurableSet] with x hx hxball
  have hm : x+center i ∈ ball (center i) r := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hxball
  have hmateri : x+center i ∈ ConicalCommonMaterial.materialBall a center i := by
    have hn : ‖x‖ < r := by simpa using hxball
    simp only [ConicalCommonMaterial.materialBall, mem_closedBall, dist_eq_norm, add_sub_cancel_right]
    exact (hn.trans_le (hrb.trans hb)).le
  have hmem := hR i (ConicalCommonMaterial.material_subset_outer p a center ha i hmateri)
  have hh := hx.1 hm
  rw [hx.2 hmem] at hh
  simpa only [E, ConicalCommonEntire.electric, ConicalCommonEntire.solution, add_comm] using hh

omit [DecidableEq ι] in
theorem eventually_high (i : ι) (R k b r : ℝ) (hR0 : 0 ≤ R) (hk : 0 < k)
    (hb0 : 0 < b) (hb : b ≤ a i) (hr0 : 0 < r) (hrb : r ≤ b)
    (hai : a i < (p i).cutoff.rIn) (hν : (p i).exponent < 1)
    (hcommon : |k| ≤ MaterialVolumeLimit.commonRadius (coefficient p a center B hB hcontrast ha hsep).bound R)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (d : Input) (hq : ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k b hR0 hk.ne' hb hai hfreq hR hb0 hν d ≠ 0) :
    ∃ j : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
      0 < (volume.restrict (ball (center i) r)) {x | M < ‖electric p a center B hB hcontrast ha hsep R k n (FiniteAngularHerglotz.incident k d) x j‖} := by
  obtain ⟨j,hj⟩ := limiting_unbounded p a center B hB hcontrast ha hsep i R k b r hR0 hk hb0 hb hr0 hrb hai hν hfreq hR d hq
  let I := FiniteAngularHerglotz.incident k d
  let F := ConicalBallExtension.vector R (ConicalEntireGauge.restricted R I)
  have hlim := ((ConicalVolumePeaks.physicalCoordinateCLM j).continuous.tendsto _).comp
    (CommonTipRounding.volumeField_tendsto center (coefficient p a center B hB hcontrast ha hsep) k R hR0 hcommon F)
  refine ⟨j, fun M => ?_⟩
  have he := L2PeakPreservation.eventually_exceeds (ball (center i) r) _ _ hlim hj M
  filter_upwards [he] with n hn
  have hactual := volumeField_actual (rounded p a center B hB hcontrast ha hsep n) R k
    (support p a center B hB hcontrast ha hsep R hR n) I j
  have hsubset : ball (center i) r ⊆ closedBall (0 : Space) R := by
    intro x hx
    have hm : x ∈ ConicalCommonMaterial.materialBall a center i := by
      exact closedBall_subset_closedBall (hrb.trans hb) (ball_subset_closedBall hx)
    exact hR i (ConicalCommonMaterial.material_subset_outer p a center ha i hm)
  have hact := ae_restrict_of_ae_restrict_of_subset hsubset hactual
  have hn' : ¬∀ᵐ x : Space ∂volume.restrict (ball (center i) r),
      ‖electric p a center B hB hcontrast ha hsep R k n I x j‖ ≤ M := by
    intro hh
    apply hn
    filter_upwards [hh,hact] with x hh hact
    change ‖physicalCoordinate (MaterialVolumeLimit.volumeField (rounded p a center B hB hcontrast ha hsep n) k R F) j x‖ ≤ M
    rw [hact]
    exact hh
  rw [ae_iff] at hn'
  exact pos_iff_ne_zero.mpr (by simpa only [not_le] using hn')

theorem one_input_rounded_superlevels [Nonempty ι] (R T : ℝ) (b : ι → ℝ)
    (hR0 : 0 ≤ R) (hRT : R ≤ T) (hb0 : ∀ i, 0 < b i) (hb : ∀ i, b i < a i)
    (hν : ∀ i, (p i).exponent < 1) (hra : ∀ i, 0 ≤ a i)
    (hgeom : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j))
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hai : ∀ i, a i < (p i).cutoff.rIn) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, ∀ (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p a center B hB hcontrast ha hsep) R)
        (d : Input), d ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k d) atTop (𝓝 1) ∧
        (∀ i, ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k (b i) hR0 hk.ne'
          (hb i).le (hai i) hfreq hR (hb0 i) (hν i) d ≠ 0) ∧
        (∀ n : ℕ, MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (rounded p a center B hB hcontrast ha hsep n))
          (electric p a center B hB hcontrast ha hsep R k n (FiniteAngularHerglotz.incident k d))
          (magnetic p a center B hB hcontrast ha hsep R k n (FiniteAngularHerglotz.incident k d))) ∧
        ∀ i : ι, ∀ r : ℝ, 0 < r → r ≤ b i → ∃ j : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
          0 < (volume.restrict (ball (center i) r))
            {x | M < ‖electric p a center B hB hcontrast ha hsep R k n (FiniteAngularHerglotz.incident k d) x j‖} := by
  obtain ⟨δ,hδ,hinput⟩ := ConicalCommonRungeNonzero.one_normalized_illumination p a center B hB hcontrast ha hsep
    R T b hR0 hRT hb0 hb hν hra hgeom hKR hR hai
  let c := coefficient p a center B hB hcontrast ha hsep
  have hc0 : 0 ≤ c.bound := StaticCoefficient.bound_nonnegative c
  have hrad := MaterialVolumeLimit.commonRadius_positive c.bound R hc0
  refine ⟨min δ (MaterialVolumeLimit.commonRadius c.bound R), lt_min hδ hrad, ?_⟩
  intro k hk hkd
  obtain ⟨hfreq,d,hd,hpower,hq,hm⟩ := hinput k hk (hkd.trans_le (min_le_left _ _))
  have hcommon : |k| ≤ MaterialVolumeLimit.commonRadius c.bound R := by
    rw [abs_of_pos hk]
    exact (hkd.trans_le (min_le_right _ _)).le
  refine ⟨hfreq,d,hd,hpower,hq,fun n => rounded_maxwell p a center B hB hcontrast ha hsep R k hR0 hcommon hR n _,?_⟩
  intro i r hr0 hrb
  exact eventually_high p a center B hB hcontrast ha hsep i R k (b i) r hR0 hk (hb0 i) (hb i).le hr0 hrb
    (hai i) (hν i) hcommon hfreq hR d (hq i)

end OQ14.ConicalCommonRoundedPeaks
#print axioms OQ14.ConicalCommonRoundedPeaks.support
#print axioms OQ14.ConicalCommonRoundedPeaks.ballField_tendsto
#print axioms OQ14.ConicalCommonRoundedPeaks.rounded_maxwell
#print axioms OQ14.ConicalCommonRoundedPeaks.volumeField_actual
#print axioms OQ14.ConicalCommonRoundedPeaks.limiting_unbounded
#print axioms OQ14.ConicalCommonRoundedPeaks.eventually_high
#print axioms OQ14.ConicalCommonRoundedPeaks.one_input_rounded_superlevels
