import CommonTipRounding
import ConicalFixedInputTransfer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace OQ14.CommonRoundedTransfer
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space
variable {ι : Type*} [Fintype ι]

def electric (center : ι → Space) (c : StaticCoefficient.Coefficient) (R k : ℝ) (n : ℕ)
    (I : ConicalEntireGauge.Incident k) : Field :=
  MaterialField.total (CommonTipRounding.rounded center c n) k
    (ConicalMaterialRunge.solutionOperator (CommonTipRounding.rounded center c n) k R
      (ConicalEntireGauge.restricted R I)) I.E

def sharpElectric (c : StaticCoefficient.Coefficient) (R k : ℝ) (I : ConicalEntireGauge.Incident k) : Field :=
  MaterialField.total c k (ConicalMaterialRunge.solutionOperator c k R (ConicalEntireGauge.restricted R I)) I.E

theorem total_tendsto (center : ι → Space) (c : StaticCoefficient.Coefficient) (R k : ℝ)
    (hR : 0 ≤ R) (hk : |k| ≤ MaterialVolumeLimit.commonRadius c.bound R)
    (hcs : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (I : ConicalEntireGauge.Incident k) :
    Tendsto (fun n => ConicalMaterialRunge.totalOperator (CommonTipRounding.rounded center c n) k R
      (ConicalEntireGauge.restricted R I)) atTop
      (𝓝 (ConicalMaterialRunge.totalOperator c k R (ConicalEntireGauge.restricted R I))) := by
  let g := ConicalEntireGauge.restricted R I
  let I' := ConicalBallExtension.vector R g
  have hleft : ConicalBallRestriction.vector R I'=g := ConicalBallRestriction.extension_leftInverse R g
  have hn (n : ℕ) : ConicalMaterialRunge.totalOperator (CommonTipRounding.rounded center c n) k R g =
      ConicalBallRestriction.vector R (MaterialVolumeLimit.volumeField (CommonTipRounding.rounded center c n) k R I') := by
    have h := ConicalSeparatedIllumination.total_restriction (CommonTipRounding.rounded center c n) k R I'
      (CommonTipRounding.rounded_support center c n R hcs)
    rwa [hleft] at h
  have h0 : ConicalMaterialRunge.totalOperator c k R g =
      ConicalBallRestriction.vector R (MaterialVolumeLimit.volumeField c k R I') := by
    have h := ConicalSeparatedIllumination.total_restriction c k R I' hcs
    rwa [hleft] at h
  change Tendsto (fun n => ConicalMaterialRunge.totalOperator (CommonTipRounding.rounded center c n) k R g) atTop
    (𝓝 (ConicalMaterialRunge.totalOperator c k R g))
  simp_rw [hn,h0]
  exact (ConicalBallRestriction.vector R).continuous.tendsto _ |>.comp
    (CommonTipRounding.volumeField_tendsto center c k R hR hk I')

theorem eventually_superlevel (center : ι → Space) (c : StaticCoefficient.Coefficient) (R k : ℝ)
    (hR : 0 ≤ R) (hk : |k| ≤ MaterialVolumeLimit.commonRadius c.bound R)
    (hcs : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (I : ConicalEntireGauge.Incident k) (S : Set Space) (hS : S ⊆ closedBall (0 : Space) R)
    (j : Fin 3) (hu : ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict S, ‖sharpElectric c R k I x j‖ ≤ M)
    (M : ℝ) : ∀ᶠ n : ℕ in atTop, 0 < (volume.restrict S) {x | M < ‖electric center c R k n I x j‖} := by
  let g : ℕ → ScalarBall R := fun n => ConicalMaterialRunge.totalOperator (CommonTipRounding.rounded center c n) k R
    (ConicalEntireGauge.restricted R I) j
  let g0 : ScalarBall R := ConicalMaterialRunge.totalOperator c k R (ConicalEntireGauge.restricted R I) j
  have ht : Tendsto g atTop (𝓝 g0) :=
    ((PiLp.proj 2 (𝕜 := ℂ) (fun _ : Fin 3 => ScalarBall R) j).continuous.tendsto _).comp
      (total_tendsto center c R k hR hk hcs I)
  have hu' : ¬∃ M : ℝ, ∀ᵐ x : Space ∂(volume.restrict (closedBall (0 : Space) R)).restrict S, ‖g0 x‖ ≤ M := by
    rintro ⟨M,hM⟩
    apply hu
    refine ⟨M,?_⟩
    rw [Measure.restrict_restrict_of_subset hS] at hM
    filter_upwards [hM, ae_restrict_of_ae_restrict_of_subset hS
      (ConicalMaterialRunge.total_ae c k R _ I.E hcs (ConicalEntireGauge.restricted_ae R I) j)] with x hb he
    change (g0 : Space → ℂ) x = sharpElectric c R k I x j at he
    rw [← he]
    exact hb
  filter_upwards [L2PeakPreservation.eventually_exceeds S g g0 ht hu' M] with n hn
  have hnb : ¬∀ᵐ x : Space ∂volume.restrict S, ‖electric center c R k n I x j‖ ≤ M := by
    intro h
    apply hn
    rw [Measure.restrict_restrict_of_subset hS]
    filter_upwards [h, ae_restrict_of_ae_restrict_of_subset hS
      (ConicalMaterialRunge.total_ae (CommonTipRounding.rounded center c n) k R _ I.E
        (CommonTipRounding.rounded_support center c n R hcs) (ConicalEntireGauge.restricted_ae R I) j)] with x hb he
    change (g n : Space → ℂ) x = electric center c R k n I x j at he
    rw [he]
    exact hb
  rw [ae_iff] at hnb
  exact pos_iff_ne_zero.mpr (by simpa only [not_le] using hnb)
def magnetic (center : ι → Space) (c : StaticCoefficient.Coefficient) (R k : ℝ) (n : ℕ)
    (I : ConicalEntireGauge.Incident k) : Field :=
  MaterialMaxwell.totalMagnetic (CommonTipRounding.rounded center c n) k
    (ConicalMaterialRunge.solutionOperator (CommonTipRounding.rounded center c n) k R
      (ConicalEntireGauge.restricted R I)) I.H

theorem rounded_maxwell (center : ι → Space) (c : StaticCoefficient.Coefficient) (R k : ℝ)
    (hR : 0 ≤ R) (hk : |k| ≤ MaterialVolumeLimit.commonRadius c.bound R)
    (hcs : ∀ x : Space, x ∉ closedBall (0 : Space) R → c.value (VectorFourier.coordinateMap x)=0)
    (n : ℕ) (I : ConicalEntireGauge.Incident k) :
    MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (CommonTipRounding.rounded center c n))
      (electric center c R k n I) (magnetic center c R k n I) :=
  MaterialMaxwell.volume_solution_testMaxwell (CommonTipRounding.rounded center c n) k R
    (ConicalMaterialRunge.solutionOperator (CommonTipRounding.rounded center c n) k R (ConicalEntireGauge.restricted R I))
    (ConicalBallExtension.weighted (CommonTipRounding.rounded center c n) R (ConicalEntireGauge.restricted R I))
    I.E I.H (CommonTipRounding.rounded_support center c n R hcs)
    (ConicalMaterialRunge.weighted_actual _ R _ _ (CommonTipRounding.rounded_support center c n R hcs)
      (ConicalEntireGauge.restricted_ae R I))
    (ConicalMaterialRunge.solution_equation _ k R hR
      (hk.trans (MaterialVolumeLimit.commonRadius_le (CommonTipRounding.rounded center c n) c.bound R (by rfl))) _)
    (fun i => (I.smoothE i).continuous.locallyIntegrable)
    (fun i => (I.smoothH i).continuous.locallyIntegrable)
    (MaterialMaxwell.classical_vacuum_testMaxwell k I.E I.H
      (fun i => (I.smoothE i).of_le (by simp)) (fun i => (I.smoothH i).of_le (by simp)) I.maxwell)
theorem sharp_unbounded_at_tip {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ) (center : ι → Space)
    (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i) (ConicalCommonMaterial.outer p center j))
    (i : ι) (R k b r : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b ≤ a i) (hb0 : 0 < b)
    (hai : a i < (p i).cutoff.rIn) (hν : (p i).exponent < 1)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) (hq : ConicalIntrinsicCoefficient.coefficient
      (ConicalCommonEntire.system p a center B hB hcontrast ha hsep i R k b hR0 hk hb hai hfreq hR I)
      hb0 (hb.trans_lt hai) hν ≠ 0) (hr : 0 < r) (hrb : r ≤ b) :
    ¬∃ M : ℝ, ∀ᵐ x : Space ∂volume.restrict (ball (center i) r),
      ‖sharpElectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R k I x‖ ≤ M := by
  let s := ConicalCommonEntire.system p a center B hB hcontrast ha hsep i R k b hR0 hk hb hai hfreq hR I
  have hun := ConicalFixedInputTransfer.not_essentially_bounded (p i) b hν s
    (fun x => sharpElectric (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R k I (center i+x))
    (fun j => ConicalCommonEntire.system_actual p a center B hB hcontrast ha hsep i R k b hR0 hk hb hai hfreq hR I j)
    (ConicalIntrinsicCoefficient.coefficient s hb0 (hb.trans_lt hai) hν) hq
    (ConicalIntrinsicCoefficient.coefficient_spec s hb0 (hb.trans_lt hai) hν) r hr hrb
  intro h
  obtain ⟨M,hM⟩ := h
  apply hun
  refine ⟨M,?_⟩
  have hm := (ae_restrict_iff' measurableSet_ball).mp hM
  have ht := (measurePreserving_add_right (volume : Measure Space) (center i)).quasiMeasurePreserving.ae hm
  filter_upwards [ae_restrict_of_ae ht, ae_restrict_mem measurableSet_ball] with x hx hxb
  have hxc : x+center i ∈ ball (center i) r := by
    simpa [mem_ball,dist_eq_norm,add_sub_cancel_right] using hxb
  simpa only [add_comm] using hx hxc
theorem tip_superlevels {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ConicalStaticVolume.Data) (a : ι → ℝ) (center : ι → Space)
    (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i) (ConicalCommonMaterial.outer p center j))
    (i : ι) (R k b r : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : b ≤ a i) (hb0 : 0 < b)
    (hai : a i < (p i).cutoff.rIn) (hν : (p i).exponent < 1)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hcr : |k| ≤ MaterialVolumeLimit.commonRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep).bound R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) (hq : ConicalIntrinsicCoefficient.coefficient
      (ConicalCommonEntire.system p a center B hB hcontrast ha hsep i R k b hR0 hk hb hai hfreq hR I)
      hb0 (hb.trans_lt hai) hν ≠ 0) (hr : 0 < r) (hrb : r ≤ b) :
    ∃ j : Fin 3, ∀ M : ℝ, ∀ᶠ n : ℕ in atTop,
      0 < (volume.restrict (ball (center i) r)) {x |
        M < ‖electric center (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R k n I x j‖} := by
  let c := ConicalCommonBaseline.common p a center B hB hcontrast ha hsep
  have hu := sharp_unbounded_at_tip p a center B hB hcontrast ha hsep i R k b r hR0 hk hb hb0 hai hν hfreq hR I hq hr hrb
  obtain ⟨j,hj⟩ := ConicalVolumePeaks.coordinate_unbounded (sharpElectric c R k I) (ball (center i) r) hu
  have hS : ball (center i) r ⊆ closedBall (0 : Space) R := by
    intro x hx
    have hm : x ∈ ConicalCommonMaterial.materialBall a center i :=
      closedBall_subset_closedBall (hrb.trans hb) (ball_subset_closedBall hx)
    exact hR i (ConicalCommonMaterial.material_subset_outer p a center ha i hm)
  exact ⟨j,fun M => eventually_superlevel center c R k hR0 hcr
    (ConicalCommonMaterial.coefficient_support p a center B hB hcontrast ha hsep R hR) I _ hS j hj M⟩
theorem simultaneous_superlevels {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ConicalStaticVolume.Data) (a b r : ι → ℝ) (center : ι → Space)
    (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
    (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
    (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i) (ConicalCommonMaterial.outer p center j))
    (R k : ℝ) (hR0 : 0 ≤ R) (hk : k ≠ 0) (hb : ∀ i, b i ≤ a i) (hb0 : ∀ i, 0 < b i)
    (hai : ∀ i, a i < (p i).cutoff.rIn) (hν : ∀ i, (p i).exponent < 1)
    (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R)
    (hcr : |k| ≤ MaterialVolumeLimit.commonRadius (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep).bound R)
    (hR : ∀ j, ConicalCommonMaterial.outer p center j ⊆ closedBall (0 : Space) R)
    (I : ConicalEntireGauge.Incident k) (hq : ∀ i, ConicalIntrinsicCoefficient.coefficient
      (ConicalCommonEntire.system p a center B hB hcontrast ha hsep i R k (b i) hR0 hk (hb i) (hai i) hfreq hR I)
      (hb0 i) ((hb i).trans_lt (hai i)) (hν i) ≠ 0) (hr : ∀ i, 0 < r i) (hrb : ∀ i, r i ≤ b i) :
    ∃ j : ι → Fin 3, ∀ M : ι → ℝ, ∀ᶠ n : ℕ in atTop, ∀ i : ι,
      0 < (volume.restrict (ball (center i) (r i))) {x |
        M i < ‖electric center (ConicalCommonBaseline.common p a center B hB hcontrast ha hsep) R k n I x (j i)‖} := by
  choose j hj using fun i => tip_superlevels p a center B hB hcontrast ha hsep i R k (b i) (r i)
    hR0 hk (hb i) (hb0 i) (hai i) (hν i) hfreq hcr hR I (hq i) (hr i) (hrb i)
  refine ⟨j,fun M => ?_⟩
  exact Filter.eventually_all.mpr (fun i => hj i (M i))
end OQ14.CommonRoundedTransfer
#print axioms OQ14.CommonRoundedTransfer.total_tendsto
#print axioms OQ14.CommonRoundedTransfer.eventually_superlevel


#print axioms OQ14.CommonRoundedTransfer.rounded_maxwell



#print axioms OQ14.CommonRoundedTransfer.sharp_unbounded_at_tip


#print axioms OQ14.CommonRoundedTransfer.tip_superlevels


#print axioms OQ14.CommonRoundedTransfer.simultaneous_superlevels

