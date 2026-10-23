import ConicalSeparatedSource
import ConicalMaterialRunge
import DynamicStaticLimit
import MaterialVolumeLimit

/-! The actual dynamic separated-source inverse converges to the identical singular static cut field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalSeparatedDynamic
open MeasureTheory Metric Filter OQ14.ConicalStaticVolume OQ14.ConicalSeparatedSource OQ14.NewtonL2
open scoped Topology
abbrev Space := Maxwell.Space
abbrev VectorL2 := VectorFourier.VectorL2

def incident (p : Data) (a k : ℝ) : VectorL2 :=
  -(newtonOperator+DynamicConvolution.operator k (a+p.cutoff.rOut)) (ConicalSeparatedSource.forcing p a)

def weightedForcing (p : Data) (a k : ℝ) : VectorL2 := StaticCoefficient.sqrtMultiplier (material p a) (incident p a k)
def solution (p : Data) (a k : ℝ) : VectorL2 :=
  Ring.inverse (DynamicVolume.volumeBlock (material p a) k a) (weightedForcing p a k)
def field (p : Data) (a k : ℝ) : VectorL2 := MaterialVolumeLimit.volumeField (material p a) k a (incident p a k)

theorem remainder_norm (k R : ℝ) (hR : 0 ≤ R) : ‖DynamicConvolution.operator k R‖ ≤ 63*R^2*k^2 := by
  apply (DynamicConvolution.operator_norm_le k R hR).trans_eq
  unfold DynamicConvolution.entryMass
  rw [DynamicVolume.unitBall_volume]
  field_simp [Real.pi_ne_zero]
  ring

theorem remainder_tendsto (R : ℝ) (hR : 0 ≤ R) :
    Tendsto (fun k : ℝ => DynamicConvolution.operator k R) (𝓝 0) (𝓝 0) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hl : Tendsto (fun k : ℝ => 63*R^2*k^2) (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 (0 : ℝ)) (𝓝 0)).pow 2)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => remainder_norm k R hR) hl

theorem incident_difference_bound (p : Data) (a k : ℝ) (ha : 0 ≤ a) :
    ‖incident p a k-ConicalSeparatedSource.staticIncident p a‖ ≤
      (63*(a+p.cutoff.rOut)^2*‖ConicalSeparatedSource.forcing p a‖)*k^2 := by
  have he : incident p a k-ConicalSeparatedSource.staticIncident p a=
      -DynamicConvolution.operator k (a+p.cutoff.rOut) (ConicalSeparatedSource.forcing p a) := by
    simp only [incident,ConicalSeparatedSource.staticIncident,ContinuousLinearMap.add_apply]
    abel
  rw [he,norm_neg]
  apply ((DynamicConvolution.operator k (a+p.cutoff.rOut)).le_opNorm _).trans
  exact (mul_le_mul_of_nonneg_right (remainder_norm k (a+p.cutoff.rOut) (add_nonneg ha p.cutoff.rOut_pos.le))
    (norm_nonneg _)).trans_eq (by ring)

theorem incident_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (incident p a) (𝓝 0) (𝓝 (ConicalSeparatedSource.staticIncident p a)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hl : Tendsto (fun k : ℝ => (63*(a+p.cutoff.rOut)^2*‖ConicalSeparatedSource.forcing p a‖)*k^2)
      (𝓝 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul ((tendsto_id : Tendsto (fun k : ℝ => k) (𝓝 (0 : ℝ)) (𝓝 0)).pow 2)
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => incident_difference_bound p a k ha) hl

theorem forcing_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (weightedForcing p a) (𝓝 0) (𝓝 (ConicalSeparatedSource.staticForcing p a)) :=
  ((StaticCoefficient.sqrtMultiplier (material p a)).continuous.tendsto _).comp (incident_tendsto p a ha)

theorem solution_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (solution p a) (𝓝 0) (𝓝 (ConicalSeparatedSource.weightedElectric p a)) := by
  have h := isBoundedBilinearMap_apply.continuous.tendsto
    (Ring.inverse (StaticNewton.volumeBlock (material p a)),ConicalSeparatedSource.staticForcing p a) |>.comp
      ((DynamicStaticLimit.inverse_tendsto (material p a) a ha).prodMk_nhds (forcing_tendsto p a ha))
  simpa only [solution,ConicalSeparatedSource.static_inverse] using h

theorem field_weighted (p : Data) (a k : ℝ) (ha : 0 ≤ a)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (material p a) a) :
    StaticCoefficient.sqrtMultiplier (material p a) (field p a k)=solution p a k :=
  MaterialVolumeLimit.volumeField_weighted (material p a) k a ha hk _

theorem field_tendsto (p : Data) (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (field p a) (𝓝 0) (𝓝 (ConicalStaticVolume.electric p)) := by
  have hresp : Tendsto (fun k : ℝ => newtonOperator+DynamicConvolution.operator k (2*a))
      (𝓝 0) (𝓝 newtonOperator) := by
    simpa only [add_zero] using tendsto_const_nhds.add (remainder_tendsto (2*a) (by linarith))
  have hsource := ((StaticCoefficient.sqrtMultiplier (material p a)).continuous.tendsto _).comp (solution_tendsto p a ha)
  have hscatter := isBoundedBilinearMap_apply.continuous.tendsto
    (newtonOperator,ConicalSeparatedSource.materialSource p a) |>.comp (hresp.prodMk_nhds hsource)
  have ht := (incident_tendsto p a ha).add hscatter
  have he : ConicalSeparatedSource.staticIncident p a+newtonOperator (ConicalSeparatedSource.materialSource p a)=
      ConicalStaticVolume.electric p := by
    have h := ConicalSeparatedSource.static_field_equation p a
    change _=ConicalSeparatedSource.staticIncident p a at h
    rw [← h]
    abel
  simpa only [field,MaterialVolumeLimit.volumeField,MaterialVolumeLimit.weightedSolution,solution,weightedForcing,he] using ht

theorem incident_ae (p : Data) (a k : ℝ) (hai : a < p.cutoff.rIn) (j : Fin 3) :
    NewtonL2.physicalCoordinate (incident p a k) j =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      fun x => -FieldResponse.electric k (ConicalSeparatedSource.forcing p a)
        (ConicalSeparatedSource.physicalSource p a) x j := by
  have he := LocalVolumeResponse.electric_ae_on_ball k a p.cutoff.rOut (ConicalSeparatedSource.forcing p a)
    (ConicalSeparatedSource.physicalSource p a)
    (ConicalSeparatedSource.source_integrable p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.source_zero_outer p a (hai.trans p.cutoff.rIn_lt_rOut).le)
    (ConicalSeparatedSource.forcing_ae p a) j
  simp only [incident,NewtonL2.physicalCoordinate_neg]
  filter_upwards [he,ae_restrict_of_ae (Lp.coeFn_neg
    (physicalCoordinate ((newtonOperator+DynamicConvolution.operator k (a+p.cutoff.rOut))
      (ConicalSeparatedSource.forcing p a)) j))] with x he hn
  rw [hn]
  simp only [Pi.neg_apply]
  congr 1

end OQ14.ConicalSeparatedDynamic

#print axioms OQ14.ConicalSeparatedDynamic.remainder_norm
#print axioms OQ14.ConicalSeparatedDynamic.remainder_tendsto
#print axioms OQ14.ConicalSeparatedDynamic.incident_difference_bound
#print axioms OQ14.ConicalSeparatedDynamic.incident_tendsto
#print axioms OQ14.ConicalSeparatedDynamic.forcing_tendsto
#print axioms OQ14.ConicalSeparatedDynamic.solution_tendsto
#print axioms OQ14.ConicalSeparatedDynamic.field_weighted
#print axioms OQ14.ConicalSeparatedDynamic.field_tendsto
#print axioms OQ14.ConicalSeparatedDynamic.incident_ae
