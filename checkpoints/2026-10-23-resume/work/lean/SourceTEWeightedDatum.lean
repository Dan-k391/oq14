import SourceTEVolumeRepresentation
import SourceMuBounds
import IncidentLocalization
import MaterialVolumeConverse

/-! Actual magnetic-profile weighted data for the singular TE source modes. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SourceTEWeightedDatum
open MeasureTheory Set Metric OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceCoreReaction
abbrev Coefficient := StaticCoefficient.Coefficient

theorem material_outer (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=SourceGeneralMaxwell.mu d ‖x‖-1)
    (x : Space) (hx : x∉closedBall 0 d.X) : c.value (VectorFourier.coordinateMap x)=0 := by
  have hn : d.X<‖x‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  have he := hm x
  have hR : d.R<‖x‖ := (RadialStack.chain_ordered d.chain).trans_lt hn
  simp only [SourceGeneralMaxwell.mu,SourceRadialSystem.extend,if_neg (not_le.mpr hR),if_neg (not_le.mpr hn),sub_self] at he
  exact Complex.ofReal_eq_zero.mp he

theorem material_inner (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=SourceGeneralMaxwell.mu d ‖x‖-1)
    (x : Space) (hx : ‖x‖≤d.R) : c.value (VectorFourier.coordinateMap x)=0 := by
  have he := hm x
  simp only [SourceGeneralMaxwell.mu,SourceRadialSystem.extend,if_pos hx,sub_self] at he
  exact Complex.ofReal_eq_zero.mp he

def datum (c : Coefficient) (X : ℝ)
    (hc : ∀ x : Space, x∉closedBall 0 X → c.value (VectorFourier.coordinateMap x)=0)
    (a : Data) (p : HarmonicPolynomial.Poly) : VectorFourier.VectorL2 :=
  IncidentLocalization.datum c X (SourceElectricProfiles.magnetic (SourceCorrectionLocalBounds.clipped a) p)
    hc (SourceLocalBounds.magnetic_memLp_ball (SourceCorrectionLocalBounds.clipped a) p X)

theorem actual (c : Coefficient) (X : ℝ)
    (hc : ∀ x : Space, x∉closedBall 0 X → c.value (VectorFourier.coordinateMap x)=0)
    (a : Data) (p : HarmonicPolynomial.Poly)
    (hzero : ∀ x : Space, ‖x‖≤a.R → c.value (VectorFourier.coordinateMap x)=0) (i : Fin 3) :
    (fun x => datum c X hc a p (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*SourceUnclippedMaxwell.magnetic a p x i := by
  filter_upwards [IncidentLocalization.datum_actual c X
    (SourceElectricProfiles.magnetic (SourceCorrectionLocalBounds.clipped a) p) hc
    (SourceLocalBounds.magnetic_memLp_ball (SourceCorrectionLocalBounds.clipped a) p X) i] with x hx
  change datum c X hc a p (VectorFourier.coordinateMap x) i=_
  unfold datum
  rw [hx]
  by_cases hn : ‖x‖≤a.R
  · simp only [IncidentLocalization.weighted,hzero x hn,Real.sqrt_zero,Complex.ofReal_zero,zero_mul]
  · have hgap : a.R/4<‖x‖ := by linarith [a.hR]
    have he := SourceUnclippedMaxwell.magnetic_agrees a (a.R/4) (by linarith [a.hR]) p x hgap
    change _*SourceElectricProfiles.magnetic (SourceCorrectionLocalBounds.clipped a) p x i=_
    exact congrArg (fun v : Vector => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*v i) he

theorem source_actual (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=SourceGeneralMaxwell.mu d ‖x‖-1)
    (p : HarmonicPolynomial.Poly) (i : Fin 3) :
    DynamicVolume.source c (datum c d.X (material_outer c d hm) d p) i=ᵐ[volume]
      SourceTECorrection.polarization d p i := by
  have h := MaterialVolumeConverse.source_from_weighted c (datum c d.X (material_outer c d hm) d p)
    (SourceUnclippedMaxwell.magnetic d p) (actual c d.X _ d p (material_inner c d hm)) i
  filter_upwards [h] with x hx
  rw [hx,hm]
  rfl

theorem sourceL2_eq (c : Coefficient) (d : Data)
    (hm : ∀ x : Space, (c.value (VectorFourier.coordinateMap x) : ℂ)=SourceGeneralMaxwell.mu d ‖x‖-1)
    (p : HarmonicPolynomial.Poly) :
    StaticCoefficient.sqrtMultiplier c (datum c d.X (material_outer c d hm) d p)=
      SourceTEVolumeRepresentation.sourceL2 d p := by
  apply MaterialVolumeConverse.vector_ext
  intro i
  exact (StaticNewton.material_source_ae c _ i).trans
    ((source_actual c d hm p i).trans (SourceTEVolumeRepresentation.sourceL2_actual d p i).symm)

end OQ14.SourceTEWeightedDatum
#print axioms OQ14.SourceTEWeightedDatum.material_outer
#print axioms OQ14.SourceTEWeightedDatum.material_inner
#print axioms OQ14.SourceTEWeightedDatum.actual
#print axioms OQ14.SourceTEWeightedDatum.source_actual
#print axioms OQ14.SourceTEWeightedDatum.sourceL2_eq
