import Packet06PlacedProjection
import Packet06PlacedAction
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedGreenSupport
open MeasureTheory Metric Maxwell Packet06PlacedEquivalence Packet06PlacedProjection
open scoped Topology
abbrev V := VectorFourier.VectorL2

theorem point_qmp (s : ℝ) (hs : 0 < s) (a : Space) :
    Measure.QuasiMeasurePreserving (Packet06PhysicalPlacement.point s a) volume volume := by
  have hr := Packet06CyclicRotation.rotation.measurePreserving.quasiMeasurePreserving
  have hd := DilationL2.smul_qmp_space s⁻¹ (inv_ne_zero hs.ne')
  have ht := (measurePreserving_add_left (volume : Measure Space) a).quasiMeasurePreserving
  simpa only [Packet06PhysicalPlacement.point,Function.comp_def] using ht.comp (hd.comp hr)

theorem inverse_source_supported (s : ℝ) (hs : 0 < s) (a : Space) (r : ℝ)
    (f : V)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall a r → f (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ y : Space ∂volume, y ∉ closedBall 0 (s*r) →
      ((placed s hs a).symm f) (VectorFourier.coordinateMap y) = 0 := by
  let u := (placed s hs a).symm f
  have hu : Packet06PlacedKernel.placedUnknown s a u = f := by
    rw [← placed_apply]
    exact (placed s hs a).apply_symm_apply f
  have hp := (point_qmp s hs a).ae hf
  have ha := (point_qmp s hs a).ae (ae_all_iff.mpr (fun i => Packet06PlacedAction.placed_unknown_ae s hs a u i))
  have hcoeff : (((Real.sqrt s*s : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_ne_zero (Real.sqrt_ne_zero'.mpr hs) hs.ne')
  filter_upwards [hp,ha] with y hp ha hy
  have hyn : s*r < ‖y‖ := by simpa only [mem_closedBall,dist_zero_right,not_le] using hy
  have hout : Packet06PhysicalPlacement.point s a y ∉ closedBall a r := by
    rw [mem_closedBall,Packet06PhysicalPlacement.point_distance s hs a y,not_le]
    have hmul := mul_lt_mul_of_pos_left hyn (inv_pos.mpr hs)
    have hcancel : s⁻¹*(s*r) = r := by field_simp
    linarith
  have hz := hp hout
  have hback : Packet06CyclicRotation.unrotate (s • (Packet06PhysicalPlacement.point s a y-a)) = y := by
    simp only [Packet06PhysicalPlacement.point,add_sub_cancel_left,smul_smul,mul_inv_cancel₀ hs.ne',one_smul,
      Packet06CyclicRotation.unrotate_rotate]
  apply PiLp.ext
  intro j
  have h := ha (WeakCurl.next j)
  rw [hu,hback,hz] at h
  have hi : WeakCurl.previous (WeakCurl.next j) = j := by fin_cases j <;> rfl
  rw [hi] at h
  exact (mul_eq_zero.mp h.symm).resolve_left hcoeff

/-- Physical placement transports an a.e. centered-ball support to the
corresponding shifted ball, with its exact positive scale. -/
theorem placed_source_supported (s : ℝ) (hs : 0 < s) (a : Space) (J : ℝ) (u : V)
    (hu : ∀ᵐ y : Space ∂volume, y ∉ closedBall 0 J → u (VectorFourier.coordinateMap y) = 0) :
    ∀ᵐ x : Space ∂volume, x ∉ closedBall a (J/s) →
      (placed s hs a u) (VectorFourier.coordinateMap x) = 0 := by
  let q : Space → Space := fun x => Packet06CyclicRotation.unrotate (s • (x-a))
  have hq : Measure.QuasiMeasurePreserving q volume volume := by
    have ht := (measurePreserving_add_right (volume : Measure Space) (-a)).quasiMeasurePreserving
    have hd := DilationL2.smul_qmp_space s hs.ne'
    have hr := Packet06CyclicRotation.rotation.symm.measurePreserving.quasiMeasurePreserving
    simpa only [q,Function.comp_def,sub_eq_add_neg] using hr.comp (hd.comp ht)
  have hu' := hq.ae hu
  have ha := ae_all_iff.mpr (fun i => Packet06PlacedAction.placed_unknown_ae s hs a u i)
  filter_upwards [hu',ha] with x hx hax hout
  have hdist : J/s < ‖x-a‖ := by simpa only [mem_closedBall,dist_eq_norm,not_le] using hout
  have hqout : q x ∉ closedBall 0 J := by
    simp only [mem_closedBall,dist_zero_right,not_le,q]
    change J < ‖Packet06CyclicRotation.rotation.symm (s • (x-a))‖
    rw [Packet06CyclicRotation.rotation.symm.norm_map, norm_smul,Real.norm_eq_abs,abs_of_pos hs]
    have he : s*(J/s)=J := mul_div_cancel₀ J hs.ne'
    nlinarith
  have hz := hx hqout
  apply PiLp.ext
  intro i
  rw [placed_apply,hax i,hz]
  simp

/-- The transported sector projection preserves every centered-on-device source
ball, for arbitrary compactly supported ambient inputs. -/
theorem placed_projected_supported (s : ℝ) (hs : 0 < s) (a : Space) (r : ℝ) (f : V)
    (hf : ∀ᵐ x : Space ∂volume, x ∉ closedBall a r → f (VectorFourier.coordinateMap x) = 0) :
    ∀ᵐ x : Space ∂volume, x ∉ closedBall a r →
      ((placedSector s hs a).orthogonalProjection f : V) (VectorFourier.coordinateMap x) = 0 := by
  let u := (placed s hs a).symm f
  have hu := inverse_source_supported s hs a r f hf
  have hp := Packet06ProjectedSupport.projected_supported (s*r) u hu
  have ht := placed_source_supported s hs a (s*r)
    (Packet06SectorOperator.Sector.orthogonalProjection u) hp
  have he : (s*r)/s = r := by field_simp
  rw [he] at ht
  have hproj : ((placedSector s hs a).orthogonalProjection f : V) =
      placed s hs a (Packet06SectorOperator.Sector.orthogonalProjection u) := by
    rw [projected_transport]
    rfl
  rwa [hproj]

#print axioms OQ14.Packet06PlacedGreenSupport.placed_projected_supported
#print axioms OQ14.Packet06PlacedGreenSupport.placed_source_supported
#print axioms OQ14.Packet06PlacedGreenSupport.point_qmp
#print axioms OQ14.Packet06PlacedGreenSupport.inverse_source_supported
end OQ14.Packet06PlacedGreenSupport
