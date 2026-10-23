import SourceCorrectionLocalBounds
import VacuumOutgoingHelmholtz

/-! Genuine smoothness of the actual layered source fields beyond the last interface. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceExteriorSmooth
open MeasureTheory Filter Set OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourceRadiation
open OQ14.HarmonicPolynomial Complex
open scoped Topology

theorem electric_exterior (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) :
    SourceUnclippedMaxwell.electric d P x=(I*amplitude d) •
      SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data d.l) P x := by
  have hs : raw d ‖x‖=amplitude d • RadialStack.outgoing d.l ‖x‖ :=
    RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  have hσ : SourceRadialSystem.inverseSigma d ‖x‖=1 := by
    simp only [SourceRadialSystem.inverseSigma,SourceRadialSystem.extend,
      if_neg (not_le.mpr ((RadialStack.chain_ordered d.chain).trans_lt hx)),if_neg (not_le.mpr hx)]
  have hv := VacuumOutgoingHelmholtz.raw_state d.l ‖x‖
  rw [VacuumOutgoingHelmholtz.u_value,VacuumOutgoingHelmholtz.uD_value] at hv
  ext i
  simp only [SourceUnclippedMaxwell.electric,hs,hv,hσ,VacuumOutgoingHelmholtz.inverse_sigma,
    one_mul,Prod.smul_fst,Prod.smul_snd,RadialStack.outgoing,Pi.smul_apply,smul_eq_mul,
    show (VacuumOutgoingBounds.data d.l).l=d.l from rfl]
  ring_nf
  simp only [I_sq]
  ring

theorem magnetic_exterior (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) :
    SourceUnclippedMaxwell.magnetic d P x=(I*amplitude d) •
      SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data d.l) P x := by
  have hs : raw d ‖x‖=amplitude d • RadialStack.outgoing d.l ‖x‖ :=
    RadialGluing.sourceState_exterior d.l d.chain d.hR ‖x‖ hx
  have hv := VacuumOutgoingHelmholtz.raw_state d.l ‖x‖
  rw [VacuumOutgoingHelmholtz.u_value,VacuumOutgoingHelmholtz.uD_value] at hv
  ext i
  simp only [SourceUnclippedMaxwell.magnetic,hs,hv,Prod.smul_fst,RadialStack.outgoing,Pi.smul_apply,smul_eq_mul,
    show (VacuumOutgoingBounds.data d.l).l=d.l from rfl]
  ring_nf
  simp [I_sq]

theorem electric_smooth (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (hh : formalLaplacian P=0)
    (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => SourceUnclippedMaxwell.electric d P z i) x := by
  have hx0 : x≠0 := norm_pos_iff.mp ((d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx)
  apply (contDiffAt_const.mul (VacuumOutgoingHelmholtz.electric_smooth d.l P hp hh x hx0 i)).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact congrFun (electric_exterior d P y hy) i

theorem magnetic_smooth (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => SourceUnclippedMaxwell.magnetic d P z i) x := by
  have hx0 : x≠0 := norm_pos_iff.mp ((d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx)
  apply (contDiffAt_const.mul (VacuumOutgoingHelmholtz.magnetic_smooth d.l P x hx0 i)).congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
  exact congrFun (magnetic_exterior d P y hy) i

theorem correction_electric_smooth (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) (hh : formalLaplacian P=0)
    (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => SourceRegularCorrection.electric d P z i) x := by
  have hx0 : x≠0 := norm_pos_iff.mp ((d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx)
  have hR : (SourceCoreReaction.vacuum d).X<‖x‖ := (RadialStack.chain_ordered d.chain).trans_lt hx
  apply ((electric_smooth d P hp hh x hx i).sub
    (electric_smooth (SourceCoreReaction.vacuum d) P hp hh x hR i)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx0] with y hy
  exact congrFun (SourceRegularCorrection.electric_away d P hp hh y hy) i

theorem correction_magnetic_smooth (d : Data) (P : Poly) (x : Space) (hx : d.X<‖x‖) (i : Fin 3) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun z => SourceRegularCorrection.magnetic d P z i) x := by
  have hx0 : x≠0 := norm_pos_iff.mp ((d.hR.trans_le (RadialStack.chain_ordered d.chain)).trans hx)
  have hR : (SourceCoreReaction.vacuum d).X<‖x‖ := (RadialStack.chain_ordered d.chain).trans_lt hx
  apply ((magnetic_smooth d P x hx i).sub
    (magnetic_smooth (SourceCoreReaction.vacuum d) P x hR i)).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hx0] with y hy
  exact congrFun (SourceRegularCorrection.magnetic_away d P y hy) i

end OQ14.SourceExteriorSmooth

#print axioms OQ14.SourceExteriorSmooth.electric_exterior
#print axioms OQ14.SourceExteriorSmooth.magnetic_exterior
#print axioms OQ14.SourceExteriorSmooth.electric_smooth
#print axioms OQ14.SourceExteriorSmooth.magnetic_smooth
#print axioms OQ14.SourceExteriorSmooth.correction_electric_smooth
#print axioms OQ14.SourceExteriorSmooth.correction_magnetic_smooth
