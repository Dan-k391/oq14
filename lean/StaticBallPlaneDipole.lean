import NewtonSeparatedResponse

/-! Exact pointwise plane dipoles from genuine continuous static ball responses. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace OQ14.StaticBallPlaneDipole

open MeasureTheory Metric Set StaticPlaneKernel NewtonSeparatedResponse
open scoped Topology

abbrev Vector := StaticBallNewton.Vector

def source (c : Space) (R : ℝ) (P : Vector) (j : Fin 3) : Space → ℂ :=
  (ball c R).indicator (fun _ => P j)

def dipole (c : Space) (R : ℝ) (P : Vector) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j, GreenKernel.phiHessian 0 (x-c) i j*((volume.real (ball c R) : ℂ)*P j)

theorem source_compact (c : Space) (R : ℝ) (P : Vector) (j : Fin 3) :
    ∀ y : Space, y ∉ closedBall 0 (‖c‖+R) → source c R P j y=0 := by
  intro y hout
  apply Set.indicator_of_not_mem
  intro hball
  apply hout
  simp only [mem_closedBall, dist_zero_right]
  have hd : ‖y-c‖ < R := by simpa only [mem_ball, dist_eq_norm] using hball
  have ht := norm_add_le (y-c) c
  rw [sub_add_cancel] at ht
  linarith

theorem source_gap (c : Space) (R d : ℝ) (P : Vector) (hc : d+R ≤ |c 2|) (j : Fin 3) :
    ∀ y : Space, source c R P j y ≠ 0 → d ≤ |y 2| := by
  intro y hy
  by_cases hb : y ∈ ball c R
  · exact StaticPlaneInclusions.ball_gap c R d hc y hb
  · exact False.elim (hy (Set.indicator_of_not_mem hb _))

theorem strip_outside (c : Space) (R d : ℝ) (hd : 0 < d) (hc : d+R ≤ |c 2|)
    (x : Space) (hx : x ∈ strip d) : R < ‖x-c‖ := by
  have hi : |x 2-c 2| ≤ ‖x-c‖ := by
    simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x-c) 2
  have ha := abs_sub_abs_le_abs_sub (c 2) (x 2)
  rw [abs_sub_comm] at ha
  change |x 2| < d/2 at hx
  linarith

theorem dipole_continuousOn (c : Space) (R d : ℝ) (hR : 0 < R) (hd : 0 < d)
    (hc : d+R ≤ |c 2|) (P : Vector) (i : Fin 3) :
    ContinuousOn (fun x => dipole c R P x i) (strip d) := by
  intro x hx
  have hn : x-c ≠ 0 := norm_ne_zero_iff.mp (hR.trans (strip_outside c R d hd hc x hx)).ne'
  have ht : ContinuousAt (fun z => dipole c R P z i) x :=
    tendsto_finset_sum _ (fun j _ =>
      ((NewtonExterior.hessian_continuousAt 0 i j (x-c) hn).comp
        (f := fun z : Space => z-c) (continuous_id.sub continuous_const).continuousAt).mul continuousAt_const)
  exact ht.continuousWithinAt

theorem response_eq_dipole (c : Space) (R d : ℝ) (hR : 0 < R) (hd : 0 < d)
    (hc : d+R ≤ |c 2|) (P : Vector) (i : Fin 3) :
    EqOn (fun x => response (source c R P) x i) (fun x => dipole c R P x i) (strip d) := by
  let F := StaticBallCentered.source c R P
  have hρ : ∀ j, Integrable (source c R P j) := fun j => StaticBallDipole.indicator_integrable c R (P j)
  have hF : ∀ j, NewtonL2.physicalCoordinate F j =ᵐ[volume] source c R P j :=
    fun j => (NewtonL2.physicalCoordinate_ae F j).trans (StaticBallCentered.source_ae c R P j)
  apply representative_unique d _ _
    (response_continuousOn _ hρ d hd (source_gap c R d P hc) i)
    (dipole_continuousOn c R d hR hd hc P i)
  filter_upwards [newton_ae_response F (source c R P) hρ hF d (‖c‖+R) hd
    (source_compact c R P) (source_gap c R d P hc) i,
    NewtonL2.physicalCoordinate_ae (NewtonL2.newtonOperator F) i,
    StaticBallDipole.newton_source_dipole c R hR P i] with x hx hp hdip hstrip
  exact (hx hstrip).symm.trans (hp.trans (hdip (strip_outside c R d hd hc x hstrip)))

theorem plane_response_eq_dipole (c : Space) (R d : ℝ) (hR : 0 < R) (hd : 0 < d)
    (hc : d+R ≤ |c 2|) (P : Vector) (i : Fin 3) (q : PlaneInverseCube.Plane) :
    (∑ j, StaticPlaneSource.field (source c R P j) i j q)=
      dipole c R P (MaxwellPlaneTail.planePoint q) i := by
  rw [← response_plane]
  apply response_eq_dipole c R d hR hd hc P i
  simp [strip, MaxwellPlaneTail.planePoint, hd]

end OQ14.StaticBallPlaneDipole

#print axioms OQ14.StaticBallPlaneDipole.source_compact
#print axioms OQ14.StaticBallPlaneDipole.source_gap
#print axioms OQ14.StaticBallPlaneDipole.strip_outside
#print axioms OQ14.StaticBallPlaneDipole.dipole_continuousOn
#print axioms OQ14.StaticBallPlaneDipole.response_eq_dipole
#print axioms OQ14.StaticBallPlaneDipole.plane_response_eq_dipole
