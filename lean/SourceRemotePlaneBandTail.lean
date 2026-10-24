import SourceRemotePlaneBand
import SourceRemotePlaneTail

/-! The absolute plane flux of a finite mixed TM/TE band of layered source modes, outside radius R,
tends to zero as R tends to infinity. Fixed finite band, exterior only. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SourceRemotePlaneBandTail
open MeasureTheory Set Metric Filter Complex OQ14.Maxwell OQ14.HarmonicPolynomial OQ14.SourceRadialSystem
  OQ14.PlaneInverseCube OQ14.SourceRemotePlaneBand
open scoped Topology

theorem modeElectric_continuousOn (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ContinuousOn (modeElectric tm d P) {x : Space | d.X<‖x‖} := by
  cases tm
  · simpa only [modeElectric,Bool.false_eq_true,if_false,SourceGeneralMaxwell.teElectric] using
      SourceRemotePlaneTail.magnetic_continuousOn d P
  · simpa only [modeElectric,if_true] using SourceRemotePlaneTail.electric_continuousOn d P hp

theorem modeMagnetic_continuousOn (tm : Bool) (d : Data) (P : Poly) (hp : P.IsHomogeneous d.l) :
    ContinuousOn (modeMagnetic tm d P) {x : Space | d.X<‖x‖} := by
  cases tm
  · have h := (SourceRemotePlaneTail.electric_continuousOn d P hp).neg
    have : modeMagnetic false d P=fun x => -SourceUnclippedMaxwell.electric d P x := by
      funext x
      funext i
      simp [modeMagnetic,SourceGeneralMaxwell.teMagnetic]
    rw [this]
    exact h
  · simpa only [modeMagnetic,if_true] using SourceRemotePlaneTail.magnetic_continuousOn d P

theorem band_tail_small {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tmE : ι → Bool) (dE : ι → Data) (PE : ι → Poly) (hE : ∀ i, (PE i).IsHomogeneous (dE i).l) (cE : ι → ℂ)
    (tmH : κ → Bool) (dH : κ → Data) (PH : κ → Poly) (hH : ∀ j, (PH j).IsHomogeneous (dH j).l) (cH : κ → ℂ) :
    Tendsto (fun R : ℝ => ∫ q : Plane in {q : Plane | R ≤ ‖q‖}, ‖crossProduct
      (∑ i, cE i • modeElectric (tmE i) (dE i) (PE i) (MaxwellPlaneTail.planePoint q))
      (conjugate (∑ j, cH j • modeMagnetic (tmH j) (dH j) (PH j) (MaxwellPlaneTail.planePoint q))) 2‖)
      atTop (𝓝 0) := by
  obtain ⟨r0,C,hr0,hC,hXE,hXH,hb⟩ := band_plane_flux_bound tmE dE PE hE cE tmH dH PH hH cH
  have hmaps : MapsTo MaxwellPlaneTail.planePoint {q : Plane | r0<‖q‖} {x : Space | r0<‖x‖} := by
    intro q hq
    change r0<‖MaxwellPlaneTail.planePoint q‖
    rw [MaxwellPlaneTail.planePoint_norm]
    exact hq
  have hEc : ContinuousOn (fun x : Space => ∑ i, cE i • modeElectric (tmE i) (dE i) (PE i) x)
      {x : Space | r0<‖x‖} := by
    apply continuousOn_finset_sum
    intro i _
    apply ContinuousOn.const_smul
    exact (modeElectric_continuousOn (tmE i) (dE i) (PE i) (hE i)).mono
      (fun x hx => lt_trans (hXE i) hx)
  have hHc : ContinuousOn (fun x : Space => ∑ j, cH j • modeMagnetic (tmH j) (dH j) (PH j) x)
      {x : Space | r0<‖x‖} := by
    apply continuousOn_finset_sum
    intro j _
    apply ContinuousOn.const_smul
    exact (modeMagnetic_continuousOn (tmH j) (dH j) (PH j) (hH j)).mono
      (fun x hx => lt_trans (hXH j) hx)
  have hE' := hEc.comp MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps
  have hH' := hHc.comp MaxwellPlaneTail.planePoint_continuous.continuousOn hmaps
  have hEi (i : Fin 3) := continuousOn_pi.mp hE' i
  have hHi (i : Fin 3) : ContinuousOn (fun q : Plane => (starRingEnd ℂ)
      ((∑ j, cH j • modeMagnetic (tmH j) (dH j) (PH j) (MaxwellPlaneTail.planePoint q)) i))
      {q : Plane | r0<‖q‖} :=
    Complex.continuous_conj.comp_continuousOn (continuousOn_pi.mp hH' i)
  have hcont : ContinuousOn (fun q : Plane => crossProduct
      (∑ i, cE i • modeElectric (tmE i) (dE i) (PE i) (MaxwellPlaneTail.planePoint q))
      (conjugate (∑ j, cH j • modeMagnetic (tmH j) (dH j) (PH j) (MaxwellPlaneTail.planePoint q))) 2)
      {q : Plane | r0<‖q‖} := by
    simp only [SourceRemotePlaneFlux.cross_two,conjugate]
    exact ((hEi 0).mul (hHi 1)).sub ((hEi 1).mul (hHi 0))
  refine (SourceRemotePlaneTail.tail_integral_small _ C r0 ?_ ?_).2
  · exact hcont.aestronglyMeasurable (isOpen_lt continuous_const continuous_norm).measurableSet
  · intro q hq
    have := hb (MaxwellPlaneTail.planePoint q) (SourceRemotePlaneTail.planePoint_two q)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hq.le)
    rwa [MaxwellPlaneTail.planePoint_norm] at this

end OQ14.SourceRemotePlaneBandTail
#print axioms OQ14.SourceRemotePlaneBandTail.modeElectric_continuousOn
#print axioms OQ14.SourceRemotePlaneBandTail.modeMagnetic_continuousOn
#print axioms OQ14.SourceRemotePlaneBandTail.band_tail_small
