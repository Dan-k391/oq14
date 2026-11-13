import Packet07DrivenUniformTraceCollar
import Packet07BoundaryNull
import Packet07PeakAttainment

/-! An actual low trace collar isolates the driven half-amplitude hotspot. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet07DrivenUniformHotspot
open MeasureTheory Set Filter Metric Maxwell Packet05ActualMaximum Packet05BinaryPhaseMaximum
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ

def HotspotAbove (E : Field) (body : Set Space) (center : Space) (r M B : ℝ) : Prop :=
  let K := closedBall center r
  ∃ inside outside : Fin 3 → Space → ℂ,
    (∀ i, ContinuousOn (inside i) (K ∩ closure body)) ∧
    (∀ i, ContinuousOn (outside i) (K ∩ closure (closure body)ᶜ)) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ body)] inside i) ∧
    (∀ i, (fun y => E y i) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside i) ∧
    ∃ b x, x ∈ K ∩ phaseDomain body b ∧
      M < physicalAmplitude (phaseField inside outside b) x ∧
      2*B < physicalAmplitude (phaseField inside outside b) x ∧
      (∀ b' y, y ∈ K ∩ phaseDomain body b' →
        physicalAmplitude (phaseField inside outside b') y ≤ physicalAmplitude (phaseField inside outside b) x) ∧
      (∀ b' y, y ∈ phaseDomain body b' → dist y center=r → physicalAmplitude (phaseField inside outside b') y ≤ B) ∧
      let S := Packet07HotspotComponent.branchSuperlevel (phaseDomain body)
        (fun b' => physicalAmplitude (phaseField inside outside b')) (physicalAmplitude (phaseField inside outside b) x/2)
      x ∈ ball center r ∧ x ∈ connectedComponentIn S x ∧ IsConnected (connectedComponentIn S x) ∧
        IsCompact (connectedComponentIn S x) ∧ connectedComponentIn S x ⊆ ball center r

theorem eventually_actual_hotspot {N : ℕ} {Pset : Set Packet07PlanarCenters.Plane} {d t : ℝ}
    (g : Packet07PlanarSetup.Setup N Pset d t) (freq : ℝ) (hfreq0 : freq ≠ 0) (input : Input)
    (hfreq : |freq| ≤ MaterialVolumeLimit.commonRadius d g.enclosing)
    (i : Fin N) (r : ℝ) (hr : 0 < r) (hrR : r < g.radius) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ j : ℕ in atTop, ∀ M : ℝ,
      0 < (volume.restrict (closedBall (g.centers i) r))
        {y | max M (2*B) < physicalAmplitude (fun k x => g.electric freq j input x k) y} →
      HotspotAbove (g.electric freq j input) (CommonBinaryInterface.body g.dataFamily g.radii g.centers j)
        (g.centers i) r M B := by
  obtain ⟨A,B,hA,hAr,hSphere,hB,htraces⟩ := Packet07DrivenUniformTraceCollar.actual_uniform_trace_collar
    g freq hfreq0 input hfreq i r hr hrR
  refine ⟨B,hB,?_⟩
  filter_upwards [htraces,CommonBinaryInterface.eventually_body_smooth g.dataFamily g.radii g.centers
    g.radii_pos g.radii_outer g.outer_sep] with j hj hcert M hpeak
  let body := CommonBinaryInterface.body g.dataFamily g.radii g.centers j
  let K := closedBall (g.centers i) r
  let L := closedBall (g.centers i) g.radius
  have hKL : K ⊆ L := closedBall_subset_closedBall hrR.le
  obtain ⟨inside,outside,hi,ho,hiae,hoae,htrace⟩ := hj
  have hic (l : Fin 3) : ContinuousOn (inside l) (K ∩ closure body) :=
    (hi l).mono (inter_subset_inter_left _ hKL)
  have hoc (l : Fin 3) : ContinuousOn (outside l) (K ∩ closure (closure body)ᶜ) :=
    (ho l).mono (inter_subset_inter_left _ hKL)
  have hiAE (l : Fin 3) : (fun y => g.electric freq j input y l) =ᵐ[volume.restrict (K ∩ body)] inside l :=
    ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hKL) (hiae l)
  have hoAE (l : Fin 3) : (fun y => g.electric freq j input y l) =ᵐ[volume.restrict (K ∩ (closure body)ᶜ)] outside l :=
    ae_restrict_of_ae_restrict_of_subset (inter_subset_inter_left _ hKL) (hoae l)
  have hb : IsOpen body := CommonBinaryInterface.body_open g.dataFamily g.radii g.centers j
  have hn : volume (frontier body)=0 := Packet07BoundaryNull.bounded_regular_body_boundary_null body 0 g.enclosing
    (CommonBinaryInterface.body_support g.dataFamily g.radii g.centers g.radii_pos g.radii_outer g.enclosing g.outer_enclosed j) hcert
  obtain ⟨b,x,hx,hhigh,hmax⟩ := attained_above_peak body K hb (isCompact_closedBall _ _)
    (nonempty_closedBall.mpr hr.le) hn (g.electric freq j input) inside outside hic hoc hiAE hoAE (max M (2*B)) hpeak
  have hc (b : Bool) : ContinuousOn (physicalAmplitude (phaseField inside outside b)) (K ∩ phaseDomain body b) := by
    cases b
    · exact amplitude_continuousOn _ _ hoc
    · exact amplitude_continuousOn _ _ hic
  have hboundary (b' : Bool) (y : Space) (hy : y ∈ phaseDomain body b') (hd : dist y (g.centers i)=r) :
      physicalAmplitude (phaseField inside outside b') y ≤ B := htrace b' y ⟨hSphere hd,hy⟩
  have htwo : 2*B < physicalAmplitude (phaseField inside outside b) x := (le_max_right _ _).trans_lt hhigh
  have hcomponent := Packet07PeakAttainment.half_peak_component (phaseDomain body)
    (fun b' => physicalAmplitude (phaseField inside outside b')) (fun b' => by cases b' <;> exact isClosed_closure)
    (g.centers i) x r B hB hc b hx htwo hboundary
  exact ⟨inside,outside,hic,hoc,hiAE,hoAE,b,x,hx,(le_max_left _ _).trans_lt hhigh,htwo,hmax,hboundary,hcomponent⟩
end OQ14.Packet07DrivenUniformHotspot
#print axioms OQ14.Packet07DrivenUniformHotspot.eventually_actual_hotspot
