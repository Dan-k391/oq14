import FourierL2
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.Restrict

/-! # Connected-open propagation of actual local almost-everywhere zero germs -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace OQ14.LocalAEZeroPropagation
open MeasureTheory Filter Metric Set
open scoped Topology
abbrev Space := FourierL2.Space

def germZero (u : Space → ℂ) (x : Space) : Prop :=
  ∃ r : ℝ, 0 < r ∧ u =ᵐ[volume.restrict (ball x r)] 0

def zeroGerms (u : Space → ℂ) : Set Space := {x | germZero u x}

theorem germZero_of_ball (u : Space → ℂ) (c : Space) (r : ℝ)
    (hz : u =ᵐ[volume.restrict (ball c r)] 0) (x : Space) (hx : x ∈ ball c r) :
    germZero u x := by
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
  exact ⟨δ,hδ,ae_restrict_of_ae_restrict_of_subset hball hz⟩

theorem zeroGerms_open (u : Space → ℂ) : IsOpen (zeroGerms u) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨r,hr,hz⟩ := hx
  exact Filter.mem_of_superset (ball_mem_nhds x hr)
    (fun y hy => germZero_of_ball u x r hz y hy)

theorem zeroGerms_closure_inter (Ω : Set Space) (hΩ : IsOpen Ω) (u : Space → ℂ)
    (hprop : ∀ c ∈ Ω, ∀ r : ℝ, 0 < r → ball c r ⊆ Ω →
      germZero u c → u =ᵐ[volume.restrict (ball c r)] 0) :
    closure (zeroGerms u) ∩ Ω ⊆ zeroGerms u := by
  rintro x ⟨hxZ,hxΩ⟩
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hΩ x hxΩ
  obtain ⟨c,hcZ,hc⟩ := Metric.mem_closure_iff.mp hxZ (δ/4) (by linarith)
  have hcball : c ∈ ball x δ := by rw [mem_ball,dist_comm]; linarith
  have hcΩ : c ∈ Ω := hball hcball
  have hb : ball c (δ/2) ⊆ Ω := by
    intro y hy
    apply hball
    rw [mem_ball] at hy ⊢
    have ht := dist_triangle y c x
    rw [dist_comm c x] at ht
    linarith
  have hz := hprop c hcΩ (δ/2) (by linarith) hb hcZ
  have hxc : x ∈ ball c (δ/2) := by rw [mem_ball]; linarith
  exact germZero_of_ball u c (δ/2) hz x hxc

theorem germs_on_of_germ (Ω : Set Space) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (u : Space → ℂ)
    (hprop : ∀ c ∈ Ω, ∀ r : ℝ, 0 < r → ball c r ⊆ Ω →
      germZero u c → u =ᵐ[volume.restrict (ball c r)] 0)
    (c₀ : Space) (hc₀ : c₀ ∈ Ω) (hzero : germZero u c₀) :
    ∀ x ∈ Ω, germZero u x := by
  exact hconn.subset_of_closure_inter_subset (zeroGerms_open u)
    ⟨c₀,hc₀,hzero⟩ (zeroGerms_closure_inter Ω hΩ u hprop)

theorem ae_zero_of_germs (Ω : Set Space) (u : Space → ℂ)
    (hlocal : ∀ x ∈ Ω, germZero u x) : u =ᵐ[volume.restrict Ω] 0 := by
  choose r hr hz using (fun x : Ω => hlocal x x.property)
  let b : Ω → Set Space := fun x => ball (x : Space) (r x)
  obtain ⟨T,hT,hcover⟩ := TopologicalSpace.isOpen_iUnion_countable b (fun _ => isOpen_ball)
  have hu : u =ᵐ[volume.restrict (⋃ x ∈ T, b x)] 0 := by
    apply (ae_eq_restrict_biUnion_iff b hT u 0).mpr
    intro x _
    exact hz x
  rw [hcover] at hu
  apply ae_restrict_of_ae_restrict_of_subset _ hu
  intro x hx
  exact mem_iUnion.mpr ⟨⟨x,hx⟩, mem_ball_self (hr ⟨x,hx⟩)⟩

theorem ae_zero_on_of_germ (Ω : Set Space) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (u : Space → ℂ)
    (hprop : ∀ c ∈ Ω, ∀ r : ℝ, 0 < r → ball c r ⊆ Ω →
      germZero u c → u =ᵐ[volume.restrict (ball c r)] 0)
    (c₀ : Space) (hc₀ : c₀ ∈ Ω) (hzero : germZero u c₀) :
    u =ᵐ[volume.restrict Ω] 0 :=
  ae_zero_of_germs Ω u (germs_on_of_germ Ω hΩ hconn u hprop c₀ hc₀ hzero)

end OQ14.LocalAEZeroPropagation

#print axioms OQ14.LocalAEZeroPropagation.germZero_of_ball
#print axioms OQ14.LocalAEZeroPropagation.zeroGerms_open
#print axioms OQ14.LocalAEZeroPropagation.zeroGerms_closure_inter
#print axioms OQ14.LocalAEZeroPropagation.germs_on_of_germ
#print axioms OQ14.LocalAEZeroPropagation.ae_zero_of_germs
#print axioms OQ14.LocalAEZeroPropagation.ae_zero_on_of_germ

