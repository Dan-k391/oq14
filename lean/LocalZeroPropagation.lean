import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Connected-domain propagation from an explicit local ball property -/

noncomputable section
set_option autoImplicit false

namespace OQ14.LocalZeroPropagation

open Filter Metric Set
open scoped Topology

variable {X Y : Type*} [PseudoMetricSpace X] [Zero Y]

def zeroGerms (u : X → Y) : Set X := {x | u =ᶠ[𝓝 x] 0}

theorem zeroGerms_open (u : X → Y) : IsOpen (zeroGerms u) :=
  isOpen_setOf_eventually_nhds

theorem zeroGerms_closure_inter (Ω : Set X) (hΩ : IsOpen Ω) (u : X → Y)
    (hprop : ∀ c ∈ Ω, ∀ r : ℝ, 0 < r → ball c r ⊆ Ω →
      u =ᶠ[𝓝 c] 0 → ∀ x ∈ ball c r, u x = 0) :
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
  exact eventually_of_mem (isOpen_ball.mem_nhds hxc) hz

theorem zero_on_of_germ (Ω : Set X) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (u : X → Y)
    (hprop : ∀ c ∈ Ω, ∀ r : ℝ, 0 < r → ball c r ⊆ Ω →
      u =ᶠ[𝓝 c] 0 → ∀ x ∈ ball c r, u x = 0)
    (c₀ : X) (hc₀ : c₀ ∈ Ω) (hzero : u =ᶠ[𝓝 c₀] 0) :
    ∀ x ∈ Ω, u x = 0 := by
  have hs : Ω ⊆ zeroGerms u := hconn.subset_of_closure_inter_subset (zeroGerms_open u)
    ⟨c₀,hc₀,hzero⟩ (zeroGerms_closure_inter Ω hΩ u hprop)
  intro x hx
  exact (hs hx).eq_of_nhds

theorem zero_on_of_ball (Ω : Set X) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (u : X → Y)
    (hprop : ∀ c ∈ Ω, ∀ r : ℝ, 0 < r → ball c r ⊆ Ω →
      u =ᶠ[𝓝 c] 0 → ∀ x ∈ ball c r, u x = 0)
    (c₀ : X) (hc₀ : c₀ ∈ Ω) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hzero : ∀ x ∈ ball c₀ r₀, u x = 0) :
    ∀ x ∈ Ω, u x = 0 :=
  zero_on_of_germ Ω hΩ hconn u hprop c₀ hc₀
    (eventually_of_mem (ball_mem_nhds c₀ hr₀) hzero)

end OQ14.LocalZeroPropagation

#print axioms OQ14.LocalZeroPropagation.zeroGerms_open
#print axioms OQ14.LocalZeroPropagation.zeroGerms_closure_inter
#print axioms OQ14.LocalZeroPropagation.zero_on_of_germ
#print axioms OQ14.LocalZeroPropagation.zero_on_of_ball
