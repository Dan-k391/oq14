import RegionalMaxwellLocalization
import WeakHelmholtzContinuation

/-! # Actual continuation of weak Maxwell electric fields across material cells

An actual global Maxwell field whose material-weighted electric field agrees
with a constant positive material on a connected open set obeys the actual
scalar weak Helmholtz equation there. Zero propagates across an interface
using an open bridge covered almost everywhere by the two material cells.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.RegionalMaxwellContinuation

open MeasureTheory Filter Metric Set OQ14.Maxwell
  OQ14.RegionalMaxwellLocalization
open scoped Topology

theorem material_frequency_ne (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : 0 < ε₀) :
    ((k*Real.sqrt ε₀ : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (mul_ne_zero hk (ne_of_gt (Real.sqrt_pos.mpr hε₀)))

theorem component_zero_of_field_zero (E : Field) (U : Set Space)
    (hz : E =ᵐ[volume.restrict U] 0) (i : Fin 3) :
    (fun x => E x i) =ᵐ[volume.restrict U] 0 := by
  filter_upwards [hz] with x hx
  exact congrFun hx i

theorem zero_germ_of_open (E : Field) (U : Set Space) (hU : IsOpen U)
    (hz : E =ᵐ[volume.restrict U] 0) (c : Space) (hc : c ∈ U) :
    ∃ r : ℝ, 0 < r ∧ E =ᵐ[volume.restrict (ball c r)] 0 := by
  obtain ⟨r,hr,hb⟩ := Metric.isOpen_iff.mp hU c hc
  exact ⟨r,hr,ae_restrict_of_ae_restrict_of_subset hb hz⟩

theorem electric_zero_on_weighted_region (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : 0 < ε₀)
    (ε : Space → ℝ) (Ω : Set Space) (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (E H : Field) (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (hε : ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3,
      (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i)
    (c : Space) (hc : c ∈ Ω)
    (hz : ∃ r : ℝ, 0 < r ∧ E =ᵐ[volume.restrict (ball c r)] 0) :
    E =ᵐ[volume.restrict Ω] 0 := by
  obtain ⟨r,hr,hzr⟩ := hz
  have hi (i : Fin 3) : (fun x => E x i) =ᵐ[volume.restrict Ω] 0 :=
    WeakHelmholtzContinuation.zero_on_connected_open Ω hΩ hconn
      ((k*Real.sqrt ε₀ : ℝ) : ℂ) (material_frequency_ne k ε₀ hk hε₀)
      (fun x => E x i) (hE i)
      (electric_weak_helmholtz_of_global k ε₀ hk hε₀ ε Ω E H hM hε hE i)
      c hc ⟨r,hr,component_zero_of_field_zero E (ball c r) hzr i⟩
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact funext hx

theorem weight_equality_on_constant_region (ε : Space → ℝ) (ε₀ : ℝ)
    (Ω : Set Space) (E : Field) (hε : ∀ᵐ x : Space, x ∈ Ω → ε x = ε₀) :
    ∀ᵐ x : Space, x ∈ Ω → ∀ i : Fin 3,
      (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i := by
  filter_upwards [hε] with x hx hΩ i
  rw [hx hΩ]

theorem electric_zero_across_interface (k ε₀ : ℝ) (hk : k ≠ 0) (hε₀ : 0 < ε₀)
    (ε : Space → ℝ) (E H : Field) (hM : MaterialMaxwell.TestMaxwell k ε E H)
    (hE : ∀ i, LocallyIntegrable (fun x => E x i))
    (U V B : Set Space) (hU : IsOpen U) (hV : IsOpen V) (hVc : IsPreconnected V)
    (hB : IsOpen B) (hBc : IsPreconnected B)
    (hcover : ∀ᵐ x : Space, x ∈ B → x ∈ U ∪ V)
    (hBU : (B ∩ U).Nonempty) (hBV : (B ∩ V).Nonempty)
    (hεV : ∀ᵐ x : Space, x ∈ V → ε x = ε₀)
    (hzero : E =ᵐ[volume.restrict U] 0) : E =ᵐ[volume.restrict V] 0 := by
  have hw : ∀ᵐ x : Space, x ∈ B → ∀ i : Fin 3,
      (ε x : ℂ)*E x i = (ε₀ : ℂ)*E x i := by
    apply weight_equality_of_material_or_zero ε ε₀ B E
    filter_upwards [hcover,hεV,ae_imp_of_ae_restrict hzero] with x hx hεx hzx hxB
    rcases hx hxB with hxU | hxV
    · exact Or.inr (fun i => congrFun (hzx hxU) i)
    · exact Or.inl (hεx hxV)
  obtain ⟨a,haB,haU⟩ := hBU
  have hzB := electric_zero_on_weighted_region k ε₀ hk hε₀ ε B hB hBc E H hM hE
    hw a haB (zero_germ_of_open E U hU hzero a haU)
  obtain ⟨b,hbB,hbV⟩ := hBV
  exact electric_zero_on_weighted_region k ε₀ hk hε₀ ε V hV hVc E H hM hE
    (weight_equality_on_constant_region ε ε₀ V E hεV) b hbV
    (zero_germ_of_open E B hB hzB b hbB)

end OQ14.RegionalMaxwellContinuation

#print axioms OQ14.RegionalMaxwellContinuation.material_frequency_ne
#print axioms OQ14.RegionalMaxwellContinuation.component_zero_of_field_zero
#print axioms OQ14.RegionalMaxwellContinuation.zero_germ_of_open
#print axioms OQ14.RegionalMaxwellContinuation.electric_zero_on_weighted_region
#print axioms OQ14.RegionalMaxwellContinuation.weight_equality_on_constant_region
#print axioms OQ14.RegionalMaxwellContinuation.electric_zero_across_interface
