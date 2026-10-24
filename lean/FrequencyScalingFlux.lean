import RestrictedTEActualFields

/-! Frequency scaling of the plane flux.

Under the dilation of the plane `ξ ↦ k ξ` (`k > 0`) with the amplitude factor `k` on the fields, the plane flux
density `E × conj H` picks up the factor `k ^ 2` (`fieldFlux_scale`), and the flux through the square of half-side
`L` of the scaled fields equals the flux through the square of half-side `k L` of the original fields
(`passage_scale`, `bypass_scale`, through the Haar scaling of the plane measure and `k • Dsq L = Dsq (k * L)`).
Hence the counted-subspace predicate transfers from the square `Dsq (k * L)` to the square `Dsq L` with the same
scattering map, the same power and the same thresholds (`isCounted_scale`). -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.FrequencyScalingFlux
open MeasureTheory
open OQ14.RestrictedTEActualFields (fieldFlux fieldFlux_eq)
open OQ14.RestrictedTEPassageTransfer (passage bypass)
open OQ14.RestrictedTEActualSquare (Dsq)
open OQ14.RestrictedTEActualCounting (IsCounted)
open scoped ComplexConjugate Pointwise

abbrev Plane := PlaneInverseCube.Plane
abbrev Vector := Maxwell.Vector
abbrev FieldMap := OQ14.RestrictedTEActualFields.FieldMap
abbrev Idx := SymmetricHarmonicJets.Index

/-! ### The dilated field -/

/-- The dilated and amplified plane field `ξ ↦ k G (k ξ)`. -/
def scalePlane (k : ℝ) (G : Plane → Vector) : Plane → Vector := fun ξ => (k : ℂ) • G (k • ξ)

/-- The dilation with amplitude factor as a `ℂ`-linear map on plane fields. -/
def scalePlaneLin (k : ℝ) : (Plane → Vector) →ₗ[ℂ] (Plane → Vector) where
  toFun := scalePlane k
  map_add' := by
    intro F G
    funext ξ
    simp only [scalePlane, Pi.add_apply, smul_add]
  map_smul' := by
    intro c F
    funext ξ
    simp only [scalePlane, Pi.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

/-- The dilated and amplified linear field family. -/
def scaleMap (k : ℝ) (E : FieldMap) : FieldMap := (scalePlaneLin k).comp E

theorem scaleMap_apply (k : ℝ) (E : FieldMap) (x : Idx →₀ ℂ) (ξ : Plane) :
    scaleMap k E x ξ = (k : ℂ) • E x (k • ξ) := rfl

/-! ### The flux of the dilated fields -/

theorem conjugate_real_smul (k : ℝ) (v : Vector) :
    Maxwell.conjugate ((k : ℂ) • v) = (k : ℂ) • Maxwell.conjugate v := by
  funext j
  simp only [Maxwell.conjugate, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]

theorem fieldFlux_scale (k : ℝ) (E H : FieldMap) (x : Idx →₀ ℂ) (ξ : Plane) :
    fieldFlux (scaleMap k E) (scaleMap k H) x ξ = ((k : ℂ) ^ 2) * fieldFlux E H x (k • ξ) := by
  rw [fieldFlux_eq, fieldFlux_eq]
  simp only [scaleMap_apply, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
  ring

theorem fieldFlux_scale_fun (k : ℝ) (E H : FieldMap) (x : Idx →₀ ℂ) :
    fieldFlux (scaleMap k E) (scaleMap k H) x = fun ξ => ((k : ℂ) ^ 2) * fieldFlux E H x (k • ξ) :=
  funext (fieldFlux_scale k E H x)

/-! ### The dilated square -/

theorem smul_Dsq (k L : ℝ) (hk : 0 < k) : k • Dsq L = Dsq (k * L) := by
  ext q
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hk.ne']
  have h : ∀ a : ℝ, k⁻¹ * |a| < L ↔ |a| < k * L := fun a => by rw [inv_mul_lt_iff₀ hk]
  simp only [Dsq, Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hk, h]

theorem smul_Dsq_compl (k L : ℝ) (hk : 0 < k) : k • (Dsq L)ᶜ = (Dsq (k * L))ᶜ := by
  ext q
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hk.ne']
  have h : ∀ a : ℝ, k⁻¹ * |a| < L ↔ |a| < k * L := fun a => by rw [inv_mul_lt_iff₀ hk]
  simp only [Dsq, Set.mem_compl_iff, Set.mem_setOf_eq, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_inv,
    abs_of_pos hk, h]

/-! ### Scaling of the plane integral -/

theorem finrank_plane : Module.finrank ℝ Plane = 2 := by
  simp [finrank_euclideanSpace]

theorem setIntegral_plane_scale (k : ℝ) (hk : 0 < k) (s : Set Plane) (F : Plane → ℂ) :
    (∫ ξ in s, F (k • ξ) ∂volume) = (((k ^ 2)⁻¹ : ℝ) : ℂ) * ∫ ξ in k • s, F ξ ∂volume := by
  rw [Measure.setIntegral_comp_smul volume F s hk.ne', finrank_plane,
    abs_of_pos (inv_pos.mpr (pow_pos hk 2)), Complex.real_smul]

theorem setIntegral_plane_scale_real (k : ℝ) (hk : 0 < k) (s : Set Plane) (G : Plane → ℝ) :
    (∫ ξ in s, G (k • ξ) ∂volume) = (k ^ 2)⁻¹ * ∫ ξ in k • s, G ξ ∂volume := by
  rw [Measure.setIntegral_comp_smul volume G s hk.ne', finrank_plane,
    abs_of_pos (inv_pos.mpr (pow_pos hk 2)), smul_eq_mul]

/-! ### Passage and bypass of the dilated flux -/

theorem passage_scale (k L : ℝ) (hk : 0 < k) (F : Plane → ℂ) :
    passage volume (Dsq L) (fun ξ => ((k : ℂ) ^ 2) * F (k • ξ)) = passage volume (Dsq (k * L)) F := by
  have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have h : ((k : ℂ) ^ 2) * (((k ^ 2)⁻¹ : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp
  unfold passage
  congr 1
  rw [integral_const_mul, setIntegral_plane_scale k hk, smul_Dsq k L hk, ← mul_assoc, h, one_mul]

theorem bypass_scale (k L : ℝ) (hk : 0 < k) (F : Plane → ℂ) :
    bypass volume (Dsq L) (fun ξ => ((k : ℂ) ^ 2) * F (k • ξ)) = bypass volume (Dsq (k * L)) F := by
  have h1 : ∀ ξ : Plane, ‖((k : ℂ) ^ 2) * F (k • ξ)‖ = k ^ 2 * ‖F (k • ξ)‖ := by
    intro ξ
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  have hk2 : k ^ 2 ≠ 0 := (pow_pos hk 2).ne'
  unfold bypass
  simp only [h1]
  rw [integral_const_mul, setIntegral_plane_scale_real k hk ((Dsq L)ᶜ) (fun ξ => ‖F ξ‖),
    smul_Dsq_compl k L hk, ← mul_assoc, mul_inv_cancel₀ hk2, one_mul]

/-! ### Transfer of the counted-subspace predicate -/

theorem isCounted_scale (k L : ℝ) (hk : 0 < k) (W : Submodule ℂ (Idx →₀ ℂ))
    (T : (Idx →₀ ℂ) →ₗ[ℂ] OQ14.ChannelScatteringMap.Ambient) (E H : FieldMap) (τ η δ : ℝ)
    (h : IsCounted W T (fun a => passage volume (Dsq (k * L)) (fieldFlux E H a))
      (fun a => bypass volume (Dsq (k * L)) (fieldFlux E H a)) τ η δ) :
    IsCounted W T (fun a => passage volume (Dsq L) (fieldFlux (scaleMap k E) (scaleMap k H) a))
      (fun a => bypass volume (Dsq L) (fieldFlux (scaleMap k E) (scaleMap k H) a)) τ η δ := by
  intro a ha
  obtain ⟨h1, h2, h3⟩ := h a ha
  refine ⟨h1, ?_, ?_⟩
  · show η * ‖T a‖ ^ 2 ≤ passage volume (Dsq L) (fieldFlux (scaleMap k E) (scaleMap k H) a)
    rw [fieldFlux_scale_fun, passage_scale k L hk]
    exact h2
  · show bypass volume (Dsq L) (fieldFlux (scaleMap k E) (scaleMap k H) a) ≤
      δ * OQ14.RestrictedTEIncoming.physicalPower a
    rw [fieldFlux_scale_fun, bypass_scale k L hk]
    exact h3

end OQ14.FrequencyScalingFlux

#print axioms OQ14.FrequencyScalingFlux.scaleMap_apply
#print axioms OQ14.FrequencyScalingFlux.conjugate_real_smul
#print axioms OQ14.FrequencyScalingFlux.fieldFlux_scale
#print axioms OQ14.FrequencyScalingFlux.fieldFlux_scale_fun
#print axioms OQ14.FrequencyScalingFlux.smul_Dsq
#print axioms OQ14.FrequencyScalingFlux.smul_Dsq_compl
#print axioms OQ14.FrequencyScalingFlux.finrank_plane
#print axioms OQ14.FrequencyScalingFlux.setIntegral_plane_scale
#print axioms OQ14.FrequencyScalingFlux.setIntegral_plane_scale_real
#print axioms OQ14.FrequencyScalingFlux.passage_scale
#print axioms OQ14.FrequencyScalingFlux.bypass_scale
#print axioms OQ14.FrequencyScalingFlux.isCounted_scale
