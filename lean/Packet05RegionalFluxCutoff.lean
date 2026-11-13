import Packet05RegionalDivergence
import Packet05ScalarCutoffTesting

/-! Extend a locally divergence-free L² flux with an outer cutoff. Its
new divergence is exactly the cutoff-gradient source and vanishes wherever
the cutoff is locally constant. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05RegionalFluxCutoff
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.Packet05RegionalDivergence
open scoped Topology

def cutFlux (κ : Test) (P : L2Vector) : L2Vector := fun j =>
  scaleL2 κ.function κ.regular.continuous κ.compact (P j)

def cutFluxSource (κ : Test) (P : L2Vector) : L2Scalar :=
  ∑ j : Fin 3, scaleL2 (fun x => dcoord κ.function x j) (partial_continuous κ.regular j)
    (κ.compact.fderiv_apply ℝ (basis j)) (P j)

theorem derivativePair_product_cutoff (κ φ : Test) (u : L2Scalar) (j : Fin 3) :
    derivativePair (smoothProductTest κ φ.function φ.regular) j u =
      derivativePair φ j (scaleL2 κ.function κ.regular.continuous κ.compact u) +
      valuePair φ (scaleL2 (fun x => dcoord κ.function x j) (partial_continuous κ.regular j)
        (κ.compact.fderiv_apply ℝ (basis j)) u) := by
  rw [derivativePair_smooth_product]
  simp only [derivativePair, valuePair, scalarProduct_scale_smooth, testPair_integral]
  congr 1
  · apply integral_congr_ae
    filter_upwards [scaleL2_ae κ.function κ.regular.continuous κ.compact u] with x hu
    rw [hu]
    ring
  · apply integral_congr_ae
    filter_upwards [scaleL2_ae (fun x => dcoord κ.function x j) (partial_continuous κ.regular j)
      (κ.compact.fderiv_apply ℝ (basis j)) u] with x hd
    rw [hd]
    ring

theorem regional_flux_cutoff_divergence (V : Set Space) (P : L2Vector)
    (hdiv : HasDivergenceOn V P 0) (κ : Test) (hκV : tsupport κ.function ⊆ V) :
    HasWeakDivergence (cutFlux κ P) (cutFluxSource κ P) := by
  intro φ
  have hsupport : tsupport (smoothProductTest κ φ.function φ.regular).function ⊆ V :=
    tsupport_mul_subset_left.trans hκV
  have hh := hdiv (smoothProductTest κ φ.function φ.regular) hsupport
  simp only [map_zero, zero_add] at hh
  rw [derivativePair_product_cutoff, derivativePair_product_cutoff, derivativePair_product_cutoff] at hh
  simp only [cutFlux, cutFluxSource, Fin.sum_univ_three, map_add]
  linear_combination hh

theorem cutoff_source_vanishes_on (κ : Test) (P : L2Vector) (S : Set Space)
    (hκ : ∀ x ∈ S, κ.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ))) :
    ∀ᵐ x ∂volume, x ∈ S → cutFluxSource κ P x = 0 := by
  let X (j : Fin 3) := scaleL2 (fun x => dcoord κ.function x j) (partial_continuous κ.regular j)
    (κ.compact.fderiv_apply ℝ (basis j)) (P j)
  have ha : ∀ᵐ x ∂volume, ∀ j, X j x = dcoord κ.function x j * P j x :=
    ae_all_iff.mpr (fun j => scaleL2_ae _ _ _ _)
  filter_upwards [ha, Lp.coeFn_add (X 0) (X 1), Lp.coeFn_add (X 0 + X 1) (X 2)] with x ha h01 h012 hx
  have hz (j : Fin 3) : dcoord κ.function x j = 0 := by
    simp [dcoord, (hκ x hx).fderiv_eq]
  unfold cutFluxSource
  rw [Fin.sum_univ_three]
  change (X 0 + X 1 + X 2 : L2Scalar) x = 0
  rw [h012]
  simp only [Pi.add_apply]
  rw [h01]
  simp only [Pi.add_apply, ha, hz, zero_mul, add_zero]

end OQ14.Packet05RegionalFluxCutoff
#print axioms OQ14.Packet05RegionalFluxCutoff.derivativePair_product_cutoff
#print axioms OQ14.Packet05RegionalFluxCutoff.regional_flux_cutoff_divergence
#print axioms OQ14.Packet05RegionalFluxCutoff.cutoff_source_vanishes_on
