import CompactLaurent
import VolumeAnalyticAlternative

/-! # Actual volume inverse with finite-rank principal Laurent coefficients -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.VolumeLaurent

open Metric OQ14.DynamicConvolution OQ14.ComplexConvolutionAnalytic
open OQ14.StaticCoefficient (Coefficient)
open scoped Topology

theorem finite_rank_laurent (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (z₀ : ℂ) :
    ∃ (n : ℕ) (G : ℂ → VectorL2 →L[ℂ] VectorL2)
      (p : FormalMultilinearSeries ℂ ℂ (VectorL2 →L[ℂ] VectorL2)),
      AnalyticAt ℂ G z₀ ∧
      (∀ j : ℕ, FiniteDimensional ℂ (LinearMap.range (p.coeff j))) ∧
      ∀ᶠ z in 𝓝[≠] z₀,
        HasSum (fun j : ℕ => ((z-z₀)^n)⁻¹ • ((z-z₀)^j • p.coeff j))
          (Ring.inverse (volumeBlock c z R) - G z) := by
  have hbase : ∃ z : ℂ, IsUnit (1-compactPart c z R) :=
    ⟨0, by rw [compactPart_zero, sub_zero]; exact isUnit_one⟩
  obtain ⟨n, G, p, hG, hp, hseries⟩ := CompactLaurent.finite_rank_laurent
    (fun z => compactPart c z R) (compactPart_differentiable c R hR)
      (fun z => compactPart_compact c z R hc) hbase z₀
  let S : VectorL2 →L[ℂ] VectorL2 := Ring.inverse (StaticNewton.volumeBlock c)
  let L : (VectorL2 →L[ℂ] VectorL2) →L[ℂ] (VectorL2 →L[ℂ] VectorL2) :=
    (ContinuousLinearMap.compL ℂ VectorL2 VectorL2 VectorL2).flip S
  let q := L.compFormalMultilinearSeries p
  refine ⟨n, fun z => L (G z), q, (L.analyticAt (G z₀)).comp (f := G) hG, ?_, ?_⟩
  · intro j
    have hq : q.coeff j = (p.coeff j).comp S := rfl
    rw [hq]
    letI := hp j
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (p.coeff j))
    exact LinearMap.range_comp_le_range S.toLinearMap (p.coeff j).toLinearMap
  · filter_upwards [hseries, VolumeAnalyticAlternative.pencil_punctured_isUnit c R hR hc z₀]
      with z hs hz
    have hm := L.hasSum hs
    have hv : L (Ring.inverse (1-compactPart c z R)) = Ring.inverse (volumeBlock c z R) :=
      (VolumeAnalyticAlternative.inverse_factor c z R hz).symm
    simpa only [map_smul, map_sub, hv] using hm

end OQ14.VolumeLaurent

#print axioms OQ14.VolumeLaurent.finite_rank_laurent
