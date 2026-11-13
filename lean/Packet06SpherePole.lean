import Packet06Laurent
import Packet06Cokernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace OQ14.Packet06SpherePole
open Complex Filter OQ14.Packet06SectorOperator OQ14.Packet06SectorCrossing
open scoped Topology

/-- The actual restricted electric-sector inverse has a simple pole at every
simple dipole determinant root for algebraic n. -/
theorem inverse_order_eq_neg_one (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (hs : deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z ≠ 0) :
    (inverse_meromorphicAt n hn z).order = (-1 : ℤ) := by
  apply Packet06PoleOrder.inverse_order_eq_neg_one (block n hn) (blockDerivative n hn z) z
    (block_hasDerivAt n hn z) (numerator n hn z) (leftFunctional n hn z)
  · intro v hv
    obtain ⟨c,hc,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd v).mp hv
    exact ⟨c,hc⟩
  · exact left_annihilates n hn z hz hd
  · exact crossing_nonzero n hn z hz hd hs
  · exact block_punctured_isUnit n hn z
  · exact block_not_isUnit n hn z hz hd

/-- Actual sector inverse Laurent expansion, with its reciprocal residue. -/
theorem inverse_simple_expansion (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0)
    (hs : deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z ≠ 0) :
    ∃ (R : Sector →L[ℂ] Sector) (B : ℂ → Sector →L[ℂ] Sector),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, R x = (leftFunctional n hn z x /
        leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))) • numerator n hn z) ∧
      Tendsto (fun w => (w-z) • Ring.inverse (block n hn w)) (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ w in 𝓝[≠] z, Ring.inverse (block n hn w) = (w-z)⁻¹ • R + B w) := by
  apply Packet06Laurent.simple_inverse_expansion (block n hn) (blockDerivative n hn z) z
    (block_hasDerivAt n hn z) (numerator n hn z) (leftFunctional n hn z)
  · intro v hv
    obtain ⟨c,hc,_⟩ := (kernel_iff_unique_multiple n hn hna z hz hd v).mp hv
    exact ⟨c,hc⟩
  · exact left_annihilates n hn z hz hd
  · exact crossing_nonzero n hn z hz hd hs
  · exact inverse_meromorphicAt n hn z
  · exact block_punctured_isUnit n hn z
  · exact block_not_isUnit n hn z hz hd

/-- Algebraicity makes every nonzero dipole determinant root simple. -/
theorem determinant_simple (n : ℝ) (hn : 1 < n) (hna : IsAlgebraic ℚ (n : ℂ))
    (z : ℂ) (hz : z ≠ 0) (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    deriv (ModalAlgebra.tmDet 1 (n : ℂ)) z ≠ 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hn1 : (n : ℂ) ≠ 1 := by exact_mod_cast (ne_of_gt hn)
  have hnm : (n : ℂ) ≠ -1 := by exact_mod_cast (show n ≠ -1 by linarith)
  exact (ModalTMIsolation.isolated_degree 1 n z hna hn0 hn1 hnm hz hd).1

/-- Full actual sector Laurent and cokernel endpoint at a nonzero dipole root. -/
theorem actual_sector_pole_and_cokernel (n : ℝ) (hn : 1 < n)
    (hna : IsAlgebraic ℚ (n : ℂ)) (z : ℂ) (hz : z ≠ 0)
    (hd : ModalAlgebra.tmDet 1 (n : ℂ) z = 0) :
    (inverse_meromorphicAt n hn z).order = (-1 : ℤ) ∧
    ∃ (R : Sector →L[ℂ] Sector) (B : ℂ → Sector →L[ℂ] Sector),
      R ≠ 0 ∧ AnalyticAt ℂ B z ∧
      (∀ x, R x = (leftFunctional n hn z x /
        leftFunctional n hn z (blockDerivative n hn z (numerator n hn z))) • numerator n hn z) ∧
      Tendsto (fun w => (w-z) • Ring.inverse (block n hn w)) (𝓝[≠] z) (𝓝 R) ∧
      (∀ᶠ w in 𝓝[≠] z, Ring.inverse (block n hn w) = (w-z)⁻¹ • R + B w) ∧
      (block n hn z).comp (B z) + (blockDerivative n hn z).comp R = 1 ∧
      LinearMap.range (block n hn z).toLinearMap = LinearMap.ker (leftFunctional n hn z).toLinearMap ∧
      IsClosed (Set.range (block n hn z)) ∧
      Module.finrank ℂ (Sector ⧸ LinearMap.range (block n hn z).toLinearMap) = 1 := by
  have hs := determinant_simple n hn hna z hz hd
  refine ⟨inverse_order_eq_neg_one n hn hna z hz hd hs, ?_⟩
  obtain ⟨R,B,hR,hB,hform,hlim,hexp⟩ := inverse_simple_expansion n hn hna z hz hd hs
  have hconstant := Packet06Cokernel.laurent_constant_identity (block n hn) (blockDerivative n hn z)
    z R B (block_hasDerivAt n hn z) hB (block_punctured_isUnit n hn z) hexp
  have hann := left_annihilates n hn z hz hd
  have hcross := crossing_nonzero n hn z hz hd hs
  refine ⟨R,B,hR,hB,hform,hlim,hexp,hconstant,?_⟩
  refine ⟨Packet06Cokernel.range_eq_kernel _ _ _ _ _ _ _ hann hform hconstant,
    Packet06Cokernel.range_closed _ _ _ _ _ _ _ hann hform hconstant, ?_⟩
  exact Packet06Cokernel.quotient_finrank_one _ _ _ _ _ _ _ hann hform hconstant
    (blockDerivative n hn z (numerator n hn z)) hcross

#print axioms OQ14.Packet06SpherePole.determinant_simple
#print axioms OQ14.Packet06SpherePole.actual_sector_pole_and_cokernel

#print axioms OQ14.Packet06SpherePole.inverse_order_eq_neg_one
#print axioms OQ14.Packet06SpherePole.inverse_simple_expansion
end OQ14.Packet06SpherePole
