import ConicalLocalSystem
import ConicalFiniteExpansion

/-! Finite-energy expansion derived from actual local spatial gradient and Gauss data. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ConicalLocalExpansion
open MeasureTheory Set OQ14.ConicalStaticVolume OQ14.ConicalProjectionData
  OQ14.ConicalGraphProjection OQ14.ConicalRadialParticular
open scoped Topology

theorem actual_projected_expansion {p : Data} {a : ℝ} (s : System p a)
    (ha : 0 < a) (hai : a < p.cutoff.rIn) (hν : p.exponent < 1) :
    ∃ c : ℂ, projected p s.graph =ᵐ[volume.restrict (Ioo (0 : ℝ) a)]
      fun r => c*power p.exponent r+particular p.exponent (radialCorrection s) (tangentCorrection s) r := by
  obtain ⟨U,F,_,_,hUa,_,hU,hF,he⟩ := ConicalLocalSystem.exists_classical_system s hai
  obtain ⟨c,hc⟩ := ConicalFiniteExpansion.finite_energy_expansion p.exponent a ⟨p.exponent_pos,hν⟩ ha
    (radialCorrection s) (tangentCorrection s) U F
    (radialCorrection_continuous s).continuousOn (tangentCorrection_continuous s).continuousOn hU
    (fun r hr => by simpa only [p.separation] using hF r hr) he
  refine ⟨c,?_⟩
  filter_upwards [hUa,ae_restrict_mem measurableSet_Ioo] with r hr hm
  exact hr.trans (hc r hm)

end OQ14.ConicalLocalExpansion

#print axioms OQ14.ConicalLocalExpansion.actual_projected_expansion
