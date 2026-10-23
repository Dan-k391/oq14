import ConicalSeparatedSystem
import ConicalFiniteExpansion

/-! Finite-energy expansion for the literal separated conical Maxwell field. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ConicalSeparatedExpansion
open MeasureTheory Set OQ14.ConicalStaticVolume OQ14.ConicalSeparatedCorrection
  OQ14.ConicalGraphProjection OQ14.ConicalRadialParticular
open scoped Topology

theorem actual_projected_expansion (p : Data) (hν : p.exponent < 1) (a k : ℝ) (ha : 0 < a) (hai : a < p.cutoff.rIn) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalSeparatedSource.material p a) a) :
    ∃ c : ℂ, projected p (ConicalGradientGraph.separated p a k hai) =ᵐ[volume.restrict (Ioo (0 : ℝ) a)]
      fun r => c*power p.exponent r+particular p.exponent (radialCorrection p a k) (tangentCorrection p a k) r := by
  obtain ⟨U,F,_,_,hUa,_,hU,hF,he⟩ := ConicalSeparatedSystem.exists_classical_system p a k hai ha.le hk0 hk
  obtain ⟨c,hc⟩ := ConicalFiniteExpansion.finite_energy_expansion p.exponent a ⟨p.exponent_pos,hν⟩ ha
    (radialCorrection p a k) (tangentCorrection p a k) U F
    (radialCorrection_continuous p a k hai).continuousOn (tangentCorrection_continuous p a k hai).continuousOn hU
    (fun r hr => by simpa only [p.separation] using hF r hr) he
  refine ⟨c,?_⟩
  filter_upwards [hUa,ae_restrict_mem measurableSet_Ioo] with r hr hm
  exact hr.trans (hc r hm)

end OQ14.ConicalSeparatedExpansion

#print axioms OQ14.ConicalSeparatedExpansion.actual_projected_expansion
