import ConicalIntervalExpansion
import ConicalParticularBounds
import ConicalRadialWeakSystem
import ConeFiniteEnergy

/-! Actual radial finite energy removes the negative conical mode. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalFiniteExpansion
open MeasureTheory Set OQ14.ConicalRadialParticular OQ14.ConicalStaticVolume
  OQ14.ConicalCorrectionMoments OQ14.ConicalProjectedDerivative OQ14.ConicalFluxMoments
open scoped Topology

theorem positive_power_memLp (ν R : ℝ) (hν : 0 ≤ ν) :
    MemLp (power ν) 2 (volume.restrict (Ioo (0 : ℝ) R)) := by
  have hm : AEStronglyMeasurable (power ν) (volume.restrict (Ioo (0 : ℝ) R)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_rpow_const hν)).aestronglyMeasurable
  apply MemLp.of_bound hm (R^ν)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  simp only [power,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hr.1.le _)]
  exact Real.rpow_le_rpow hr.1.le hr.2.le hν

theorem particular_memLp (ν R : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (A B : ℝ → ℂ)
    (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0)) :
    MemLp (particular ν A B) 2 (volume.restrict (Ioo (0 : ℝ) R)) := by
  obtain ⟨MA,hMA⟩ := isCompact_Icc.exists_bound_of_continuousOn (hA.mono (show Icc (0 : ℝ) R ⊆ Ici 0 from fun _ hr => hr.1))
  obtain ⟨MB,hMB⟩ := isCompact_Icc.exists_bound_of_continuousOn (hB.mono (show Icc (0 : ℝ) R ⊆ Ici 0 from fun _ hr => hr.1))
  let M := max 0 (max MA MB)
  have hM : 0 ≤ M := le_max_left _ _
  have hb : ∀ s ∈ Icc (0 : ℝ) R, ‖A s‖ ≤ M ∧ ‖B s‖ ≤ M := by
    intro s hs
    exact ⟨(hMA s hs).trans ((le_max_left MA MB).trans (le_max_right _ _)),
      (hMB s hs).trans ((le_max_right MA MB).trans (le_max_right _ _))⟩
  have hreg : ContinuousOn (particular ν A B) (Ioo (0 : ℝ) R) := fun r hr =>
    (particular_hasDerivAt ν hν A B hA hB r hr.1).continuousAt.continuousWithinAt
  have hK : 0 ≤ ConicalParticularBounds.constant ν := by
    dsimp only [ConicalParticularBounds.constant]
    exact add_nonneg (div_nonneg (by linarith [hν.1]) (by linarith [hν.2])) (by norm_num)
  apply MemLp.of_bound (hreg.aestronglyMeasurable measurableSet_Ioo) (ConicalParticularBounds.constant ν*M*R)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  apply (ConicalParticularBounds.particular_norm_le ν hν A B hA hB r M hr.1 hM ?_).trans
    (mul_le_mul_of_nonneg_left hr.2.le (mul_nonneg hK hM))
  intro s hs
  exact hb s ⟨hs.1.le,(hs.2.trans hr.2).le⟩

theorem finite_energy_expansion (ν R : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1) (hR : 0 < R)
    (A B U F : ℝ → ℂ) (hA : ContinuousOn A (Ici 0)) (hB : ContinuousOn B (Ici 0))
    (hU : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt U (F r/(r : ℂ)^2-A r) r)
    (hF : ∀ r ∈ Ioo (0 : ℝ) R, HasDerivAt F (((ν*(ν+1) : ℝ) : ℂ)*U r+(r : ℂ)*B r) r)
    (henergy : MemLp U 2 (volume.restrict (Ioo (0 : ℝ) R))) :
    ∃ c : ℂ, ∀ r ∈ Ioo (0 : ℝ) R, U r=c*power ν r+particular ν A B r := by
  obtain ⟨c,b,hcb⟩ := ConicalIntervalExpansion.forced_expansion_on ν R hν A B U F hA hB hU hF
  have hv : MemLp (fun r => c*power ν r+particular ν A B r) 2 (volume.restrict (Ioo (0 : ℝ) R)) :=
    ((positive_power_memLp ν R hν.1.le).const_mul c).add (particular_memLp ν R hν A B hA hB)
  have hb : b=0 := ConeFiniteEnergy.negative_coefficient_zero ν R hν.1 hR U _ b henergy hv (by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    linear_combination hcb r hr)
  refine ⟨c,fun r hr => ?_⟩
  simpa only [hb,zero_mul,add_zero] using hcb r hr

theorem actual_projected_expansion (p : Data) (hν : p.exponent < 1) (k : ℝ) (hk0 : k≠0)
    (hk : |k| ≤ DynamicStaticLimit.frequencyRadius (coefficient p) p.cutoff.rOut) :
    ∃ c : ℂ, projected p k =ᵐ[volume.restrict (Ioo (0 : ℝ) p.cutoff.rIn)]
      fun r => c*power p.exponent r+particular p.exponent (radialCorrection p k) (tangentCorrection p k) r := by
  obtain ⟨U,F,_,_,hUa,_,hU,hF,he⟩ := ConicalRadialWeakSystem.exists_classical_system p k hk0 hk
  obtain ⟨c,hc⟩ := finite_energy_expansion p.exponent p.cutoff.rIn ⟨p.exponent_pos,hν⟩ p.cutoff.rIn_pos
    (radialCorrection p k) (tangentCorrection p k) U F
    (radialCorrection_continuous p k).continuousOn (tangentCorrection_continuous p k).continuousOn hU
    (fun r hr => by simpa only [p.separation] using hF r hr) he
  refine ⟨c,?_⟩
  filter_upwards [hUa,ae_restrict_mem measurableSet_Ioo] with r hr hm
  exact hr.trans (hc r hm)

end OQ14.ConicalFiniteExpansion

#print axioms OQ14.ConicalFiniteExpansion.positive_power_memLp
#print axioms OQ14.ConicalFiniteExpansion.particular_memLp
#print axioms OQ14.ConicalFiniteExpansion.finite_energy_expansion
#print axioms OQ14.ConicalFiniteExpansion.actual_projected_expansion
