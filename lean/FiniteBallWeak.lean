import FiniteParityWeak
import FiniteSphereActualSources

/-! Actual finite-ball inverse weak Maxwell equations with smallness derived from its geometry. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.FiniteBallWeak
open MeasureTheory Metric MaterialMaxwell
open scoped Topology
abbrev Space := FourierL2.Space
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
theorem smallness (p : ℝ → ι → Space) (ρ χ R k b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hb : b ≠ 0)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R) :
    ∃ η > 0, ∀ a : ℝ, ∀ ha : 0 < a, a < η → ∃ ha1 : a ≤ 1,
      ParityReactionVolume.perturbationBound (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1) k (b/a) < 1 := by
  let V := FiniteSphereScale.totalVolume (ι := ι) ρ
  let K := StaticSphereScale.linearBound χ V k R b
  have hV : 0 ≤ V := FiniteSphereScale.totalVolume_nonnegative ρ hρ.le
  have hK : 0 ≤ K := StaticSphereScale.linearBound_nonnegative χ V k R b hχ hV
  obtain ⟨η,hη,hsmall⟩ := StaticSphereScale.linear_smallness K hK
  refine ⟨min η 1,lt_min hη zero_lt_one,?_⟩
  intro a ha had
  have ha1 : a ≤ 1 := (had.trans_le (min_le_right _ _)).le
  refine ⟨ha1,?_⟩
  have hv := FiniteSphereScale.union_volume_bound (p a) ρ a hρ.le ha.le
  have hp := StaticSphereScale.perturbation_linear
    (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1) χ V k b a hχ hV ha ha1 hb le_rfl hv
  exact hp.trans_lt ((hsmall a ha.le (had.trans_le (min_le_left _ _))).trans (by norm_num))

omit [DecidableEq ι] in
theorem actual_inverse (p : ℝ → ι → Space) (ρ χ R k b : ℝ) (hρ : 0 < ρ) (hχ : 0 ≤ χ) (hb : b ≠ 0)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖p a l‖+ρ ≤ R)
    (q : ℝ → κ → Space) (j : ℝ → κ → Fin 3) (A : ℝ → κ → ℂ) :
    ∃ η > 0, ∀ a : ℝ, 0 < a → a < η →
      let c := FiniteSphereStatic.coefficient (p a) (fun _ => ρ*a) χ hχ
      let u := FiniteSphereActualSources.solution p ρ χ R k b hρ hχ hi q j A a
      TestMaxwell k (dielectric c)
        (ParityMaterialField.total c k (b/a) u (FiniteHerglotzFlux.electric k (fun _ => true) (q a) (j a) (A a)))
        (ParityMaterialMaxwell.magnetic c k (b/a) u (FiniteHerglotzFlux.magnetic k (fun _ => true) (q a) (j a) (A a))) := by
  obtain ⟨η,hη,hs⟩ := smallness p ρ χ R k b hρ hχ hb hi
  refine ⟨η,hη,?_⟩
  intro a ha had
  obtain ⟨ha1,hsmall⟩ := hs a ha had
  have hm := FiniteParityWeak.material_inverse _ (FiniteSphereActualSources.data p ρ χ R hρ hχ hi a ha ha1)
    k (b/a) hsmall (fun _ => true) (q a) (j a) (A a)
  simpa only [FiniteSphereActualSources.solution,FiniteSphereIllumination.datum,
    dif_pos (show 0 < a ∧ a ≤ 1 from ⟨ha,ha1⟩),FiniteSphereActualSources.data] using hm

end OQ14.FiniteBallWeak
#print axioms OQ14.FiniteBallWeak.smallness
#print axioms OQ14.FiniteBallWeak.actual_inverse
