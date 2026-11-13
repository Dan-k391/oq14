import Packet05ActualContinuous
import Packet05FiniteBranchMaximum

/-! Actual attained material-side electric maximum at a flat jump. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4800000
namespace OQ14.Packet05ActualMaximum
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.Packet05ActualContinuous OQ14.Packet05FiniteBranchMaximum
open scoped Topology

def physicalAmplitude (R : Fin 3 → Space → ℂ) (x : Space) : ℝ :=
  Real.sqrt (∑ j : Fin 3, ‖R j x‖^2)

theorem physicalAmplitude_continuous (R : Fin 3 → Space → ℂ) (hR : ∀ j, Continuous (R j)) :
    Continuous (physicalAmplitude R) := by
  unfold physicalAmplitude
  apply Continuous.sqrt
  simp only [Fin.sum_univ_three]
  exact (((hR 0).norm.pow 2).add ((hR 1).norm.pow 2)).add ((hR 2).norm.pow 2)

theorem actual_flat_two_sided_maximum {Ω U : Set Space}
    (hΩ : IsOpen Ω) (c₀ : Space) (r₀ R₀ : ℝ) (hr₀ : r₀ < R₀)
    (κ₀ : DomainCurl.Test Ω) (hκ₀2 : ContDiff ℝ 2 κ₀.function)
    (hS₀ : Metric.ball c₀ R₀ ⊆ Ω)
    (hκ₀ : ∀ x ∈ Metric.ball c₀ R₀, κ₀.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A₀ B₀ : ℝ) (hA₀ : 0 ≤ A₀) (hB₀ : 0 ≤ B₀)
    (hvκ₀ : ∀ x, ‖κ₀.function x‖ ≤ A₀) (hdκ₀ : ∀ l x, ‖dcoord κ₀.function x l‖ ≤ B₀)
    (k d : ℝ) (hk : k ≠ 0) (hd : 0 ≤ d) (E H : DomainCurl.HCurl Ω)
    (hM : WeakConservation.WeakMaxwell k (fun _ => 1)
      (FlatDifferenceCoercivity.dielectric d) E H)
    (ζ₀ : WeakConservation.RealTest (Metric.ball c₀ r₀))
    (hζ₀2 : ContDiff ℝ 2 ζ₀.complexTest.function) (η₀ : DomainCurl.Test (Metric.ball c₀ r₀))
    (hη₀ : ∀ x ∈ tsupport ζ₀.function, η₀.function x = 1)
    (hζ₀ : ∀ x, ‖ζ₀.function x‖ ≤ 1) (L₀ C₀ D₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hgrad₀ : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ₀ x) ≤ L₀^2)
    (hηbound₀ : ∀ x, ‖η₀.function x‖ ≤ C₀)
    (hζder₀ : ∀ l x, ‖dcoord ζ₀.complexTest.function x l‖ ≤ D₀)
    (hUopen : IsOpen U) (hU : U ⊆ Metric.ball c₀ r₀)
    (hζunit₀ : ∀ x ∈ U, ζ₀.complexTest.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (c₁ : Space) (r₁ R₁ : ℝ) (hr₁ : r₁ < R₁)
    (κ₁ : DomainCurl.Test U) (hκ₁2 : ContDiff ℝ 2 κ₁.function)
    (hS₁ : Metric.ball c₁ R₁ ⊆ U)
    (hκ₁ : ∀ x ∈ Metric.ball c₁ R₁, κ₁.function =ᶠ[𝓝 x] (fun _ => (1 : ℂ)))
    (A₁ B₁ : ℝ) (hA₁ : 0 ≤ A₁) (hB₁ : 0 ≤ B₁)
    (hvκ₁ : ∀ x, ‖κ₁.function x‖ ≤ A₁) (hdκ₁ : ∀ l x, ‖dcoord κ₁.function x l‖ ≤ B₁)
    (ζ₁ : WeakConservation.RealTest (Metric.ball c₁ r₁))
    (hζ₁2 : ContDiff ℝ 2 ζ₁.complexTest.function) (η₁ : DomainCurl.Test (Metric.ball c₁ r₁))
    (hη₁ : ∀ x ∈ tsupport ζ₁.function, η₁.function x = 1)
    (hζ₁ : ∀ x, ‖ζ₁.function x‖ ≤ 1) (L₁ C₁ D₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hgrad₁ : ∀ x, WeakEnergy.realEnergy (WeakEnergy.gradient ζ₁ x) ≤ L₁^2)
    (hηbound₁ : ∀ x, ‖η₁.function x‖ ≤ C₁)
    (hζder₁ : ∀ l x, ‖dcoord ζ₁.complexTest.function x l‖ ≤ D₁)
    (Vminus Vplus K : Set Space) (hVm : IsOpen Vminus) (hVp : IsOpen Vplus)
    (hVmU : Vminus ⊆ U) (hVpU : Vplus ⊆ U)
    (hζm : ∀ x ∈ Vminus, ζ₁.complexTest.function x = 1)
    (hζp : ∀ x ∈ Vplus, ζ₁.complexTest.function x = 1)
    (hεm : ∀ x ∈ Vminus, FlatDifferenceCoercivity.dielectric d x = 1)
    (hεp : ∀ x ∈ Vplus, FlatDifferenceCoercivity.dielectric d x = 1+d)
    (hK : IsCompact K) (hne : K.Nonempty) (hcover : K ⊆ closure Vminus ∪ closure Vplus) :
    ∃ Rminus Rplus : Fin 3 → Space → ℂ,
      (∀ j, Continuous (Rminus j)) ∧ (∀ j, Continuous (Rplus j)) ∧
      (∀ j, (fun x => E.val.1 j x) =ᵐ[volume.restrict Vminus] Rminus j) ∧
      (∀ j, (fun x => E.val.1 j x) =ᵐ[volume.restrict Vplus] Rplus j) ∧
      ∃ b : Fin 2, ∃ x ∈ K ∩ (if b = 0 then closure Vminus else closure Vplus),
        ∀ b' : Fin 2, ∀ y ∈ K ∩ (if b' = 0 then closure Vminus else closure Vplus),
          physicalAmplitude (if b' = 0 then Rminus else Rplus) y ≤
            physicalAmplitude (if b = 0 then Rminus else Rplus) x := by
  have hp : (1+d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨Rm,hRmc,hRmae⟩ := actual_flat_one_sided_continuous hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
    Vminus hVmU hζm 1 (by norm_num) hεm hVm
  obtain ⟨Rp,hRpc,hRpae⟩ := actual_flat_one_sided_continuous hΩ c₀ r₀ R₀ hr₀ κ₀ hκ₀2 hS₀ hκ₀
    A₀ B₀ hA₀ hB₀ hvκ₀ hdκ₀ k d hk hd E H hM ζ₀ hζ₀2 η₀ hη₀ hζ₀
    L₀ C₀ D₀ hC₀ hgrad₀ hηbound₀ hζder₀ hUopen hU hζunit₀
    c₁ r₁ R₁ hr₁ κ₁ hκ₁2 hS₁ hκ₁ A₁ B₁ hA₁ hB₁ hvκ₁ hdκ₁
    ζ₁ hζ₁2 η₁ hη₁ hζ₁ L₁ C₁ D₁ hC₁ hgrad₁ hηbound₁ hζder₁
    Vplus hVpU hζp (1+d) hp hεp hVp
  refine ⟨Rm,Rp,hRmc,hRpc,hRmae,hRpae,?_⟩
  let D : Fin 2 → Set Space := fun b => if b = 0 then closure Vminus else closure Vplus
  let amp : Fin 2 → Space → ℝ := fun b x => physicalAmplitude (if b = 0 then Rm else Rp) x
  have hclosed (b : Fin 2) : IsClosed (D b) := by
    dsimp [D]
    split_ifs <;> exact isClosed_closure
  have hcov : K ⊆ ⋃ b, D b := by
    intro x hx
    rcases hcover hx with hm | hp
    · exact mem_iUnion.mpr ⟨0, by simpa [D] using hm⟩
    · exact mem_iUnion.mpr ⟨1, by simpa [D] using hp⟩
  have hcont (b : Fin 2) : ContinuousOn (amp b) (K ∩ D b) := by
    apply Continuous.continuousOn
    by_cases hb : b = 0
    · simp only [amp, hb, if_true]
      exact physicalAmplitude_continuous Rm hRmc
    · simp only [amp, hb, if_false]
      exact physicalAmplitude_continuous Rp hRpc
  obtain ⟨b,x,hx,hmax⟩ := finite_closed_branches_attain_max K hK hne D hclosed hcov amp hcont
  exact ⟨b,x,hx,hmax⟩

end OQ14.Packet05ActualMaximum
#print axioms OQ14.Packet05ActualMaximum.actual_flat_two_sided_maximum
#print axioms OQ14.Packet05ActualMaximum.physicalAmplitude_continuous
