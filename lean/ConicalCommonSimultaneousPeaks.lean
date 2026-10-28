import ConicalCommonRoundedPeaks

/-! Simultaneous positive-volume superlevels for one fixed input and common material sequence. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ConicalCommonSimultaneousPeaks
open MeasureTheory Set Metric Filter
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Data := ConicalStaticVolume.Data
abbrev Input := ComplexTransverseExpansion.ModeIndex →₀ ℂ
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable (p : ι → Data) (a : ι → ℝ) (center : ι → Space)
  (B : ℝ) (hB : 0 ≤ B) (hcontrast : ∀ i, (p i).contrast ≤ B)
  (ha : ∀ i, a i ≤ (p i).cutoff.rOut)
  (hsep : ∀ i j, i ≠ j → Disjoint (ConicalCommonMaterial.outer p center i)
    (ConicalCommonMaterial.outer p center j))

theorem one_input_simultaneous (R T : ℝ) (b : ι → ℝ)
    (hR0 : 0 ≤ R) (hRT : R ≤ T) (hb0 : ∀ i, 0 < b i) (hb : ∀ i, b i < a i)
    (hν : ∀ i, (p i).exponent < 1) (hra : ∀ i, 0 ≤ a i)
    (hgeom : ∀ i j, i ≠ j → a i+a j < dist (center i) (center j))
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hai : ∀ i, a i < (p i).cutoff.rIn) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, ∀ (hk : 0 < k), k < δ →
      ∃ (hfreq : |k| ≤ DynamicStaticLimit.frequencyRadius (ConicalCommonRoundedPeaks.coefficient p a center B hB hcontrast ha hsep) R)
        (d : Input), d ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k d) atTop (𝓝 1) ∧
        (∀ i, ConicalCommonAngular.coefficient p a center B hB hcontrast ha hsep i R k (b i) hR0 hk.ne'
          (hb i).le (hai i) hfreq hR (hb0 i) (hν i) d ≠ 0) ∧
        (∀ n : ℕ, MaterialMaxwell.TestMaxwell k (MaterialMaxwell.dielectric (ConicalCommonRoundedPeaks.rounded p a center B hB hcontrast ha hsep n))
          (ConicalCommonRoundedPeaks.electric p a center B hB hcontrast ha hsep R k n (FiniteAngularHerglotz.incident k d))
          (ConicalCommonRoundedPeaks.magnetic p a center B hB hcontrast ha hsep R k n (FiniteAngularHerglotz.incident k d))) ∧
        ∀ radii : ι → ℝ, (∀ i, 0 < radii i) → (∀ i, radii i ≤ b i) →
          ∃ components : ι → Fin 3, ∀ thresholds : ι → ℝ, ∀ᶠ n : ℕ in atTop, ∀ i : ι,
            0 < (volume.restrict (ball (center i) (radii i)))
              {x | thresholds i < ‖ConicalCommonRoundedPeaks.electric p a center B hB hcontrast ha hsep R k n
                (FiniteAngularHerglotz.incident k d) x (components i)‖} := by
  obtain ⟨δ,hδ,hinput⟩ := ConicalCommonRoundedPeaks.one_input_rounded_superlevels p a center B hB hcontrast ha hsep
    R T b hR0 hRT hb0 hb hν hra hgeom hKR hR hai
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  obtain ⟨hfreq,d,hd,hpower,hq,hm,hpeak⟩ := hinput k hk hkd
  refine ⟨hfreq,d,hd,hpower,hq,hm,?_⟩
  intro radii hr0 hrb
  choose components hcomponents using (fun i => hpeak i (radii i) (hr0 i) (hrb i))
  refine ⟨components,?_⟩
  intro thresholds
  exact Filter.eventually_all.mpr (fun i => hcomponents i (thresholds i))

end OQ14.ConicalCommonSimultaneousPeaks
#print axioms OQ14.ConicalCommonSimultaneousPeaks.one_input_simultaneous
