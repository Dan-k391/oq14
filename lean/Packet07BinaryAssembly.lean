import ConicalCommonBinaryPeaks
import CommonBinaryInterface
import CommonBinaryValues

/-! Simultaneous actual Maxwell peaks and one smooth binary material at a common rounding index. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.Packet07BinaryAssembly
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
    (ConicalCommonMaterial.outer p center j)) (ha0 : ∀ i, 0 < a i)

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
include ha hsep ha0 in
theorem component_pairwise_disjoint (n : ℕ) :
    ∀ i j, i ≠ j → Disjoint (CommonBinaryInterface.component p a center n i)
      (CommonBinaryInterface.component p a center n j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hci := CommonBinaryInterface.closure_component_subset p a center ha0 ha n i (subset_closure hi)
  have hcj := CommonBinaryInterface.closure_component_subset p a center ha0 ha n j (subset_closure hj)
  exact (Set.disjoint_left.mp (hsep i j hij)) hci hcj

/-- One finite common binary device realizes every prescribed finite list of
    positive-volume peak thresholds, while retaining smooth boundary certificates,
    finite support, exact binary values, actual Maxwell fields and one unit-power input.
    The high-field assertions are measure superlevels, not attained maxima. -/
theorem one_smooth_binary_device (R T : ℝ) (b : ι → ℝ) (contrast : ℝ)
    (hcommon : ∀ i, (p i).contrast = contrast)
    (hR0 : 0 ≤ R) (hRT : R ≤ T) (hb0 : ∀ i, 0 < b i) (hb : ∀ i, b i < a i)
    (hν : ∀ i, (p i).exponent < 1) (hra : ∀ i, 0 ≤ a i)
    (hgeom : ∀ i j, i ≠ j → a i + a j < dist (center i) (center j))
    (hKR : UnionFreeRunge.balls center a ⊆ closedBall (0 : Space) R)
    (hR : ∀ i, ConicalCommonMaterial.outer p center i ⊆ closedBall (0 : Space) R)
    (hai : ∀ i, a i < (p i).cutoff.rIn) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℝ, 0 < k → k < δ →
      ∃ d : Input, d ≠ 0 ∧ Tendsto (FiniteMixedScaledFlux.inwardPowerK k d) atTop (𝓝 1) ∧
        ∀ radii : ι → ℝ, (∀ i, 0 < radii i) → (∀ i, radii i ≤ b i) →
        ∀ thresholds : ι → ℝ, ∃ (n : ℕ) (components : ι → Fin 3),
          MaterialMaxwell.TestMaxwell k
            (MaterialMaxwell.dielectric (ConicalCommonBinaryPeaks.rounded p a center B hB hcontrast ha hsep ha0 n))
            (ConicalCommonBinaryPeaks.electric p a center B hB hcontrast ha hsep ha0 R k n (FiniteAngularHerglotz.incident k d))
            (ConicalCommonBinaryPeaks.magnetic p a center B hB hcontrast ha hsep ha0 R k n (FiniteAngularHerglotz.incident k d)) ∧
          (∀ i : ι, 0 < (volume.restrict (ball (center i) (radii i)))
            {x | thresholds i < ‖ConicalCommonBinaryPeaks.electric p a center B hB hcontrast ha hsep ha0 R k n
              (FiniteAngularHerglotz.incident k d) x (components i)‖}) ∧
          IsOpen (CommonBinaryInterface.body p a center n) ∧
          CommonBinaryInterface.body p a center n ⊆ closedBall (0 : Space) R ∧
          (∀ i j, i ≠ j → Disjoint (CommonBinaryInterface.component p a center n i)
            (CommonBinaryInterface.component p a center n j)) ∧
          (∀ x ∈ frontier (CommonBinaryInterface.body p a center n),
            ∃ F : Space → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
              ∃ U : Set Space, IsOpen U ∧ x ∈ U ∧ ∀ y ∈ U, (y ∈ CommonBinaryInterface.body p a center n ↔ 0 < F y)) ∧
          (∀ x : Space, (ConicalCommonBinaryPeaks.rounded p a center B hB hcontrast ha hsep ha0 n).value
            (VectorFourier.coordinateMap x) = (by classical exact if x ∈ CommonBinaryInterface.body p a center n then contrast else 0)) := by
  obtain ⟨δ,hδ,hinput⟩ := ConicalCommonBinaryPeaks.one_input_simultaneous p a center B hB hcontrast ha hsep ha0
    R T b hR0 hRT hb0 hb hν hra hgeom hKR hR hai
  refine ⟨δ,hδ,?_⟩
  intro k hk hkd
  obtain ⟨hfreq,d,hd,hpower,hq,hm,hpeak⟩ := hinput k hk hkd
  refine ⟨d,hd,hpower,?_⟩
  intro radii hr0 hrb thresholds
  obtain ⟨components,hp⟩ := hpeak radii hr0 hrb
  have hs := CommonBinaryInterface.eventually_body_smooth p a center ha0 ha hsep
  obtain ⟨n, hn⟩ := ((hp thresholds).and hs).exists
  refine ⟨n, components, hm n, hn.1, CommonBinaryInterface.body_open p a center n,
    CommonBinaryInterface.body_support p a center ha0 ha R hR n,
    component_pairwise_disjoint p a center ha hsep ha0 n, hn.2, ?_⟩
  intro x
  exact CommonBinaryInterface.coefficient_body p a center B hB hcontrast ha0 ha hsep contrast hcommon n x

end OQ14.Packet07BinaryAssembly
#print axioms OQ14.Packet07BinaryAssembly.component_pairwise_disjoint
#print axioms OQ14.Packet07BinaryAssembly.one_smooth_binary_device
