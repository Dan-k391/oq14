import Packet06ModalVolumeExistence
import Packet06RoundedPlacedPole

/-! The same target-placed modal volume family retains exact normalization,
outgoing Maxwell character, quality factor, and its observed simple pole. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06ModalVolumePlacedProperties
open Filter Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06PlacedKernel Packet06PhysicalPlacement
open scoped Topology

theorem eventual_placed_properties {N : ℕ} (n : ℝ) (hn : 1 < n) (g : Geometry N n)
    (η : ℝ) (hη : 0 ≤ η) (K target Q : ℝ) (hK : 1 < K) (hceil : (1+η)*n^2 ≤ K^2)
    (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hseq : ∀ᶠ j in atTop, s j = target/(z j).re)
    (hg : ∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im<0 ∧ Q < (z j).re/(-2*(z j).im) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
      Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1) :
    ∀ᶠ j in atTop,
      let c := rounded n hn g η hη j
      let cp := placedCoefficient (s j) 0 c
      let zp := ((s j) : ℂ)*(z j)
      let up := placedUnknown (s j) 0 (v j)
      zp.re=target ∧ zp.im<0 ∧ Q < zp.re/(-2*zp.im) ∧
      (∀ x, 1 ≤ MaterialMaxwell.dielectric cp x ∧ MaterialMaxwell.dielectric cp x ≤ K^2) ∧
      ComplexConvolutionAnalytic.volumeBlock cp zp (1/(s j)) up=0 ∧
      Packet06PhysicalNormalization.reciprocalNorm cp (1/(s j)) zp up=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode cp zp (1/(s j)) up ∧
      Packet06PlacedPole.SimpleObservedPole c 1 (s j) (hs j) 0 zp (v j) := by
  filter_upwards [hseq,hg] with j hj h
  obtain ⟨w,ψ,_,hk,_,_⟩ := h.2.2.2.1
  have hsup := Packet05RoundedModeSupport.rounded_support n hn g η hη j
  obtain ⟨hpc,hpk,hNp,hne⟩ := placed_normalized_kernel (rounded n hn g η hη j) 1 (by norm_num)
    hsup (z j) (v j) hk h.2.2.2.2 (s j) (hs j) 0
  have hre : (((s j : ℝ) : ℂ)*z j).re=target := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [hj]
    field_simp [ne_of_gt h.1]
  have him : (((s j : ℝ) : ℂ)*z j).im<0 := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_neg_of_pos_of_neg (hs j) h.2.1
  have hratio : (((s j : ℝ) : ℂ)*z j).re/(-2*(((s j : ℝ) : ℂ)*z j).im)=(z j).re/(-2*(z j).im) := by
    simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero]
    field_simp [(hs j).ne',ne_of_lt h.2.1]
    ring
  have hout := Packet06OutgoingMode.actual_outgoing_mode _ _ _
    (add_nonneg (div_nonneg (by norm_num) (hs j).le) (norm_nonneg (0 : Maxwell.Space))) _ hpc hpk hne
  refine ⟨hre,him,by rw [hratio]; exact h.2.2.1,?_,?_,?_,?_,?_⟩
  · intro x
    exact Packet06BoundedModalMaterial.placed_bounds _ K
      (fun y => Packet06BoundedModalMaterial.rounded_bounds n hn g η hη K hK hceil j y) (s j) 0 x
  · simpa using hpk
  · simpa using hNp
  · simpa using hout
  · exact Packet06RoundedPlacedPole.rounded_placed_observed_pole n hn g η hη j (z j) (v j) h.2.2.2.1 (s j) (hs j) 0
end OQ14.Packet06ModalVolumePlacedProperties
#print axioms OQ14.Packet06ModalVolumePlacedProperties.eventual_placed_properties
