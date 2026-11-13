import Packet06ModalVolumePlacedProperties
import Packet06AllPhaseWeightedVolumes
import Packet06ModalPlacementScale
import Packet06SmallClusterExcited

/-! Unconditional normalized outgoing modal family with diverging attained
maxima and vanishing physical volumes at exact target-frequency placements. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace OQ14.Packet06FinalAllModalVolumes
open Set Metric Filter Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06RoundedVolumeLimits Packet06PhysicalVolumeLimits Packet06PlacedRoundedVolumeLimits
  Packet06ModalPlacementScale Packet06PlacedPhaseField Packet06PlacementHomeomorph
  Packet06PhaseWeightedMaximum Packet05BinaryPhaseMaximum Packet05ActualMaximum
open scoped Topology

theorem exists_all_modal_volume_families (N : ℕ) (K target Q : ℝ) (hK : 1 < K) (ht : 0 < target) (hQ : 0 ≤ Q) :
    ∃ (n η : ℝ) (hn : 1 < n) (hη : 0 ≤ η) (g : Geometry N n)
      (z₀ : ℂ) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
      (d : ℕ → Fin N → MaximumData) (b : ℕ → Fin N → Bool) (x : ℕ → Fin N → Maxwell.Space) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j),
      n < K ∧ 0 < z₀.re ∧ Tendsto z atTop (𝓝 z₀) ∧
      Tendsto s atTop (𝓝 (target/z₀.re)) ∧
      (∀ᶠ j in atTop, s j = target/(z j).re) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) ∧
      (∀ᶠ j in atTop,
        let c := rounded n hn g η hη j
        let cp := Packet06PlacedKernel.placedCoefficient (s j) 0 c
        let zp := ((s j) : ℂ)*(z j)
        let up := Packet06PlacedKernel.placedUnknown (s j) 0 (v j)
        zp.re=target ∧ zp.im<0 ∧ Q < zp.re/(-2*zp.im) ∧
        (∀ x, 1 ≤ MaterialMaxwell.dielectric cp x ∧ MaterialMaxwell.dielectric cp x ≤ K^2) ∧
        ComplexConvolutionAnalytic.volumeBlock cp zp (1/(s j)) up=0 ∧
        Packet06PhysicalNormalization.reciprocalNorm cp (1/(s j)) zp up=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode cp zp (1/(s j)) up ∧
        Packet06PlacedPole.SimpleObservedPole c 1 (s j) (hs j) 0 zp (v j)) ∧
      (∀ᶠ j in atTop, ∀ i, Valid n hn g η hη (z j) (v j) j i (g.radius/2) (d j i) ∧
        x j i ∈ closedBall (g.center i) (g.radius/2) ∩ phaseDomain (body g j) (b j i) ∧
        ∀ b' y, y ∈ closedBall (g.center i) (g.radius/2) ∩ phaseDomain (body g j) b' →
          weighted n η (d j i) b' y ≤ weighted n η (d j i) (b j i) (x j i)) ∧
      (∀ i, Tendsto (fun j => amplitude (placedVector (d j i) (s j) (hs j) 0)) atTop atTop) ∧
      (∀ i, Tendsto (fun j => (Packet06PlacedPhaseField.scale (s j)^2 * weighted n η (d j i) (b j i) (x j i))⁻¹) atTop (𝓝 0)) ∧
      ∀ i, ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) 0 k ≠ 0) ∧
        Tendsto (fun j => (((phasePermittivity n η (d (φ j) i).side : ℝ) : ℂ)*
          (placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) 0 k)^2)⁻¹) atTop (𝓝 0) := by
  obtain ⟨n,ηmax,hn,hnK,hna,hηmax,hceiling⟩ := Packet06BoundedModalMaterial.choose_index K hK
  let δ : ℂ → ℝ := fun _ => 1
  have hδ (w : ℂ) (_ : 0 < w.re) : 0 < δ w := by norm_num [δ]
  obtain ⟨zbase,a₀,g,zsharp,vsharp,η,hη,p,hp,sys,hzbase,ha₀,hdet,hbasepos,hbaseim,hbaseQ,
    hcluster,hηmax',hnear,hsharpRe,hsharpIm,hsharpQ,hcert,hN,hout,hpole,hE,hcoeff⟩ :=
    Packet06SmallClusterExcited.exists_excited_mode N n hn hna Q hQ ηmax (1/4) hηmax (by norm_num) δ hδ
  have hp' : p.cutoff=g.datum.cutoff ∧ p.exponent<1 := ⟨hp.1,hp.2.2.2⟩
  have hr : 0 < g.radius/2 := by linarith [g.radius_pos]
  have hrg : g.radius/2 ≤ g.radius := by linarith [g.radius_pos]
  have hceil : (1+η)*n^2 ≤ K^2 := by
    have hh := mul_le_mul_of_nonneg_right hηmax'.le (sq_nonneg n)
    nlinarith
  obtain ⟨z,v,hz,hv,hresp,hgood,hpeak⟩ := Packet06ActualPeakFamily.actual_peak_family
    n hn g η hη.le zsharp vsharp hcert hN hsharpRe hsharpIm Q hsharpQ p hp' sys hE hcoeff
    (g.radius/2) hr hrg
  let s := Packet06ModalPlacementScale.scale target zsharp z
  obtain ⟨hs,hst,hseq⟩ := target_scale target ht zsharp hsharpRe z hz
  have hz0 : ∀ᶠ j in atTop, z j ≠ 0 := by
    filter_upwards [hgood] with j hj
    intro he
    have hh := hj.1
    rw [he] at hh
    simp at hh
  have hm : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) (z j) 1 (v j)=0 := by
    filter_upwards [hgood] with j hj
    obtain ⟨w,ψ,_,hk,_,_⟩ := hj.2.2.2.1
    exact hk
  obtain ⟨d,b,x,hmax,hdiv,hvol,hdir⟩ := Packet06AllPhaseWeightedVolumes.all_weighted_volumes
    n hn g η hη.le z v hz0 hm (g.radius/2) hr hrg hpeak K hK hceil s hs
    (target/zsharp.re) (div_pos ht hsharpRe) hst
  have hg : ∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im<0 ∧ Q < (z j).re/(-2*(z j).im) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη.le j) 1 (z j) (v j) ∧
      Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 (z j) (v j)=1 := by
    filter_upwards [hgood] with j hj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1⟩
  have hplaced := Packet06ModalVolumePlacedProperties.eventual_placed_properties n hn g η hη.le K target Q hK hceil z v s hs hseq hg
  exact ⟨n,η,hn,hη.le,g,zsharp,z,v,d,b,x,s,hs,hnK,hsharpRe,hz,hst,hseq,hgood,hplaced,hmax,hdiv,hvol,hdir⟩
end OQ14.Packet06FinalAllModalVolumes
#print axioms OQ14.Packet06FinalAllModalVolumes.exists_all_modal_volume_families
