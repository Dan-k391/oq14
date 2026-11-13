import Packet06ModalVolumePlacedProperties
import Packet06ModalPlacementScale
import Packet06SmallClusterExcited

/-! Unconditional normalized outgoing modal family with diverging attained
maxima and vanishing physical volumes at exact target-frequency placements. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace OQ14.Packet06FinalModalVolume
open Filter Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06RoundedVolumeLimits Packet06PhysicalVolumeLimits Packet06PlacedRoundedVolumeLimits
  Packet06ModalPlacementScale Packet06PlacedPhaseField Packet06PlacementHomeomorph
open scoped Topology

theorem exists_final_modal_volume_family (K target Q : ℝ) (hK : 1 < K) (ht : 0 < target) (hQ : 0 ≤ Q) :
    ∃ (n η : ℝ) (hn : 1 < n) (hη : 0 ≤ η) (g : Geometry 1 n)
      (z₀ : ℂ) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
      (d : ℕ → MaximumData) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j),
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
      (∀ᶠ j in atTop, Valid n hn g η hη (z j) (v j) j 0 (g.radius/2) (d j)) ∧
      Tendsto (fun j => amplitude (placedVector (d j) (s j) (hs j) 0)) atTop atTop ∧
      Tendsto (fun j => 1/(MaterialMaxwell.dielectric
        (Packet06PlacedKernel.placedCoefficient (s j) 0 (rounded n hn g η hη j))
        ((placement (s j) (hs j) 0) (d j).point) *
        (amplitude (placedVector (d j) (s j) (hs j) 0))^2)) atTop (𝓝 0) ∧
      ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, placedVector (d (φ j)) (s (φ j)) (hs (φ j)) 0 k ≠ 0) ∧
        Tendsto (fun j => (((MaterialMaxwell.dielectric
          (Packet06PlacedKernel.placedCoefficient (s (φ j)) 0 (rounded n hn g η hη (φ j)))
          ((placement (s (φ j)) (hs (φ j)) 0) (d (φ j)).point) : ℝ) : ℂ)*
          (placedVector (d (φ j)) (s (φ j)) (hs (φ j)) 0 k)^2)⁻¹) atTop (𝓝 0) := by
  obtain ⟨n,ηmax,hn,hnK,hna,hηmax,hceiling⟩ := Packet06BoundedModalMaterial.choose_index K hK
  let δ : ℂ → ℝ := fun _ => 1
  have hδ (w : ℂ) (_ : 0 < w.re) : 0 < δ w := by norm_num [δ]
  obtain ⟨zbase,a₀,g,zsharp,vsharp,η,hη,p,hp,sys,hzbase,ha₀,hdet,hbasepos,hbaseim,hbaseQ,
    hcluster,hηmax',hnear,hsharpRe,hsharpIm,hsharpQ,hcert,hN,hout,hpole,hE,hcoeff⟩ :=
    Packet06SmallClusterExcited.exists_excited_mode 1 n hn hna Q hQ ηmax (1/4) hηmax (by norm_num) δ hδ
  have hp' : p.cutoff=g.datum.cutoff ∧ p.exponent<1 := ⟨hp.1,hp.2.2.2⟩
  have hr : 0 < g.radius/2 := by linarith [g.radius_pos]
  have hrg : g.radius/2 ≤ g.radius := by linarith [g.radius_pos]
  have hceil : (1+η)*n^2 ≤ K^2 := by
    have hh := mul_le_mul_of_nonneg_right hηmax'.le (sq_nonneg n)
    nlinarith
  obtain ⟨z,v,d,hz,hv,hgood,hd,hdiv,hvol,hdir⟩ := Packet06ActualFamilyVolume.actual_family_volume
    n hn g η hη.le zsharp vsharp hcert hN hsharpRe hsharpIm Q hsharpQ p hp' sys hE hcoeff 0
    (g.radius/2) hr hrg K hK hceil
  let s := Packet06ModalPlacementScale.scale target zsharp z
  obtain ⟨hs,hst,hseq⟩ := target_scale target ht zsharp hsharpRe z hz
  have hε (j : ℕ) (x : Maxwell.Space) : 1 ≤ MaterialMaxwell.dielectric (rounded n hn g η hη.le j) x :=
    (Packet06BoundedModalMaterial.rounded_bounds n hn g η hη.le K hK hceil j x).1
  have hv := variable_placement_volume d s hs (target/zsharp.re) (div_pos ht hsharpRe) hst 0
    (fun j => rounded n hn g η hη.le j) hε hdiv
  have hg : ∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im<0 ∧ Q < (z j).re/(-2*(z j).im) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη.le j) 1 (z j) (v j) ∧
      Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 (z j) (v j)=1 := by
    filter_upwards [hgood] with j hj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1⟩
  have hplaced := Packet06ModalVolumePlacedProperties.eventual_placed_properties n hn g η hη.le K target Q hK hceil z v s hs hseq hg
  exact ⟨n,η,hn,hη.le,g,zsharp,z,v,d,s,hs,hnK,hsharpRe,hz,hst,hseq,hgood,hplaced,hd,hv.1,hv.2.1,hv.2.2⟩
end OQ14.Packet06FinalModalVolume
#print axioms OQ14.Packet06FinalModalVolume.exists_final_modal_volume_family
