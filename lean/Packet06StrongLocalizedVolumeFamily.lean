import Packet06StrongPlacedWeighted
import Packet06ModalTranslatedVolumeProperties
import Packet06PlacedClusterBalls
import Packet06AllStrongWeightedVolumes
import Packet06ModalPlacementScale
import Packet06SmallClusterExcited
import Packet06RoundedHotspotFamily
import Packet05GivenAllCollars

/-! Unconditional localized modal family whose maximum branches retain actual
one-sided traces on a strictly larger ball before every selection and placement. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace OQ14.Packet06StrongLocalizedVolumeFamily
open Set Metric Filter MeasureTheory Maxwell Packet06ConcreteModalGeometry Packet06ConcreteModalRounding
  Packet06RoundedVolumeLimits Packet06PhysicalVolumeLimits Packet06PlacedRoundedVolumeLimits
  Packet06ModalPlacementScale Packet06PlacedPhaseField Packet06PlacementHomeomorph
  Packet06PhaseWeightedMaximum Packet05BinaryPhaseMaximum Packet05ActualMaximum
open scoped Topology

theorem exists_strong_localized_volume_family (N : ℕ) (K target Q ell : ℝ)
    (hK : 1 < K) (ht : 0 < target) (hQ : 0 ≤ Q) (hell : 0 < ell)
    (P : Set (EuclideanSpace ℝ (Fin 2))) (hP : IsOpen P) (hne : P.Nonempty) :
    ∃ (n η : ℝ) (hn : 1 < n) (hη : 0 ≤ η) (g : Geometry N n)
      (z₀ : ℂ) (z : ℕ → ℂ) (v : ℕ → Packet06SectorOperator.Sector)
      (r : ℝ) (u : EuclideanSpace ℝ (Fin 2))
      (d : ℕ → Fin N → MaximumData) (b : ℕ → Fin N → Bool) (x : ℕ → Fin N → Maxwell.Space) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j),
      0 < r ∧ r < g.radius ∧ 0 < η ∧ u ∈ P ∧
      (∀ᶠ j in atTop, 2*(r/s j) < ell ∧
        (∀ i, (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) 2=0 ∧
          Packet06PlanarProjection.project (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∈ P) ∧
        Function.Injective (fun i => Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∧
        (∀ i y, y ∈ closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j) → Packet06PlanarProjection.project y ∈ P) ∧
        (∀ i k, i ≠ k → Disjoint
          (closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j))
          (closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center k)) (r/s j)))) ∧
      n < K ∧ 0 < z₀.re ∧ Tendsto z atTop (𝓝 z₀) ∧
      Tendsto s atTop (𝓝 (target/z₀.re)) ∧
      (∀ᶠ j in atTop, s j = target/(z j).re) ∧
      (∃ (A : Fin N → Set Maxwell.Space) (B : ℝ), 0 ≤ B ∧
        (∀ i, IsOpen (A i) ∧ A i ⊆ ball (g.center i) g.radius ∧ sphere (g.center i) r ⊆ A i) ∧
        (∀ᶠ j in atTop, ∀ i, Packet05OneSidedCollar.OneSidedCollar (rounded n hn g η hη j)
          (z j) (v j) (body g j) (A i) B) ∧
        ∀ M : ℝ, ∀ᶠ j in atTop, ∀ i, Packet06RoundedHotspot.HotspotAbove
          (rounded n hn g η hη j) (z j) (v j) (body g j) (g.center i) r M B) ∧
      (∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im < 0 ∧ Q < (z j).re/(-2*(z j).im) ∧
        Packet06SimpleCertificate.Certified (rounded n hn g η hη j) 1 (z j) (v j) ∧
        Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη j) 1 (z j) (v j)=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode (rounded n hn g η hη j) (z j) 1 (v j) ∧
        Packet06ModePolePersistence.SimpleObservedPole (rounded n hn g η hη j) 1 (z j) (v j)) ∧
      (∀ᶠ j in atTop,
        let c := rounded n hn g η hη j
        let cp := Packet06PlacedKernel.placedCoefficient (s j) (Packet07PlanarCenters.planeEmbed u) c
        let zp := ((s j) : ℂ)*(z j)
        let up := Packet06PlacedKernel.placedUnknown (s j) (Packet07PlanarCenters.planeEmbed u) (v j)
        zp.re=target ∧ zp.im<0 ∧ Q < zp.re/(-2*zp.im) ∧
        (∀ x, 1 ≤ MaterialMaxwell.dielectric cp x ∧ MaterialMaxwell.dielectric cp x ≤ K^2) ∧
        ComplexConvolutionAnalytic.volumeBlock cp zp (1/(s j)+‖Packet07PlanarCenters.planeEmbed u‖) up=0 ∧
        Packet06PhysicalNormalization.reciprocalNorm cp (1/(s j)+‖Packet07PlanarCenters.planeEmbed u‖) zp up=1 ∧
        Packet06OutgoingMode.IsActualOutgoingMode cp zp (1/(s j)+‖Packet07PlanarCenters.planeEmbed u‖) up ∧
        Packet06PlacedPole.SimpleObservedPole c 1 (s j) (hs j) (Packet07PlanarCenters.planeEmbed u) zp (v j)) ∧
      (∀ᶠ j in atTop, ∀ i, Packet06StrongRoundedMaximum.StrongValid n hn g η hη (z j) (v j) j i r (d j i) ∧
        x j i ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) (b j i) ∧
        ∀ b' y, y ∈ closedBall (g.center i) r ∩ phaseDomain (body g j) b' →
          weighted n η (d j i) b' y ≤ weighted n η (d j i) (b j i) (x j i)) ∧
      (∀ᶠ j in atTop, ∀ i, Packet06StrongPlacedWeighted.StrongPlaced
        n hn g η hη j (z j) (v j) i r (d j i) (b j i) (x j i) (s j) (hs j) (Packet07PlanarCenters.planeEmbed u)) ∧
      (∀ i, Tendsto (fun j => amplitude (placedVector (d j i) (s j) (hs j) (Packet07PlanarCenters.planeEmbed u))) atTop atTop) ∧
      (∀ i, Tendsto (fun j => (Packet06PlacedPhaseField.scale (s j)^2 * weighted n η (d j i) (b j i) (x j i))⁻¹) atTop (𝓝 0)) ∧
      ∀ i, ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
        (∀ᶠ j in atTop, placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) (Packet07PlanarCenters.planeEmbed u) k ≠ 0) ∧
        Tendsto (fun j => (((phasePermittivity n η (d (φ j) i).side : ℝ) : ℂ)*
          (placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) (Packet07PlanarCenters.planeEmbed u) k)^2)⁻¹) atTop (𝓝 0) := by
  obtain ⟨n,ηmax,hn,hnK,hna,hηmax,hceiling⟩ := Packet06BoundedModalMaterial.choose_index K hK
  obtain ⟨u,hu⟩ := hne
  obtain ⟨rp,hrp,hpatch⟩ := Metric.isOpen_iff.mp hP u hu
  let δ : ℂ → ℝ := fun w => rp*target/(2*w.re)
  have hδ (w : ℂ) (hw : 0 < w.re) : 0 < δ w := by dsimp [δ]; positivity
  obtain ⟨zbase,a₀,g,zsharp,vsharp,η,hη,p,hp,sys,hzbase,ha₀,hdet,hbasepos,hbaseim,hbaseQ,
    hcluster,hηmax',hnear,hsharpRe,hsharpIm,hsharpQ,hcert,hN,hout,hpole,hE,hcoeff⟩ :=
    Packet06SmallClusterExcited.exists_excited_mode N n hn hna Q hQ ηmax (1/4) hηmax (by norm_num) δ hδ
  have hp' : p.cutoff=g.datum.cutoff ∧ p.exponent<1 := ⟨hp.1,hp.2.2.2⟩
  let smin : ℝ := target/(2*zbase.re)
  have hsmin : 0 < smin := div_pos ht (by positivity)
  let r : ℝ := min (g.radius/2) (ell*smin/4)
  have hr : 0 < r := lt_min (by linarith [g.radius_pos]) (by positivity)
  have hrhalf : r ≤ g.radius/2 := min_le_left _ _
  have hrell : r ≤ ell*smin/4 := min_le_right _ _
  have hrglt : r < g.radius := by linarith [g.radius_pos]
  have hrg : r ≤ g.radius := hrglt.le
  have hceil : (1+η)*n^2 ≤ K^2 := by
    have hh := mul_le_mul_of_nonneg_right hηmax'.le (sq_nonneg n)
    nlinarith
  obtain ⟨z,v,hz,hv,hresp,hgood,hpeak⟩ := Packet06ActualPeakFamily.actual_peak_family
    n hn g η hη.le zsharp vsharp hcert hN hsharpRe hsharpIm Q hsharpQ p hp' sys hE hcoeff
    r hr hrg
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
  obtain ⟨A,B,hB,hA,hcol,hhot⟩ :=
    Packet06CollaredHotspotFamily.collared_hotspots_of_uniform_collars n hn g η hη.le z v r hr hrglt
      (hz0.and hm)
      (fun i => Packet05ActualUniformCollar.actual_uniform_collar n hn g η hη.le z v zsharp vsharp
        hz hv hz0 hm i r hr hrglt) hpeak
  have honesided := Packet05GivenAllCollars.given_all_collars_eventually n hn g η hη.le z v hz0 hm A
    (fun _ => B) (fun i => (hA i).1) (fun i => (hA i).2.1)
    (fun i => hcol.mono (fun j hj => hj i))
  obtain ⟨d,b,x,hmax,hdiv,hvol,hdir⟩ := Packet06AllStrongWeightedVolumes.all_strong_weighted_volumes
    n hn g η hη.le z v hz0 hm r hr hrglt hpeak K hK hceil s hs
    (target/zsharp.re) (div_pos ht hsharpRe) hst
  have hg : ∀ᶠ j in atTop, 0 < (z j).re ∧ (z j).im<0 ∧ Q < (z j).re/(-2*(z j).im) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη.le j) 1 (z j) (v j) ∧
      Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 (z j) (v j)=1 := by
    filter_upwards [hgood] with j hj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1⟩
  have hvec (d₀ : MaximumData) (sc : ℝ) (hsc : 0 < sc) (a : Maxwell.Space) :
      placedVector d₀ sc hsc a = placedVector d₀ sc hsc 0 := by
    funext k
    simp [placedVector,transport]
  have hdiv' : ∀ i, Tendsto (fun j => amplitude (placedVector (d j i) (s j) (hs j) (Packet07PlanarCenters.planeEmbed u))) atTop atTop := by
    simpa only [hvec] using hdiv
  have hdir' : ∀ i, ∃ (k : Fin 3) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ᶠ j in atTop, placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) (Packet07PlanarCenters.planeEmbed u) k ≠ 0) ∧
      Tendsto (fun j => (((phasePermittivity n η (d (φ j) i).side : ℝ) : ℂ)*
        (placedVector (d (φ j) i) (s (φ j)) (hs (φ j)) (Packet07PlanarCenters.planeEmbed u) k)^2)⁻¹) atTop (𝓝 0) := by
    simpa only [hvec] using hdir
  have hnear' : |zsharp.re-zbase.re| < zbase.re/2 := by nlinarith
  have hnearEv : ∀ᶠ j in atTop, |(z j).re-zbase.re| < zbase.re/2 :=
    (tendsto_order.mp (((Complex.continuous_re.continuousAt.tendsto.comp hz).sub_const zbase.re).abs)).2 _ hnear'
  have hgeom : ∀ᶠ j in atTop, 2*(r/s j) < ell ∧
        (∀ i, (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) 2=0 ∧
          Packet06PlanarProjection.project (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∈ P) ∧
        Function.Injective (fun i => Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ∧
        (∀ i y, y ∈ closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j) → Packet06PlanarProjection.project y ∈ P) ∧
        (∀ i k, i ≠ k → Disjoint
          (closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j))
          (closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center k)) (r/s j))) := by
    filter_upwards [hseq,hg,hnearEv] with j hseqj hgj hnearj
    have hj := And.intro hseqj (And.intro hgj hnearj)
    have hjpos := hj.2.1.1
    have hsminle : smin ≤ s j := by
      change s j = target/(z j).re at hseqj
      rw [hseqj]
      apply (div_le_div_iff₀ (by positivity : 0 < 2*zbase.re) hjpos).mpr
      have hh := (abs_lt.mp hj.2.2).2
      nlinarith
    have hd : 2*(r/s j) < ell := by
      have hh : r/(s j) ≤ ell/4 := (div_le_iff₀ (hs j)).mpr (by
        have hm := mul_le_mul_of_nonneg_left hsminle hell.le
        nlinarith)
      linarith
    have hb := Packet06PlacedClusterBalls.placed_balls g P u rp target hrp ht hpatch
      zbase (z j) hbasepos hjpos hj.2.2 hcluster (2*r) (by positivity) (by linarith)
    rw [←hj.1] at hb
    have hsub (i : Fin N) :
        closedBall (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) (r/s j) ⊆
        ball (Packet06PhysicalPlacement.point (s j) (Packet07PlanarCenters.planeEmbed u) (g.center i)) ((2*r)/s j) :=
      closedBall_subset_ball (by exact (div_lt_div_iff_of_pos_right (hs j)).mpr (by linarith))
    exact ⟨hd,hb.1,hb.2.1,fun i y hy => hb.2.2.1 i y (hsub i hy),
      fun i k hik => (hb.2.2.2 i k hik).mono (hsub i) (hsub k)⟩
  have hplaced := Packet06ModalTranslatedVolumeProperties.eventual_placed_properties n hn g η hη.le K target Q hK hceil z v s hs (Packet07PlanarCenters.planeEmbed u) hseq hg
  have hactual : ∀ᶠ j in atTop, ∀ i, Packet06StrongPlacedWeighted.StrongPlaced
      n hn g η hη.le j (z j) (v j) i r (d j i) (b j i) (x j i) (s j) (hs j) (Packet07PlanarCenters.planeEmbed u) := by
    filter_upwards [hmax,hg,hm] with j hj hg' hk i
    exact Packet06StrongPlacedWeighted.strong_placed_certificate n hn g η hη.le j (z j) (v j) hk
      hg'.2.2.2.2 i r hrglt (d j i) (hj i).1 (b j i) (x j i)
      (hj i).2.1 (hj i).2.2 (s j) (hs j) (Packet07PlanarCenters.planeEmbed u)
  exact ⟨n,η,hn,hη.le,g,zsharp,z,v,r,u,d,b,x,s,hs,hr,hrglt,hη,hu,hgeom,hnK,hsharpRe,hz,hst,hseq,⟨A,B,hB,hA,honesided,hhot⟩,hgood,hplaced,hmax,hactual,hdiv',hvol,hdir'⟩
end OQ14.Packet06StrongLocalizedVolumeFamily
#print axioms OQ14.Packet06StrongLocalizedVolumeFamily.exists_strong_localized_volume_family
