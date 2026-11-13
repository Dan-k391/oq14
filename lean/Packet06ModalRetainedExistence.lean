import Packet06ModalHotspotExistence

/-! Preserve the actual construction data needed to rotate the full modal
device, including the same base certificate and positive host neighborhoods. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 7000000
namespace OQ14.Packet06ModalRetainedExistence
open MeasureTheory Metric Set Filter Maxwell Packet06ConcreteModalGeometry
  Packet06ConcreteModalRounding Packet06PlacedKernel Packet06PhysicalPlacement
  Packet06PlacementHomeomorph Packet06PlacedPhaseField Packet06ModalHotspotExistence
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := EuclideanSpace ℝ (Fin 2)

structure Retained {N : ℕ} (d : Device N) : Prop where
  base_radius_lt : d.baseRadius < d.geometry.radius
  collar_in_host : ∀ i, d.collar i ⊆ d.outerBody
  base_certified : Packet06SimpleCertificate.Certified d.baseMaterial 1 d.baseFrequency d.baseUnknown
  base_normalized : Packet06PhysicalNormalization.reciprocalNorm d.baseMaterial 1 d.baseFrequency d.baseUnknown=1

theorem exists_retained_modal_hotspots (N : ℕ) (K target Q ρ M : ℝ)
    (hK : 1 < K) (htarget : 0 < target) (hQ : 0 ≤ Q) (hρ : 0 < ρ)
    (P : Set Plane) (hPopen : IsOpen P) (hP : P.Nonempty) :
    ∃ d : Device N, Valid d K target Q ρ M P ∧ Retained d := by
  obtain ⟨n,ηmax,hn,hnK,hna,hηmax,hceiling⟩ := Packet06BoundedModalMaterial.choose_index K hK
  obtain ⟨uₚ,huₚ⟩ := hP
  obtain ⟨rp,hrp,hpatch⟩ := Metric.isOpen_iff.mp hPopen uₚ huₚ
  let δ : ℂ → ℝ := fun w => rp*target/(2*w.re)
  have hδ (w : ℂ) (hw : 0 < w.re) : 0 < δ w := by dsimp [δ]; positivity
  obtain ⟨zbase,a₀,g,zsharp,vsharp,η,hη,p,hp,sys,hzbase,ha₀,hdet,hbasepos,hbaseim,hbaseQ,
    hcluster,hηmax',hnear,hsharpRe,hsharpIm,hsharpQ,hcert,hN,hout,hpole,hE,hcoeff⟩ :=
    Packet06SmallClusterExcited.exists_excited_mode N n hn hna Q hQ ηmax (1/4) hηmax (by norm_num) δ hδ
  have hnear' : |zsharp.re-zbase.re| < zbase.re/2 := by nlinarith
  let smin : ℝ := target/(2*zbase.re)
  have hsmin : 0 < smin := by dsimp [smin]; positivity
  let r : ℝ := min (g.radius/2) (ρ*smin/2)
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith [g.radius_pos]) (by positivity)
  have hrg : r < g.radius := by
    dsimp [r]
    have := min_le_left (g.radius/2) (ρ*smin/2)
    linarith [g.radius_pos]
  have hrρ : r ≤ ρ*smin := by
    dsimp [r]
    have := min_le_right (g.radius/2) (ρ*smin/2)
    nlinarith
  have hp' : p.cutoff=g.datum.cutoff ∧ p.exponent<1 := ⟨hp.1,hp.2.2.2⟩
  obtain ⟨zr,vr,hzr,hvr,hresp,hgood,A,B,hB,hA,hcollar,hhot⟩ :=
    Packet06RoundedHotspotFamily.rounded_hotspot_family n hn g η hη.le zsharp vsharp
      hcert hN hsharpRe hsharpIm Q hsharpQ p hp' sys hE hcoeff r hr hrg
  have hz0 : ∀ᶠ j in atTop, zr j ≠ 0 := by
    filter_upwards [hgood] with j hj
    intro he
    have hh := hj.1
    rw [he] at hh
    simp at hh
  have hmode : ∀ᶠ j in atTop, ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) (zr j) 1 (vr j)=0 := by
    filter_upwards [hgood] with j hj
    obtain ⟨w,ψ,_,hk,_,_⟩ := hj.2.2.2.1
    exact hk
  have hgood' : ∀ᶠ j in atTop, 0 < (zr j).re ∧ (zr j).im<0 ∧ Q < (zr j).re/(-2*(zr j).im) ∧
      Packet06SimpleCertificate.Certified (rounded n hn g η hη.le j) 1 (zr j) (vr j) ∧
      Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 (zr j) (vr j)=1 := by
    filter_upwards [hgood] with j hj
    exact ⟨hj.1,hj.2.1,hj.2.2.1,hj.2.2.2.1,hj.2.2.2.2.1⟩
  let Extra : ℕ → Prop := fun j =>
    (∀ i, Packet05OneSidedCollar.OneSidedCollar (rounded n hn g η hη.le j) (zr j) (vr j) (body g j) (A i) B) ∧
    ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) (zr j) 1 (vr j)=0 ∧
    Packet06PhysicalNormalization.reciprocalNorm (rounded n hn g η hη.le j) 1 (zr j) (vr j)=1
  have hextra : ∀ᶠ j in atTop, Extra j := by
    have ht := Packet05GivenAllCollars.given_all_collars_eventually n hn g η hη.le zr vr hz0 hmode A (fun _ => B)
      (fun i => (hA i).1) (fun i => (hA i).2.1) (fun i => hcollar.mono (fun j hj => hj i))
    filter_upwards [ht,hmode,hgood'] with j hj hk hg
    exact ⟨hj,hk,hg.2.2.2.2⟩
  have hAunit (i : Fin N) : A i ⊆ ball (0 : Space) 1 :=
    (hA i).2.1.trans (ball_subset_closedBall.trans
      ((closedBall_subset_closedBall g.radius_outer).trans (g.outer_inside i)))
  have hceil : (1+η)*n^2 ≤ K^2 := by
    have hh := mul_le_mul_of_nonneg_right hηmax'.le (sq_nonneg n)
    nlinarith
  obtain ⟨j,htrace,hsc,hradpos,hrad,hfreq,him,hquality,hmat,hsupport,hcertj,hker,hNplaced,houtplaced,
    hplanar,hinj,hproject,hdisjoint,hs,hBplaced,hinner,hinnersmooth,hcollarplaced,hhotplaced⟩ :=
    Packet06CollaredHotspotSelection.select_placed_collared_hotspots n hn g η hη.le K target Q ρ M hK htarget hρ hceil
      P uₚ rp hrp hpatch zbase zsharp hbasepos hnear' hcluster zr vr hzr hgood' r B hr hrg.le hrρ hB
      Extra hextra A (fun i => ⟨(hA i).1,(hA i).2.2,hAunit i⟩) hcollar hhot
  let s := target/(zr j).re
  let a := Packet07PlanarCenters.planeEmbed uₚ
  let d : Device N := ⟨n,η,hn,hη,g,j,zr j,vr j,s,hs,r,a,scale s*B,fun i => placement s hs a '' A i⟩
  have hvalid : Valid d K target Q ρ M P := by
    refine {
      index_bound := hnK
      radius_pos := hradpos
      radius_bound := hrad
      frequency_real := hfreq
      frequency_imag := him
      quality := hquality
      material_bounds := hmat
      material_values := fun x => Packet06PlacedMaterialGeometry.placed_material_values n hn g η hη.le j s hs a x
      material_support := hsupport
      kernel := hker
      normalization := hNplaced
      outgoing := houtplaced
      observed_pole := Packet06RoundedPlacedPole.rounded_placed_observed_pole n hn g η hη.le j (zr j) (vr j) hcertj s hs a
      inner_open := hinner
      outer_open := (placement s hs a).isOpenMap _ isOpen_ball
      inner_subset := Set.image_subset _ (body_inside g j)
      inner_smooth := hinnersmooth
      outer_smooth := Packet06PlacedMaterialGeometry.placed_outer_smooth s hs a
      centers_planar := hplanar
      centers_injective := hinj
      projected_balls := hproject
      disjoint_balls := hdisjoint
      bound_nonneg := hBplaced
      collar_open := fun i => (placement s hs a).isOpenMap _ (hA i).1
      collar_contains_sphere := ?_
      collar_traces := ?_
      hotspots := hhotplaced }
    · intro i
      intro y hy
      let h := placement s hs a
      have hd := Packet06PlanarProjection.point_distance_pair s hs a (h.symm y) (g.center i)
      change dist (h (h.symm y)) (h (g.center i))=_ at hd
      rw [h.apply_symm_apply, show dist y (h (g.center i))=r/s from hy,
        div_eq_mul_inv,mul_comm r s⁻¹] at hd
      have hsource : h.symm y ∈ sphere (g.center i) r := (mul_left_cancel₀ (inv_ne_zero hs.ne') hd).symm
      exact ⟨h.symm y,(hA i).2.2 hsource,h.apply_symm_apply y⟩
    · intro i
      exact Packet06PlacedOneSidedCollar.placed_one_sided_collar (rounded n hn g η hη.le j)
        (Packet05RoundedModeSupport.rounded_support n hn g η hη.le j)
        (fun x hx => (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη.le j x hx).ne')
        (zr j) (vr j) htrace.2.1 htrace.2.2 (body g j) (A i)
        (CommonBinaryInterface.body_open (fun _ => g.datum) (fun _ => g.radius) g.center j)
        (hA i).1 (hAunit i) B (htrace.1 i) s hs a
  refine ⟨d,hvalid,?_⟩
  exact ⟨hrg,fun i => Set.image_subset _ (hAunit i),hcertj,htrace.2.2⟩

end OQ14.Packet06ModalRetainedExistence
#print axioms OQ14.Packet06ModalRetainedExistence.exists_retained_modal_hotspots
