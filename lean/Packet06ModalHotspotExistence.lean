import Packet06SmallClusterExcited
import Packet06RoundedHotspotFamily
import Packet06CollaredHotspotSelection
import Packet05GivenAllCollars
import Packet06PlacedOneSidedCollar
import Packet06RoundedPlacedPole
import Packet06PlacedMaterialGeometry
import Packet06GlobalElectricIdentification

/-! Unconditional modal existence in the coordinate plane: bounded smooth
material, exact real frequency, reciprocal normalization, genuine outgoing
Maxwell mode, selected-sector pole, and simultaneous attained isolated
Euclidean-amplitude hotspots with actual open one-sided low collars. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
namespace OQ14.Packet06ModalHotspotExistence
open MeasureTheory Metric Set Filter Maxwell Packet06ConcreteModalGeometry
  Packet06ConcreteModalRounding Packet06PlacedKernel Packet06PhysicalPlacement
  Packet06PlacementHomeomorph Packet06PlacedPhaseField
open scoped Topology
abbrev Space := Maxwell.Space
abbrev Plane := EuclideanSpace ℝ (Fin 2)

structure Device (N : ℕ) where
  n : ℝ
  η : ℝ
  hn : 1 < n
  hη : 0 < η
  geometry : Geometry N n
  index : ℕ
  baseFrequency : ℂ
  baseUnknown : Packet06SectorOperator.Sector
  dilation : ℝ
  dilation_pos : 0 < dilation
  baseRadius : ℝ
  translation : Space
  collarBound : ℝ
  collar : Fin N → Set Space

namespace Device
def baseMaterial {N : ℕ} (d : Device N) := rounded d.n d.hn d.geometry d.η d.hη.le d.index
def material {N : ℕ} (d : Device N) := placedCoefficient d.dilation d.translation d.baseMaterial
def frequency {N : ℕ} (d : Device N) := (d.dilation : ℂ)*d.baseFrequency
def unknown {N : ℕ} (d : Device N) := placedUnknown d.dilation d.translation d.baseUnknown
def radius {N : ℕ} (d : Device N) := d.baseRadius/d.dilation
def supportRadius {N : ℕ} (d : Device N) := 1/d.dilation+‖d.translation‖
def map {N : ℕ} (d : Device N) := placement d.dilation d.dilation_pos d.translation
def innerBody {N : ℕ} (d : Device N) := d.map '' body d.geometry d.index
def outerBody {N : ℕ} (d : Device N) := d.map '' ball (0 : Space) 1
def center {N : ℕ} (d : Device N) (i : Fin N) := point d.dilation d.translation (d.geometry.center i)
end Device

def SmoothBoundary (U : Set Space) : Prop :=
  ∀ x ∈ frontier U, ∃ F : Space → ℝ,
    ContDiffAt ℝ (⊤ : ℕ∞) F x ∧ F x=0 ∧ fderiv ℝ F x ≠ 0 ∧
    ∃ V : Set Space, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, (y ∈ U ↔ 0 < F y)

structure Valid {N : ℕ} (d : Device N) (K target Q ρ M : ℝ) (P : Set Plane) : Prop where
  index_bound : d.n < K
  radius_pos : 0 < d.radius
  radius_bound : d.radius ≤ ρ
  frequency_real : d.frequency.re=target
  frequency_imag : d.frequency.im<0
  quality : Q < d.frequency.re/(-2*d.frequency.im)
  material_bounds : ∀ x, 1 ≤ MaterialMaxwell.dielectric d.material x ∧ MaterialMaxwell.dielectric d.material x ≤ K^2
  material_values : ∀ x, MaterialMaxwell.dielectric d.material x =
    (by classical exact if x ∈ d.innerBody then (1+d.η)*d.n^2 else if x ∈ d.outerBody then d.n^2 else 1)
  material_support : ∀ x : Space, x ∉ closedBall 0 d.supportRadius → d.material.value (VectorFourier.coordinateMap x)=0
  kernel : ComplexConvolutionAnalytic.volumeBlock d.material d.frequency d.supportRadius d.unknown=0
  normalization : Packet06PhysicalNormalization.reciprocalNorm d.material d.supportRadius d.frequency d.unknown=1
  outgoing : Packet06OutgoingMode.IsActualOutgoingMode d.material d.frequency d.supportRadius d.unknown
  observed_pole : Packet06PlacedPole.SimpleObservedPole d.baseMaterial 1 d.dilation d.dilation_pos d.translation d.frequency d.baseUnknown
  inner_open : IsOpen d.innerBody
  outer_open : IsOpen d.outerBody
  inner_subset : d.innerBody ⊆ d.outerBody
  inner_smooth : SmoothBoundary d.innerBody
  outer_smooth : SmoothBoundary d.outerBody
  centers_planar : ∀ i, (d.center i) 2=0 ∧ Packet06PlanarProjection.project (d.center i) ∈ P
  centers_injective : Function.Injective d.center
  projected_balls : ∀ i y, y ∈ ball (d.center i) d.radius → Packet06PlanarProjection.project y ∈ P
  disjoint_balls : ∀ i k, i ≠ k → Disjoint (ball (d.center i) d.radius) (ball (d.center k) d.radius)
  bound_nonneg : 0 ≤ d.collarBound
  collar_open : ∀ i, IsOpen (d.collar i)
  collar_contains_sphere : ∀ i, sphere (d.center i) d.radius ⊆ d.collar i
  collar_traces : ∀ i, Packet05OneSidedCollar.OneSidedCollar d.material d.frequency d.unknown d.innerBody (d.collar i) d.collarBound
  hotspots : ∀ i, Packet06PlacedHotspot.PhysicalHotspot d.material d.frequency d.unknown d.innerBody (d.center i) d.radius M d.collarBound

theorem exists_modal_hotspots (N : ℕ) (K target Q ρ M : ℝ)
    (hK : 1 < K) (htarget : 0 < target) (hQ : 0 ≤ Q) (hρ : 0 < ρ)
    (P : Set Plane) (hPopen : IsOpen P) (hP : P.Nonempty) :
    ∃ d : Device N, Valid d K target Q ρ M P := by
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
  refine ⟨d,{
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
    hotspots := hhotplaced }⟩
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

end OQ14.Packet06ModalHotspotExistence
#print axioms OQ14.Packet06ModalHotspotExistence.exists_modal_hotspots
