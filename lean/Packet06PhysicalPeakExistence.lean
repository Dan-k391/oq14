import Packet06SmallClusterExcited
import Packet06RoundedIntrinsicPeaks
import Packet06PlacedModePeaks
import Packet06PlacedClusterBalls
import Packet06BoundedModalMaterial
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
namespace OQ14.Packet06PhysicalPeakExistence
open MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.Packet06ConcreteModalGeometry
  OQ14.Packet06ConcreteModalRounding OQ14.Packet06PhysicalPlacement OQ14.Packet06PlacedKernel
open scoped Topology
abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev V := VectorFourier.VectorL2

theorem exists_placed_rounded_peaks (N : ℕ) (K target Q ρ M : ℝ)
    (hK : 1 < K) (htarget : 0 < target) (hQ : 0 ≤ Q) (hρ : 0 < ρ)
    (P : Set Plane) (hPopen : IsOpen P) (hP : P.Nonempty) :
    ∃ (n η : ℝ) (hn : 1 < n) (hη : 0 < η) (zbase : ℂ) (g : Geometry N n)
      (z : ℂ) (v : Packet06SectorOperator.Sector) (j : ℕ) (s r : ℝ) (a : Maxwell.Space),
      let c := rounded n hn g η hη.le j
      let cp := placedCoefficient s a c
      let zp := (s : ℂ)*z
      let up := placedUnknown s a v
      let centers := fun i => point s a (g.center i)
      let rad := r/s
      n < K ∧ 0 < zbase.re ∧ 0 < s ∧ 0 < rad ∧ rad ≤ ρ ∧
      zp.re=target ∧ zp.im<0 ∧ Q < zp.re/(-2*zp.im) ∧
      (∀ x : Maxwell.Space, 1 ≤ MaterialMaxwell.dielectric cp x ∧ MaterialMaxwell.dielectric cp x ≤ K^2) ∧
      Packet06SimpleCertificate.Certified c 1 z v ∧
      Packet06PhysicalNormalization.reciprocalNorm c 1 z v=1 ∧
      ComplexConvolutionAnalytic.volumeBlock cp zp (1/s+‖a‖) up=0 ∧
      Packet06PhysicalNormalization.reciprocalNorm cp (1/s+‖a‖) zp up=1 ∧
      Packet06OutgoingMode.IsActualOutgoingMode cp zp (1/s+‖a‖) up ∧
      (∀ i, (centers i) 2=0 ∧ Packet06PlanarProjection.project (centers i) ∈ P) ∧
      Function.Injective centers ∧
      (∀ i y, y ∈ ball (centers i) rad → Packet06PlanarProjection.project y ∈ P) ∧
      (∀ i k, i ≠ k → Disjoint (ball (centers i) rad) (ball (centers k) rad)) ∧
      ∀ i, 0 < (volume.restrict (ball (centers i) rad)) {x | M <
        ‖Packet06LocalPencil.response cp zp (1/s+‖a‖) (1/s+‖a‖) up (VectorFourier.coordinateMap x)‖} := by
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
  have hrg : r ≤ g.radius := by dsimp [r]; have := min_le_left (g.radius/2) (ρ*smin/2); linarith [g.radius_pos]
  have hrρ : r ≤ ρ*smin := by dsimp [r]; have := min_le_right (g.radius/2) (ρ*smin/2); nlinarith
  let B : ℝ := max M 0/(Real.sqrt smin*smin)
  have hp' : p.cutoff=g.datum.cutoff ∧ p.exponent<1 := ⟨hp.1,hp.2.2.2⟩
  obtain ⟨zr,vr,coord,hzr,hvr,hgood⟩ := Packet06RoundedIntrinsicPeaks.rounded_peaks n hn g η hη.le
    zsharp vsharp hcert hN hsharpRe hsharpIm Q hsharpQ p hp' sys hE hcoeff r hr hrg B
  have hnearLimit : Tendsto (fun j => |(zr j).re-zbase.re|) atTop (𝓝 |zsharp.re-zbase.re|) := by
    exact (((Complex.continuous_re.continuousAt.tendsto.comp hzr).sub_const zbase.re).abs)
  have hnearEv : ∀ᶠ j in atTop, |(zr j).re-zbase.re| < zbase.re/2 :=
    (tendsto_order.mp hnearLimit).2 _ hnear'
  obtain ⟨j,hj⟩ := (hgood.and hnearEv).exists
  have hjgood := hj.1
  have hjclose := hj.2
  have hjker : ComplexConvolutionAnalytic.volumeBlock (rounded n hn g η hη.le j) (zr j) 1 (vr j)=0 := by
    obtain ⟨w,ψ,_,hk,_,_⟩ := hjgood.2.2.2.1
    exact hk
  have hjχ (i : Fin N) (x : Maxwell.Space) (hx : x ∈ ball (g.center i) r) :
      (rounded n hn g η hη.le j).value (VectorFourier.coordinateMap x) ≠ 0 := by
    apply (Packet06RoundedPlacement.sphere_susceptibility_positive n hn g η hη.le j x ?_).ne'
    apply g.outer_inside i
    exact closedBall_subset_closedBall (hrg.trans g.radius_outer) (ball_subset_closedBall hx)
  obtain ⟨_,_,_,hcround,_,_,_,_,_⟩ := Packet06RoundedInsertion.admissible
    (fun _ : Fin N => g.datum) (fun _ => g.radius) g.center (n^2) (sq_nonneg n)
    (fun _ => g.contrast.le) (fun _ => g.radius_outer) g.outer_disjoint (fun _ => g.radius_pos)
    (ModalWeightedMode.coefficient n hn) η hη.le (ModalWeightedMode.coefficient_support n hn)
    (Packet06SphereSymmetry.sphere_axial n hn) (Packet06SphereSymmetry.sphere_meridional n hn) g.onAxis
    (fun i => (g.outer_inside i).trans ball_subset_closedBall)
  have hroundSupport : ∀ x : Maxwell.Space, x ∉ closedBall 0 1 →
      (rounded n hn g η hη.le j).value (VectorFourier.coordinateMap x)=0 := hcround j
  have hpeak := hjgood.2.2.2.2.2.2.2
  obtain ⟨sc,hsc,hfreq,him,hquality,hplacedSupport,hplacedKer,hplacedN,hplacedOut,hplacedPeak⟩ :=
    Packet06PlacedModePeaks.place_mode (rounded n hn g η hη.le j) (zr j) (vr j) hroundSupport hjker
      hjgood.2.2.2.2.1 hjgood.1 hjgood.2.1 Q hjgood.2.2.1 target htarget
      (Packet07PlanarCenters.planeEmbed uₚ) zbase hbasepos hjclose g.center r hr coord M hjχ (by simpa [B,smin] using hpeak)
  have hsceq : sc=target/(zr j).re := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hfreq
    apply (eq_div_iff hjgood.1.ne').2
    exact hfreq
  have hcluster' : ∀ i, closedBall (g.center i) g.datum.cutoff.rOut ⊆ ball 0 (rp*target/(2*zbase.re)) := by
    simpa only [δ] using hcluster
  have hgeom := Packet06PlacedClusterBalls.placed_balls g P uₚ rp target hrp htarget hpatch zbase (zr j)
    hbasepos hjgood.1 hjclose hcluster' r hr hrg
  rw [← hsceq] at hgeom
  have hsmin_le : smin ≤ sc := by
    rw [hsceq]
    dsimp [smin]
    apply (div_le_div_iff₀ (by positivity : 0 < 2*zbase.re) hjgood.1).mpr
    have hh := (abs_lt.mp hjclose).2
    nlinarith
  have hrad : r/sc ≤ ρ := by
    apply (div_le_iff₀ hsc).mpr
    exact hrρ.trans (mul_le_mul_of_nonneg_left hsmin_le hρ.le)
  have hceil : (1+η)*n^2 ≤ K^2 := by
    have hh := mul_le_mul_of_nonneg_right hηmax'.le (sq_nonneg n)
    nlinarith
  have hmat (x : Maxwell.Space) : 1 ≤ MaterialMaxwell.dielectric (placedCoefficient sc (Packet07PlanarCenters.planeEmbed uₚ)
      (rounded n hn g η hη.le j)) x ∧ _ ≤ K^2 :=
    Packet06BoundedModalMaterial.placed_bounds _ K (fun y => Packet06BoundedModalMaterial.rounded_bounds n hn g η hη.le K hK hceil j y) sc _ x
  refine ⟨n,η,hn,hη,zbase,g,zr j,vr j,j,sc,r,Packet07PlanarCenters.planeEmbed uₚ,hnK,hbasepos,hsc,div_pos hr hsc,hrad,
    hfreq,him,hquality,hmat,hjgood.2.2.2.1,hjgood.2.2.2.2.1,hplacedKer,hplacedN,hplacedOut,?_⟩
  exact ⟨hgeom.1,hgeom.2.1,hgeom.2.2.1,hgeom.2.2.2,hplacedPeak⟩
#print axioms OQ14.Packet06PhysicalPeakExistence.exists_placed_rounded_peaks
end OQ14.Packet06PhysicalPeakExistence
