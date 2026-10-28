import ConicalJunctionRadial
import StaticPlaneKernel

/-! Physical coordinates for the inward binary junction construction. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace OQ14.ConicalJunctionPhysical
open Set OQ14.ConicalSmoothJunction
open MeasureTheory Filter
abbrev Space := Maxwell.Space

def horizontal (x : Space) : Plane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![x 0,x 1]

def split (x : Space) : Point := (horizontal x, x 2)

def horizontalLinear : Space →ₗ[ℝ] Plane where
  toFun := horizontal
  map_add' x y := by
    ext i
    fin_cases i <;> simp [horizontal]
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [horizontal]

theorem split_continuous : Continuous split := by
  exact horizontalLinear.continuous_of_finiteDimensional.prodMk (EuclideanSpace.proj (𝕜 := ℝ) (2 : Fin 3)).continuous

def slope (t : ℝ) : ℝ := t / Real.sqrt (1-t^2)

theorem slope_properties (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    0 < slope t ∧ (slope t)^2 * (1-t^2) = t^2 := by
  have hp : 0 < 1-t^2 := by nlinarith
  have hs : 0 < Real.sqrt (1-t^2) := Real.sqrt_pos.2 hp
  have hsq := Real.sq_sqrt hp.le
  constructor
  · exact div_pos ht hs
  · unfold slope
    field_simp

theorem norm_sq_split (x : Space) : ‖x‖^2 = ‖horizontal x‖^2 + (x 2)^2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three, Fin.sum_univ_two]
  simp [horizontal, Real.norm_eq_abs, sq_abs, add_assoc]

theorem cone_angle_equivalence (m t : ℝ) (hm : 0 < m) (ht : 0 < t) (ht1 : t < 1)
    (hmt : m^2 * (1-t^2) = t^2) (x : Space) :
    m*‖horizontal x‖ < |x 2| ↔ t*‖x‖ < |x 2| := by
  have hp : 0 < 1-t^2 := by nlinarith
  have hn : 0 ≤ ‖x‖ := norm_nonneg _
  have hh : 0 ≤ ‖horizontal x‖ := norm_nonneg _
  have hz : 0 ≤ |x 2| := abs_nonneg _
  have he := norm_sq_split x
  have hez : |x 2|^2 = (x 2)^2 := sq_abs _
  have hprod := congrArg (fun v : ℝ => v * ‖horizontal x‖^2) hmt
  have hid : (1-t^2)*((m*‖horizontal x‖)^2-|x 2|^2) =
      (t*‖x‖)^2-|x 2|^2 := by nlinarith
  have h1 : 0 ≤ m*‖horizontal x‖ := mul_nonneg hm.le hh
  have h2 : 0 ≤ t*‖x‖ := mul_nonneg ht.le hn
  constructor
  · intro h
    have hsq := pow_lt_pow_left₀ h h1 (by norm_num : (2 : ℕ) ≠ 0)
    have hs : (t*‖x‖)^2 < |x 2|^2 := by nlinarith [mul_neg_of_pos_of_neg hp (sub_neg.mpr hsq)]
    nlinarith
  · intro h
    have hsq := pow_lt_pow_left₀ h h2 (by norm_num : (2 : ℕ) ≠ 0)
    have hs : (m*‖horizontal x‖)^2 < |x 2|^2 := by
      by_contra hh'
      have hp' := mul_nonneg hp.le (sub_nonneg.mpr (le_of_not_gt hh'))
      linarith
    nlinarith

theorem actual_angle (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (x : Space) (hx : x ≠ 0) :
    (split x ∈ ConicalSmoothCapGraph.sharpCone (slope t)) ↔
      t < |((ConicalCapField.unit x : Maxwell.Space)) 2| := by
  have hp := slope_properties t ht ht1
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  rw [show (split x ∈ ConicalSmoothCapGraph.sharpCone (slope t)) ↔
      slope t * ‖horizontal x‖ < |x 2| by rfl]
  rw [cone_angle_equivalence (slope t) t hp.1 ht ht1 hp.2 x]
  simp only [ConicalCapField.unit, hx, ↓reduceIte, PiLp.smul_apply, smul_eq_mul,
    abs_mul, abs_inv, abs_norm]
  rw [← div_eq_inv_mul, lt_div_iff₀ hn]

def inclusion (n : ℕ) (m a : ℝ) : Set Space := split ⁻¹' ConicalSmoothJunction.inclusion n m a

theorem inclusion_open (n : ℕ) (m a : ℝ) (hm : 0 < m) : IsOpen (inclusion n m a) :=
  (ConicalSmoothJunction.inclusion_open n m a hm).preimage split_continuous

theorem inclusion_norm_bound (n : ℕ) (m a : ℝ) (ha : 0 < a) (x : Space)
    (hx : x ∈ inclusion n m a) : ‖x‖ < a := by
  have ht : 0 < ballMargin a (split x) := hx.2.1
  dsimp [ballMargin, split] at ht
  have hnorm := norm_sq_split x
  have hn : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

theorem inclusion_material (p : ConicalStaticVolume.Data) (a : ℝ) (ha : 0 < a)
    (hcut : a ≤ p.cutoff.rOut) (n : ℕ) (x : Space)
    (hx : x ∈ inclusion n (slope p.threshold) a) :
    (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) = p.contrast := by
  have hn := inclusion_norm_bound n (slope p.threshold) a ha x hx
  have hsharp := (ConicalSmoothJunction.inclusion_subset n (slope p.threshold) a
    (slope_properties p.threshold p.threshold_pos p.threshold_lt_one).1) hx
  have hnonzero : x ≠ 0 := by
    intro hz
    have hcone : slope p.threshold * ‖horizontal x‖ < |x 2| := hsharp.1
    rw [hz] at hcone
    simp only [PiLp.zero_apply, abs_zero] at hcone
    have hnonneg := mul_nonneg (slope_properties p.threshold p.threshold_pos p.threshold_lt_one).1.le
      (norm_nonneg (horizontal 0))
    linarith
  have hangle := (actual_angle p.threshold p.threshold_pos p.threshold_lt_one x hnonzero).mp hsharp.1
  rw [ConicalSeparatedSource.material_eq_inside p a x hn.le,
    ConicalStaticVolume.coefficient_spatial]
  have hcut' : x ∈ Metric.closedBall (0 : Space) p.cutoff.rOut := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le.trans hcut
  simp [ConicalAnnularSource.dielectric, hcut', ConicalCapField.permittivity,
    CapSturmLiouville.coefficient, not_le.mpr hangle]

def binaryMaterial (p : ConicalStaticVolume.Data) (a : ℝ) (n : ℕ) : StaticCoefficient.Coefficient where
  value := by classical exact fun ξ => if VectorFourier.coordinateMap.symm ξ ∈ inclusion n (slope p.threshold) a then p.contrast else 0
  bound := p.contrast
  measurable := measurable_const.piecewise
    ((inclusion_open n (slope p.threshold) a
      (slope_properties p.threshold p.threshold_pos p.threshold_lt_one).1).measurableSet.preimage
        VectorFourier.coordinateMap.symm.measurable) measurable_const
  nonnegative ξ := by
    classical
    split_ifs
    · exact p.contrast_nonnegative
    · exact le_rfl
  bounded ξ := by
    classical
    split_ifs
    · exact le_rfl
    · exact p.contrast_nonnegative

theorem binary_below_original (p : ConicalStaticVolume.Data) (a : ℝ) (ha : 0 < a)
    (hcut : a ≤ p.cutoff.rOut) (n : ℕ) (ξ : FourierL2.Space) :
    (binaryMaterial p a n).value ξ ≤ (ConicalSeparatedSource.material p a).value ξ := by
  classical
  by_cases h : VectorFourier.coordinateMap.symm ξ ∈ inclusion n (slope p.threshold) a
  · have he := inclusion_material p a ha hcut n (VectorFourier.coordinateMap.symm ξ) h
    simpa [binaryMaterial, h] using he.symm.le
  · simpa [binaryMaterial, h] using (ConicalSeparatedSource.material p a).nonnegative ξ

theorem original_binary (p : ConicalStaticVolume.Data) (a : ℝ)
    (hcut : a ≤ p.cutoff.rOut) (x : Space) (hx : x ≠ 0) (hboundary : ‖x‖ ≠ a) :
    (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) =
      (by classical exact if split x ∈ ConicalSmoothCapGraph.sharpCone (slope p.threshold) ∧ ‖x‖ < a
      then p.contrast else 0) := by
  classical
  by_cases hn : ‖x‖ < a
  · have hc : x ∈ Metric.closedBall (0 : Space) p.cutoff.rOut := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le.trans hcut
    rw [ConicalSeparatedSource.material_eq_inside p a x hn.le,
      ConicalStaticVolume.coefficient_spatial]
    have hang := actual_angle p.threshold p.threshold_pos p.threshold_lt_one x hx
    simp only [ConicalAnnularSource.dielectric, hc, ↓reduceIte, ConicalCapField.permittivity,
      CapSturmLiouville.coefficient, hn, and_true]
    rw [hang]
    split_ifs <;> linarith
  · have hout : x ∉ Metric.closedBall (0 : Space) a := by
      simp only [Metric.mem_closedBall, dist_zero_right, not_le]
      exact lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hboundary)
    rw [ConicalSeparatedSource.material_compact p a x hout]
    simp [hn]

theorem eventually_binary_matches (p : ConicalStaticVolume.Data) (a : ℝ) (ha : 0 < a)
    (hcut : a ≤ p.cutoff.rOut) (x : Space) (hx : x ≠ 0)
    (hh : horizontal x ≠ 0) (hboundary : ‖x‖ ≠ a) :
    ∀ᶠ n : ℕ in Filter.atTop,
      (binaryMaterial p a n).value (VectorFourier.coordinateMap x) =
        (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) := by
  classical
  have hb : ballMargin a (split x) ≠ 0 := by
    intro hz
    have hn := norm_sq_split x
    dsimp [ballMargin, split] at hz
    have hnx : 0 ≤ ‖x‖ := norm_nonneg _
    apply hboundary
    nlinarith
  have hj : 0 < (|(split x).2| - slope p.threshold * ‖(split x).1‖)^2 +
      (ballMargin a (split x))^2 := by positivity
  have he := ConicalSmoothJunction.eventually_matches (slope p.threshold) a
    (slope_properties p.threshold p.threshold_pos p.threshold_lt_one).1 (split x) hh hj
  filter_upwards [he] with n hn
  rw [original_binary p a hcut x hx hboundary]
  have hball : (0 < ballMargin a (split x)) ↔ ‖x‖ < a := by
    have hsq := norm_sq_split x
    have hnx : 0 ≤ ‖x‖ := norm_nonneg _
    dsimp [ballMargin, split]
    constructor <;> intro h <;> nlinarith
  simp only [inclusion, mem_preimage, mem_inter_iff, mem_setOf_eq, hball] at hn
  simp only [binaryMaterial, MeasurableEquiv.symm_apply_apply, inclusion, mem_preimage]
  rw [hn]
  split_ifs <;> rfl

theorem almost_everywhere_binary_matches (p : ConicalStaticVolume.Data) (a : ℝ)
    (ha : 0 < a) (hcut : a ≤ p.cutoff.rOut) :
    ∀ᵐ x : Space ∂volume, ∀ᶠ n : ℕ in atTop,
      (binaryMaterial p a n).value (VectorFourier.coordinateMap x) =
        (ConicalSeparatedSource.material p a).value (VectorFourier.coordinateMap x) := by
  let L : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).toLinearMap
  have hproper : LinearMap.ker L ≠ ⊤ := by
    intro he
    have hb : Maxwell.basis 0 ∈ LinearMap.ker L := by rw [he]; exact Submodule.mem_top
    have : L (Maxwell.basis 0) = 0 := LinearMap.mem_ker.mp hb
    simp [L, Maxwell.basis] at this
  have hnull : (volume : Measure Space) (LinearMap.ker L) = 0 :=
    Measure.addHaar_submodule volume (LinearMap.ker L) hproper
  have hcoord : ∀ᵐ x : Space ∂volume, x 0 ≠ 0 := by
    have hae : ∀ᵐ x : Space ∂volume, x ∉ LinearMap.ker L := by
      rw [ae_iff]
      simpa using hnull
    filter_upwards [hae] with x hx
    simpa [L, LinearMap.mem_ker] using hx
  have hsphere : ∀ᵐ x : Space ∂volume, ‖x‖ ≠ a := by
    have hn : (volume : Measure Space) (Metric.sphere 0 a) = 0 := Measure.addHaar_sphere volume 0 a
    have hae : ∀ᵐ x : Space ∂volume, x ∉ Metric.sphere 0 a := by
      rw [ae_iff]
      simpa only [Metric.sphere, dist_zero_right, not_not] using hn
    filter_upwards [hae] with x hx
    simpa only [Metric.mem_sphere, dist_zero_right] using hx
  filter_upwards [hcoord, hsphere] with x hc hs
  have hx : x ≠ 0 := by intro h; apply hc; simp [h]
  have hh : horizontal x ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : Plane => v 0) h
    apply hc
    simpa [horizontal] using h0
  exact eventually_binary_matches p a ha hcut x hx hh hs

end OQ14.ConicalJunctionPhysical
#print axioms OQ14.ConicalJunctionPhysical.norm_sq_split
#print axioms OQ14.ConicalJunctionPhysical.slope_properties
#print axioms OQ14.ConicalJunctionPhysical.cone_angle_equivalence
#print axioms OQ14.ConicalJunctionPhysical.actual_angle
#print axioms OQ14.ConicalJunctionPhysical.inclusion_norm_bound
#print axioms OQ14.ConicalJunctionPhysical.inclusion_material
#print axioms OQ14.ConicalJunctionPhysical.binary_below_original
#print axioms OQ14.ConicalJunctionPhysical.eventually_binary_matches
#print axioms OQ14.ConicalJunctionPhysical.almost_everywhere_binary_matches
