import ConicalCapField
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Genuine nonvanishing and open-cone lower bounds for the actual conical field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.ConicalNontrivial
open MeasureTheory Metric Set Real OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapH1
  OQ14.ConicalCapField OQ14.CapLegendreSeries OQ14.CapAngularShooting OQ14.CapSturmLiouville
open scoped Topology InnerProductSpace

theorem poleD_at_one (a : ℝ) : poleD a 1 = a/2 := by
  unfold poleD powerSum
  norm_num only [sub_self,zero_div]
  rw [tsum_eq_single 0]
  · simp [derivativeCoeff,poleCoeff]
    ring
  · intro n hn
    simp [zero_pow hn]

theorem exteriorD_at_one_positive (a t : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    0 < exteriorD a t 1 := by
  rw [exteriorD,poleD_at_one]
  exact mul_pos (odd_positive a t ⟨ha.1.le,ha.2.le⟩ ht ht1) (div_pos ha.1 (by norm_num))

theorem angularElectric_norm_ge (ν a t : ℝ) (n : Sphere) :
    ν*field a t n ≤ ‖angularElectric ν a t n‖ := by
  have h := angularElectric_norm_sq ν a t n
  nlinarith [norm_nonneg (angularElectric ν a t n),sq_nonneg ‖SphereCapH1.gradient a t n‖]

theorem exists_open_cone_lower_bound (ν a t : ℝ) (hν : 0 < ν) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    ∃ (c : ℝ) (S : Set Sphere), 0 < c ∧ IsOpen S ∧ S.Nonempty ∧ 0 < angularMeasure S ∧
      ∀ n ∈ S, ∀ r : ℝ, 0 < r → c*r^(ν-1) ≤ ‖electric ν a t (r • (n : Space))‖ := by
  let b : ℝ := field a t north/2
  have hb : 0 < b := by dsimp only [b]; exact half_pos (field_nonzero a t ha ht ht1)
  let S : Set Sphere := {n | b < field a t n}
  have hS : IsOpen S := isOpen_lt continuous_const (SphereCapWeak.profile_continuous a t ha ht ht1)
  have hmem : north ∈ S := by change field a t north/2 < field a t north; linarith [field_nonzero a t ha ht ht1]
  refine ⟨ν*b,S,mul_pos hν hb,hS,⟨north,hmem⟩,
    OQ14.SphereMeasure.volume_toSphere_open_pos S hS ⟨north,hmem⟩,?_⟩
  intro n hn r hr
  have hn' : b < field a t n := hn
  have hl : ν*b ≤ ‖angularElectric ν a t n‖ :=
    (mul_le_mul_of_nonneg_left hn'.le hν.le).trans
      (angularElectric_norm_ge ν a t n)
  rw [electric_polar ν a t r hr n,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr.le _),mul_comm (ν*b)]
  exact mul_le_mul_of_nonneg_left hl (Real.rpow_nonneg hr.le _)

theorem exists_nonzero_angular_gradient (a t : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) :
    ∃ n : Sphere, t < (n : Space) 2 ∧ 0 < ‖SphereCapH1.gradient a t n‖ := by
  have hpos := exteriorD_at_one_positive a t ha ht ht1
  have hc : ContinuousAt (exteriorD a t) 1 :=
    (exteriorD_hasDerivAt a t 1 ⟨ha.1.le,ha.2.le⟩ (by norm_num)).continuousAt
  obtain ⟨ε,hε,he⟩ := Metric.eventually_nhds_iff.mp (hc.eventually (Ioi_mem_nhds hpos))
  let δ : ℝ := min (ε/2) ((1-t)/2)
  have hδ : 0 < δ := lt_min (by positivity) (by linarith)
  have hδε : δ < ε := (min_le_left _ _).trans_lt (by linarith)
  have hδt : δ ≤ (1-t)/2 := min_le_right _ _
  let z : ℝ := 1-δ
  have hzt : t < z := by dsimp only [z]; linarith
  have hz1 : z < 1 := by dsimp only [z]; linarith
  have hz0 : -1 < z := by linarith
  have hez : 0 < exteriorD a t z := by
    apply he
    rw [Real.dist_eq,abs_of_nonpos (by dsimp only [z]; linarith)]
    dsimp only [z]
    linarith
  let n : Sphere := ⟨SphereAxialTests.latitude z 0,by
    rw [mem_sphere,dist_zero_right,SphereAxialTests.latitude_norm z 0 ⟨hz0.le,hz1.le⟩]⟩
  have hn : (n : Space) 2 = z := SphereCapWeak.latitude_axial z 0
  have hg : ‖basis 2-(n : Space) 2 • (n : Space)‖^2 = 1-z^2 := by
    simpa only [ConicalAngularTrial.tangentGradient,ConicalAngularTrial.coordinate,hn] using
      ConicalAngularTrial.tangentGradient_norm_sq 2 n
  have hgn : 0 < ‖basis 2-(n : Space) 2 • (n : Space)‖ := by
    nlinarith [norm_nonneg (basis 2-(n : Space) 2 • (n : Space))]
  refine ⟨n,by simpa only [hn] using hzt,?_⟩
  rw [SphereCapH1.gradient,norm_smul,hn]
  have hs : CapSturmLiouville.slope a t z = exteriorD a t z := by
    simp [CapSturmLiouville.slope,not_le.mpr hzt,show ¬z < -t by linarith]
  rw [hs,Real.norm_eq_abs,abs_of_pos hez]
  exact mul_pos hez (by simpa only [hn] using hgn)

theorem gradient_continuousAt_cap (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (n : Sphere) (hn : t < (n : Space) 2) :
    ContinuousAt (SphereCapH1.gradient a t) n := by
  have cx : Continuous (fun m : Sphere => (m : Space) 2) := ConicalAngularTrial.coordinate_continuous 2
  have hd := (exteriorD_hasDerivAt a t ((n : Space) 2) ha
    (right_argument t _ ht ht1 ⟨hn.le,(SphereCapWeak.coordinate_range n).2⟩)).continuousAt
  have hc : ContinuousAt (fun m : Sphere => exteriorD a t ((m : Space) 2) •
      (basis 2-(m : Space) 2 • (m : Space))) n :=
    (hd.comp (f := fun m : Sphere => (m : Space) 2) cx.continuousAt).smul
      (continuous_const.sub (cx.smul continuous_subtype_val)).continuousAt
  apply hc.congr
  filter_upwards [cx.continuousAt.eventually (Ioi_mem_nhds hn)] with m hm
  have hm' : t < (m : Space) 2 := hm
  simp [SphereCapH1.gradient,CapSturmLiouville.slope,not_le.mpr hm',show ¬(m : Space) 2 < -t by linarith]

theorem exists_open_gradient_positive (a t : ℝ) (ha : a ∈ Ioo (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ∃ S : Set Sphere, IsOpen S ∧ S.Nonempty ∧ 0 < angularMeasure S ∧
      ∀ n ∈ S, 0 < ‖SphereCapH1.gradient a t n‖ := by
  obtain ⟨n,hn,hpos⟩ := exists_nonzero_angular_gradient a t ha ht ht1
  have hc := (gradient_continuousAt_cap a t ⟨ha.1.le,ha.2.le⟩ ht ht1 n hn).norm
  obtain ⟨S,hsub,hS,hnS⟩ := _root_.mem_nhds_iff.mp (hc.eventually (Ioi_mem_nhds hpos))
  exact ⟨S,hS,⟨n,hnS⟩,OQ14.SphereMeasure.volume_toSphere_open_pos S hS ⟨n,hnS⟩,hsub⟩

theorem singular_power_tendsto (ν : ℝ) (hν : ν < 1) :
    Filter.Tendsto (fun r : ℝ => r^(ν-1)) (𝓝[>] (0 : ℝ)) Filter.atTop := by
  have h := (tendsto_rpow_atTop (sub_pos.mpr hν)).comp tendsto_inv_nhdsGT_zero
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hp : 0 < r := hr
  dsimp only [Function.comp_apply]
  rw [Real.inv_rpow hp.le,← Real.rpow_neg hp.le]
  congr 1
  ring

theorem exists_open_cone_blowup (ν a t : ℝ) (hν : ν ∈ Ioo (0 : ℝ) 1)
    (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ∃ S : Set Sphere, IsOpen S ∧ S.Nonempty ∧ 0 < angularMeasure S ∧
      ∀ M : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ n ∈ S, M < ‖electric ν a t (r • (n : Space))‖ := by
  obtain ⟨c,S,hc,hS,hne,hm,hb⟩ := exists_open_cone_lower_bound ν a t hν.1 ha ht ht1
  refine ⟨S,hS,hne,hm,fun M => ?_⟩
  have h := (singular_power_tendsto ν hν.2).const_mul_atTop hc
  filter_upwards [h.eventually_gt_atTop M,self_mem_nhdsWithin] with r hr hp
  intro n hn
  exact hr.trans_le (hb n hn r hp)

end OQ14.ConicalNontrivial

#print axioms OQ14.ConicalNontrivial.poleD_at_one
#print axioms OQ14.ConicalNontrivial.exteriorD_at_one_positive
#print axioms OQ14.ConicalNontrivial.angularElectric_norm_ge
#print axioms OQ14.ConicalNontrivial.exists_open_cone_lower_bound
#print axioms OQ14.ConicalNontrivial.exists_nonzero_angular_gradient
#print axioms OQ14.ConicalNontrivial.gradient_continuousAt_cap
#print axioms OQ14.ConicalNontrivial.exists_open_gradient_positive
#print axioms OQ14.ConicalNontrivial.singular_power_tendsto
#print axioms OQ14.ConicalNontrivial.exists_open_cone_blowup
