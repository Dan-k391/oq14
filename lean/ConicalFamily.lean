import ConicalPotentialSplit
import ConicalInnerMaxwell
import ConicalNontrivial

/-! Actual parameter family with fixed positive contrast and a singular static exponent. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.ConicalFamily
open Set Metric OQ14.ConicalStaticVolume
open scoped Topology

abbrev Space := FourierL2.Space

theorem exists_data (χ : ContDiffBump (0 : Space)) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ p : Data, p.cutoff=χ ∧ p.contrast=d ∧ p.threshold=t ∧
      p.exponent < 1 ∧ p.eigenvalue ∈ Ioo (0 : ℝ) 2 := by
  obtain ⟨a,ha,hr⟩ := CapAngularShooting.exists_root d t hd ht ht1
  let p : Data := {
    cutoff := χ
    exponent := CapAngularShooting.exponent a
    eigenvalue := a
    contrast := d
    threshold := t
    exponent_pos := (CapAngularShooting.exponent_range a ha).1
    eigenvalue_bounds := ⟨ha.1.le,ha.2.le⟩
    contrast_nonnegative := hd.le
    threshold_pos := ht
    threshold_lt_one := ht1
    angular_root := hr
    separation := CapAngularShooting.exponent_equation a ha.1.le }
  exact ⟨p,rfl,rfl,rfl,(CapAngularShooting.exponent_range a ha).2,ha⟩

theorem cut_electric_inner (p : Data) (x : Space)
    (hx : x ∈ ball (0 : Space) p.cutoff.rIn) :
    ConicalCutoffGradient.cutElectric p.cutoff p.exponent p.eigenvalue p.threshold x=
      ConicalCapField.electric p.exponent p.eigenvalue p.threshold x := by
  have hv := p.cutoff.one_of_mem_closedBall (ball_subset_closedBall hx)
  have hd := ConicalAnnularSource.bump_fderiv_zero_inner p.cutoff x hx
  ext i
  simp only [ConicalCutoffGradient.cutElectric,PiLp.add_apply,PiLp.smul_apply,
    smul_eq_mul,ConicalCutoffGradient.cutoffGradient_apply,hv,hd,
    ContinuousLinearMap.zero_apply,mul_zero,add_zero,one_mul]

theorem localized_static_blowup (p : Data) (hν : p.exponent < 1) :
    ∃ S : Set AngularPower.Sphere, IsOpen S ∧ S.Nonempty ∧
      0 < AngularPower.angularMeasure S ∧
      ∀ M : ℝ, ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ n ∈ S,
        M < ‖ConicalCutoffGradient.cutElectric p.cutoff p.exponent p.eigenvalue p.threshold
          (r • (n : Space))‖ := by
  obtain ⟨S,hS,hne,hm,hb⟩ := ConicalNontrivial.exists_open_cone_blowup
    p.exponent p.eigenvalue p.threshold ⟨p.exponent_pos,hν⟩
    p.eigenvalue_bounds p.threshold_pos p.threshold_lt_one
  refine ⟨S,hS,hne,hm,fun M => ?_⟩
  filter_upwards [hb M,Filter.Eventually.filter_mono nhdsWithin_le_nhds
    (Iio_mem_nhds p.cutoff.rIn_pos),self_mem_nhdsWithin] with r hr hri hr0
  have hrpos : 0 < r := hr0
  intro n hn
  have hx : r • (n : Space) ∈ ball (0 : Space) p.cutoff.rIn := by
    simpa only [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      AngularPower.sphere_norm,abs_of_pos hrpos,mul_one] using hri
  rw [cut_electric_inner p _ hx]
  exact hr n hn

theorem exists_fixed_contrast_family (χ : ContDiffBump (0 : Space)) (d t : ℝ)
    (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ p : Data, p.cutoff=χ ∧ p.contrast=d ∧ p.threshold=t ∧ p.exponent < 1 ∧
      Filter.Tendsto (ConicalDynamicVolume.field p) (𝓝 0) (𝓝 (electric p)) := by
  obtain ⟨p,hχ,hd',ht',hν,_⟩ := exists_data χ d t hd ht ht1
  exact ⟨p,hχ,hd',ht',hν,ConicalDynamicVolume.field_tendsto p⟩

end OQ14.ConicalFamily

#print axioms OQ14.ConicalFamily.exists_data
#print axioms OQ14.ConicalFamily.cut_electric_inner
#print axioms OQ14.ConicalFamily.localized_static_blowup
#print axioms OQ14.ConicalFamily.exists_fixed_contrast_family
