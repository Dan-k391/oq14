import SphereSurfaceFubini

/-! The actual cap profile has an L2 weak tangential gradient on the geometric unit sphere. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace OQ14.SphereCapH1
open MeasureTheory Metric Set OQ14.Maxwell OQ14.AngularPower OQ14.SphereCapWeak
open scoped Topology InnerProductSpace ENNReal

def field (a t : ℝ) (n : Sphere) : ℝ := CapSturmLiouville.profile a t ((n : Space) 2)
def gradient (a t : ℝ) (n : Sphere) : Space :=
  CapSturmLiouville.slope a t ((n : Space) 2) • (basis 2-(n : Space) 2 • (n : Space))

/-- Extrinsic distribution characterization: tangent almost everywhere, with the actual
surface-divergence correction for each projected Cartesian basis tangent and ambient C1 test. -/
def HasWeakTangentialGradient (f : Sphere → ℝ) (G : Sphere → Space) : Prop :=
  (∀ᵐ n : Sphere ∂angularMeasure, ⟪(n : Space),G n⟫_ℝ = 0) ∧
  ∀ (i : Fin 3) (ψ : Space → ℝ), ContDiff ℝ 1 ψ →
    (∫ n : Sphere, (G n) i*ψ n ∂angularMeasure) =
      -(∫ n : Sphere, f n*(fderiv ℝ ψ n (basis i-(n : Space) i • (n : Space))-
        2*(n : Space) i*ψ n) ∂angularMeasure)

/-- H1 is specified here by L2 membership and the proved distribution characterization. -/
def MemH1 (f : Sphere → ℝ) : Prop :=
  MemLp f 2 angularMeasure ∧ ∃ G : Sphere → Space,
    MemLp G 2 angularMeasure ∧ HasWeakTangentialGradient f G

theorem HasWeakTangentialGradient.const_smul {f : Sphere → ℝ} {G : Sphere → Space}
    (h : HasWeakTangentialGradient f G) (c : ℝ) : HasWeakTangentialGradient (c • f) (c • G) := by
  constructor
  · filter_upwards [h.1] with n hn
    simp only [Pi.smul_apply,inner_smul_right,hn,mul_zero]
  · intro i ψ hψ
    have he := h.2 i ψ hψ
    simp only [Pi.smul_apply,PiLp.smul_apply,smul_eq_mul,mul_assoc,integral_const_mul]
    rw [he]
    ring_nf

theorem MemH1.const_smul {f : Sphere → ℝ} (h : MemH1 f) (c : ℝ) : MemH1 (c • f) := by
  obtain ⟨hf,G,hG,hw⟩ := h
  exact ⟨hf.const_smul c,c • G,hG.const_smul c,hw.const_smul c⟩

theorem field_memLp (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (p : ℝ≥0∞) : MemLp (field a t) p angularMeasure := by
  have hc : Continuous (field a t) := profile_continuous a t ha ht ht1
  obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C (Filter.Eventually.of_forall (fun n => hC n (mem_univ n)))

theorem tangent_norm_le (n : Sphere) : ‖basis 2-(n : Space) 2 • (n : Space)‖ ≤ 1 := by
  have h := OQ14.ConicalAngularTrial.tangentGradient_norm_sq 2 n
  change ‖basis 2-(n : Space) 2 • (n : Space)‖^2 = 1-((n : Space) 2)^2 at h
  nlinarith [norm_nonneg (basis 2-(n : Space) 2 • (n : Space)),sq_nonneg ((n : Space) 2)]

theorem gradient_memLp (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1)
    (p : ℝ≥0∞) : MemLp (gradient a t) p angularMeasure := by
  have ct : Continuous (fun n : Sphere => basis 2-(n : Space) 2 • (n : Space)) :=
    continuous_const.sub ((OQ14.ConicalAngularTrial.coordinate_continuous 2).smul continuous_subtype_val)
  have hm : AEStronglyMeasurable (gradient a t) angularMeasure :=
    (slope_aestronglyMeasurable a t ha ht ht1).smul ct.aestronglyMeasurable
  obtain ⟨C,hC,hb⟩ := slope_bound a t ha ht ht1
  apply MemLp.of_bound hm C
  filter_upwards with n
  calc
    ‖gradient a t n‖ = ‖CapSturmLiouville.slope a t ((n : Space) 2)‖*
      ‖basis 2-(n : Space) 2 • (n : Space)‖ := norm_smul _ _
    _ ≤ C*1 := mul_le_mul (hb _ (coordinate_range n)) (tangent_norm_le n) (norm_nonneg _) hC
    _ = C := mul_one _

theorem gradient_tangent (a t : ℝ) (n : Sphere) : ⟪(n : Space),gradient a t n⟫_ℝ = 0 := by
  have h := OQ14.ConicalAngularTrial.tangentGradient_inner 2 n
  change ⟪(n : Space),basis 2-(n : Space) 2 • (n : Space)⟫_ℝ = 0 at h
  rw [gradient,inner_smul_right,h,mul_zero]

theorem field_hasWeakTangentialGradient (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) : HasWeakTangentialGradient (field a t) (gradient a t) := by
  refine ⟨Filter.Eventually.of_forall (gradient_tangent a t),?_⟩
  intro i ψ hψ
  simpa only [field,gradient,PiLp.smul_apply,smul_eq_mul] using
    OQ14.SphereSurfaceFubini.cap_surface_ibp a t ha ht ht1 i ψ hψ

theorem field_memH1 (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    MemH1 (field a t) :=
  ⟨field_memLp a t ha ht ht1 2,gradient a t,gradient_memLp a t ha ht ht1 2,
    field_hasWeakTangentialGradient a t ha ht ht1⟩

theorem field_weighted_weak (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (ht : 0 < t) (ht1 : t < 1) (hr : CapAngularShooting.determinant d t a = 0)
    (ψ : Space → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      fderiv ℝ ψ n (gradient a t n) ∂angularMeasure) =
    a*∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
      (field a t n*ψ n) ∂angularMeasure := by
  simpa only [field,gradient,map_smul,smul_eq_mul] using sphere_weak_identity a d t ha ht ht1 hr ψ hψ

def north : Sphere := ⟨basis 2,by simp [mem_sphere,dist_zero_right,basis]⟩

theorem field_nonzero (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    0 < field a t north := by
  simpa [field,north,basis] using CapSturmLiouville.profile_nonzero a t ha ht ht1

theorem field_not_ae_zero (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    ¬field a t =ᵐ[angularMeasure] 0 := by
  intro h
  have hz := OQ14.SphereMeasure.continuous_zero_of_ae_zero (field a t)
    (profile_continuous a t ha ht ht1) h
  have hn := congrFun hz north
  exact (field_nonzero a t ha ht ht1).ne' hn

theorem field_mass_positive (a t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    0 < ∫ n : Sphere, field a t n^2 ∂angularMeasure := by
  have hc := (profile_continuous a t ha ht ht1).pow 2
  have hi := OQ14.ConicalAngularTrial.continuous_integrable _ hc
  have hn : 0 ≤ ∫ n : Sphere, field a t n^2 ∂angularMeasure := integral_nonneg (fun n => sq_nonneg _)
  by_contra! hz
  have he := OQ14.SphereMeasure.continuous_zero_of_integral_zero _ hc hi (fun n => sq_nonneg _)
    (le_antisymm hz hn)
  have hp := congrFun he north
  have hpos := field_nonzero a t ha ht ht1
  change field a t north^2 = 0 at hp
  nlinarith

def weightedMass (a d t : ℝ) : ℝ :=
  ∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*field a t n^2 ∂angularMeasure

theorem weightedMass_positive (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) : 0 < weightedMass a d t := by
  have hc := (profile_continuous a t ha ht ht1).pow 2
  have hi := OQ14.ConicalAngularTrial.continuous_integrable _ hc
  have hw := coefficient_integrable _ hi d t
  have hm : (∫ n : Sphere, field a t n^2 ∂angularMeasure) ≤ weightedMass a d t := by
    apply integral_mono hi hw
    intro n
    have hcoef : 1 ≤ CapSturmLiouville.coefficient d t ((n : Space) 2) := by
      unfold CapSturmLiouville.coefficient
      split_ifs <;> linarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (sq_nonneg (field a t n))
  exact lt_of_lt_of_le (field_mass_positive a t ha ht ht1) hm

def normalizedField (a d t : ℝ) (n : Sphere) : ℝ := field a t n/Real.sqrt (weightedMass a d t)

theorem normalizedField_mass (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2)
    (hd : 0 ≤ d) (ht : 0 < t) (ht1 : t < 1) :
    (∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*normalizedField a d t n^2 ∂angularMeasure) = 1 := by
  have hp := weightedMass_positive a d t ha hd ht ht1
  have he : (fun n : Sphere => CapSturmLiouville.coefficient d t ((n : Space) 2)*normalizedField a d t n^2) =
      fun n : Sphere => (CapSturmLiouville.coefficient d t ((n : Space) 2)*field a t n^2)/weightedMass a d t := by
    funext n
    rw [normalizedField,div_pow,Real.sq_sqrt hp.le,mul_div_assoc]
  rw [he,integral_div]
  exact div_self hp.ne'

theorem normalizedField_memH1 (a d t : ℝ) (ha : a ∈ Icc (0 : ℝ) 2) (ht : 0 < t) (ht1 : t < 1) :
    MemH1 (normalizedField a d t) := by
  have h := (field_memH1 a t ha ht ht1).const_smul ((Real.sqrt (weightedMass a d t))⁻¹)
  have he : normalizedField a d t = (Real.sqrt (weightedMass a d t))⁻¹ • field a t := by
    funext n
    simp only [Pi.smul_apply,smul_eq_mul,normalizedField,div_eq_mul_inv,mul_comm]
  rw [he]
  exact h

theorem exists_nonzero_H1_eigenfunction (d t : ℝ) (hd : 0 < d) (ht : 0 < t) (ht1 : t < 1) :
    ∃ a ∈ Ioo (0 : ℝ) 2, CapAngularShooting.exponent a ∈ Ioo (0 : ℝ) 1 ∧
      MemH1 (field a t) ∧ ¬field a t =ᵐ[angularMeasure] 0 ∧ 0 < weightedMass a d t ∧
      (∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*normalizedField a d t n^2 ∂angularMeasure) = 1 ∧
      ∀ (ψ : Space → ℝ), ContDiff ℝ 1 ψ →
        (∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
          fderiv ℝ ψ n (gradient a t n) ∂angularMeasure) =
        a*∫ n : Sphere, CapSturmLiouville.coefficient d t ((n : Space) 2)*
          (field a t n*ψ n) ∂angularMeasure := by
  obtain ⟨a,ha,hr⟩ := CapAngularShooting.exists_root d t hd ht ht1
  refine ⟨a,ha,CapAngularShooting.exponent_range a ha,
    field_memH1 a t ⟨ha.1.le,ha.2.le⟩ ht ht1,
    field_not_ae_zero a t ⟨ha.1.le,ha.2.le⟩ ht ht1,
    weightedMass_positive a d t ⟨ha.1.le,ha.2.le⟩ hd.le ht ht1,
    normalizedField_mass a d t ⟨ha.1.le,ha.2.le⟩ hd.le ht ht1,?_⟩
  intro ψ hψ
  exact field_weighted_weak a d t ⟨ha.1.le,ha.2.le⟩ ht ht1 hr ψ hψ

end OQ14.SphereCapH1

#print axioms OQ14.SphereCapH1.HasWeakTangentialGradient.const_smul
#print axioms OQ14.SphereCapH1.MemH1.const_smul
#print axioms OQ14.SphereCapH1.field_memLp
#print axioms OQ14.SphereCapH1.tangent_norm_le
#print axioms OQ14.SphereCapH1.gradient_memLp
#print axioms OQ14.SphereCapH1.gradient_tangent
#print axioms OQ14.SphereCapH1.field_hasWeakTangentialGradient
#print axioms OQ14.SphereCapH1.field_memH1
#print axioms OQ14.SphereCapH1.field_weighted_weak
#print axioms OQ14.SphereCapH1.field_nonzero
#print axioms OQ14.SphereCapH1.field_not_ae_zero
#print axioms OQ14.SphereCapH1.field_mass_positive
#print axioms OQ14.SphereCapH1.weightedMass_positive
#print axioms OQ14.SphereCapH1.normalizedField_mass
#print axioms OQ14.SphereCapH1.normalizedField_memH1
#print axioms OQ14.SphereCapH1.exists_nonzero_H1_eigenfunction
