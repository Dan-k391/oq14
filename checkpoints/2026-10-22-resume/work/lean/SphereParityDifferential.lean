import FiniteSphereIncident

/-! Actual source-variable continuity and uniform differential bounds of parity point kernels. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.SphereParityDifferential
open MeasureTheory Metric Set SphereReactionKernel SphereWaveCalculus SphereMagneticKernel
open SphereMagneticParity (magneticReaction)
open Maxwell (dcoord basis)
open scoped Topology
abbrev Space := FourierL2.Space

private theorem moment_continuous (a : Sphere → ℂ) (ha : Continuous a) (A : ℝ)
    (hA : ∀ θ, ‖a θ‖ ≤ A) (k : ℝ) : Continuous (moment a k) :=
  continuous_iff_continuousAt.mpr (fun x => (moment_hasFDerivAt a ha A hA k x).continuousAt)

private theorem amplitude_continuous (i j : Fin 3) : Continuous (fun θ : Sphere => amplitude θ i j) :=
  continuous_const.sub ((coordinate_continuous i).mul (coordinate_continuous j))

private theorem weighted_bound (a : Sphere → ℂ) (ha : ∀ θ, ‖a θ‖ ≤ 2) (i : Fin 3) :
    ∀ θ, ‖a θ*coordinate i θ‖ ≤ 2 := fun θ =>
  (norm_mul _ _).trans_le ((mul_le_mul (ha θ) (coordinate_bound i θ) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))

theorem J_partial_continuous (k : ℝ) (a i j : Fin 3) :
    Continuous (fun x => dcoord (fun z => J k z i j) x a) := by
  simp_rw [J_partial]
  exact continuous_const.mul (moment_continuous _ ((amplitude_continuous i j).mul (coordinate_continuous a)) 2
    (weighted_bound _ (fun θ => amplitude_bound θ i j) a) k)

theorem K_partial_continuous (k : ℝ) (a i j : Fin 3) :
    Continuous (fun x => dcoord (fun z => K k z i j) x a) := by
  simp_rw [SphereMaxwell.K_partial]
  exact continuous_const.mul (moment_continuous _ ((transverse_continuous i j).mul (coordinate_continuous a)) 2
    (weighted_bound _ (transverse_bound i j) a) k)

theorem electric_partial_source_continuous (e : Bool) (k : ℝ) (x : Space) (a i j : Fin 3) :
    Continuous (fun y => dcoord (fun z => reaction e k z y i j) x a) := by
  simp_rw [SphereMagneticParity.reaction_partial]
  exact continuous_const.mul (((J_partial_continuous k a i j).comp (continuous_const.sub continuous_id)).add
    (continuous_const.mul ((J_partial_continuous k a i j).comp (continuous_const.sub continuous_id))))

theorem magnetic_partial_source_continuous (e : Bool) (k : ℝ) (x : Space) (a i j : Fin 3) :
    Continuous (fun y => dcoord (fun z => magneticReaction e k z y i j) x a) := by
  simp_rw [SphereParityMaxwell.magnetic_partial]
  exact continuous_const.mul (((K_partial_continuous k a i j).comp (continuous_const.sub continuous_id)).sub
    (continuous_const.mul ((K_partial_continuous k a i j).comp (continuous_const.sub continuous_id))))

theorem clm_basis_expansion (F : Space →L[ℝ] ℂ) (v : Space) :
    F v=∑ a : Fin 3, (v a) • F (basis a) := by
  have hv : v=∑ a : Fin 3, (v a) • basis a := by
    ext i
    rw [Fin.sum_univ_three]
    fin_cases i <;> simp [basis,EuclideanSpace.single_apply]
  conv_lhs => rw [hv]
  simp only [map_sum,map_smul]

private theorem differential_source_continuous (K : Space → Space → ℂ) (x : Space)
    (hc : ∀ a : Fin 3, Continuous (fun y => dcoord (fun z => K z y) x a)) :
    Continuous (fun y => fderiv ℝ (fun z => K z y) x) := by
  apply continuous_clm_apply.mpr
  intro v
  have he (y : Space) : fderiv ℝ (fun z => K z y) x v=
      ∑ a : Fin 3, (v a) • dcoord (fun z => K z y) x a := clm_basis_expansion _ v
  simp_rw [he]
  exact continuous_finset_sum _ (fun a _ => continuous_const.smul (hc a))

theorem electric_differential_source_continuous (e : Bool) (k : ℝ) (x : Space) (i j : Fin 3) :
    Continuous (fun y => fderiv ℝ (fun z => reaction e k z y i j) x) :=
  differential_source_continuous _ x (fun a => electric_partial_source_continuous e k x a i j)

theorem magnetic_differential_source_continuous (e : Bool) (k : ℝ) (x : Space) (i j : Fin 3) :
    Continuous (fun y => fderiv ℝ (fun z => magneticReaction e k z y i j) x) :=
  differential_source_continuous _ x (fun a => magnetic_partial_source_continuous e k x a i j)

theorem K_differential_bound (k : ℝ) (x : Space) (i j : Fin 3) :
    ‖fderiv ℝ (fun z => K k z i j) x‖ ≤ entryBound k*|k| := by
  have hd := moment_hasFDerivAt _ (transverse_continuous i j) 2 (transverse_bound i j) k x
  have hh := (hd.const_mul ((k^3/(16*Real.pi^2) : ℝ) : ℂ)).fderiv
  change fderiv ℝ (fun z => K k z i j) x = _ at hh
  rw [hh]
  calc
    _ ≤ ‖((k^3/(16*Real.pi^2) : ℝ) : ℂ)‖*‖fderiv ℝ (moment (transverse i j) k) x‖ := by
      rw [hd.fderiv]
      exact ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖((k^3/(16*Real.pi^2) : ℝ) : ℂ)‖*((2*|k|)*surfaceMass) :=
      mul_le_mul_of_nonneg_left (FiniteSphereIncident.moment_derivative_bound _ (transverse_continuous i j) 2
        (transverse_bound i j) k x) (norm_nonneg _)
    _ = _ := by rw [Complex.norm_real,Real.norm_eq_abs]; unfold entryBound; ring

private theorem K_partial_bound (k : ℝ) (x : Space) (a i j : Fin 3) :
    ‖dcoord (fun z => K k z i j) x a‖ ≤ entryBound k*|k| := by
  unfold dcoord
  have hb : ‖basis a‖=1 := by simp [basis]
  exact ((fderiv ℝ (fun z => K k z i j) x).le_opNorm (basis a)).trans
    ((mul_le_mul_of_nonneg_right (K_differential_bound k x i j) (norm_nonneg _)).trans_eq (by rw [hb,mul_one]))

theorem magnetic_partial_bound (e : Bool) (k : ℝ) (x y : Space) (a i j : Fin 3) :
    ‖dcoord (fun z => magneticReaction e k z y i j) x a‖ ≤ entryBound k*|k| := by
  rw [SphereParityMaxwell.magnetic_partial,norm_mul]
  have hc : ‖Complex.I/2‖=(1/2 : ℝ) := by norm_num [norm_div]
  have hs : ‖(if e then -1 else 1 : ℂ)*(sign i : ℂ)*(sign a : ℂ)‖=1 := by
    cases e <;> unfold sign <;> split_ifs <;> norm_num
  rw [hc]
  have ht := norm_sub_le (dcoord (fun z => K k z i j) (x-y) a)
    ((if e then -1 else 1 : ℂ)*(sign i : ℂ)*(sign a : ℂ)*dcoord (fun z => K k z i j) (reflect x-y) a)
  rw [norm_mul,hs,one_mul] at ht
  nlinarith [K_partial_bound k (x-y) a i j,K_partial_bound k (reflect x-y) a i j]

theorem magnetic_differential_bound (e : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    ‖fderiv ℝ (fun z => magneticReaction e k z y i j) x‖ ≤ 3*entryBound k*|k| := by
  have hE := entryBound_nonnegative k
  have hD : 0 ≤ entryBound k*|k| := mul_nonneg (entryBound_nonnegative k) (abs_nonneg k)
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  rw [clm_basis_expansion]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ a : Fin 3, ‖v‖*(entryBound k*|k|) := Finset.sum_le_sum (fun a _ => by
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le v a) (magnetic_partial_bound e k x y a i j) (norm_nonneg _) (norm_nonneg _))
    _ = _ := by rw [Fin.sum_univ_three]; ring

end OQ14.SphereParityDifferential
#print axioms OQ14.SphereParityDifferential.J_partial_continuous
#print axioms OQ14.SphereParityDifferential.K_partial_continuous
#print axioms OQ14.SphereParityDifferential.electric_partial_source_continuous
#print axioms OQ14.SphereParityDifferential.magnetic_partial_source_continuous
#print axioms OQ14.SphereParityDifferential.clm_basis_expansion
#print axioms OQ14.SphereParityDifferential.electric_differential_source_continuous
#print axioms OQ14.SphereParityDifferential.magnetic_differential_source_continuous
#print axioms OQ14.SphereParityDifferential.K_differential_bound
#print axioms OQ14.SphereParityDifferential.magnetic_partial_bound
#print axioms OQ14.SphereParityDifferential.magnetic_differential_bound
