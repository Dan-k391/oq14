import FiniteDimensionalDeterminant
import Mathlib.Analysis.Meromorphic.Order

/-! # Actual meromorphic inverses in finite dimensions

The adjugate is reconstructed as a continuous linear endomorphism. Its
analyticity is derived from finite determinants of updated matrix rows.
The actual total inverse is the adjugate divided by the actual determinant.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.FiniteMeromorphicInverse

open Filter OQ14.FiniteDimensionalDeterminant
open scoped Topology

local instance {ι : Type*} [Fintype ι] : NormedAddCommGroup (Matrix ι ι ℂ) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → ℂ))

local instance {ι : Type*} [Fintype ι] : NormedSpace ℂ (Matrix ι ι ℂ) :=
  inferInstanceAs (NormedSpace ℂ (ι → ι → ℂ))

section Matrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_determinant_analyticAt (M : ℂ → Matrix ι ι ℂ) (z : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) :
    AnalyticAt ℂ (fun w => (M w).det) z := by
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_prod
  intro i _
  exact hM (σ i) i

theorem matrix_adjugate_analyticAt (M : ℂ → Matrix ι ι ℂ) (z : ℂ)
    (hM : ∀ i j, AnalyticAt ℂ (fun w => M w i j) z) :
    AnalyticAt ℂ (fun w => (M w).adjugate) z := by
  apply AnalyticAt.pi
  intro i
  apply AnalyticAt.pi
  intro j
  simp_rw [Matrix.adjugate_apply]
  apply matrix_determinant_analyticAt (fun w => (M w).updateRow j (Pi.single i (1 : ℂ))) z
  intro p q
  by_cases hp : p = j
  · subst p
    simpa only [Matrix.updateRow_self] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (Pi.single i (1 : ℂ) : ι → ℂ) q) z)
  · simpa only [Matrix.updateRow_ne hp] using hM p q

end Matrices

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

abbrev Index (V : Type*) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] :=
  Fin (Module.finrank ℂ V)

def matrixEquiv : (V →L[ℂ] V) ≃ₐ[ℂ] Matrix (Index V) (Index V) ℂ :=
  (Module.End.toContinuousLinearMap V).symm.trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V))

def fromMatrix : Matrix (Index V) (Index V) ℂ →L[ℂ] (V →L[ℂ] V) :=
  (matrixEquiv.symm.toLinearEquiv.toContinuousLinearEquiv).toContinuousLinearMap

def adjugate (A : V →L[ℂ] V) : V →L[ℂ] V :=
  fromMatrix ((matrixEquiv A).adjugate)

theorem matrixEquiv_apply (A : V →L[ℂ] V) :
    matrixEquiv A = LinearMap.toMatrix (Module.finBasis ℂ V)
      (Module.finBasis ℂ V) A.toLinearMap := rfl

theorem matrixEquiv_determinant (A : V →L[ℂ] V) :
    (matrixEquiv A).det = determinant A := by
  rw [matrixEquiv_apply, LinearMap.det_toMatrix]
  rfl

theorem matrixEquiv_inverse (A : V →L[ℂ] V) :
    matrixEquiv (Ring.inverse A) = (matrixEquiv A)⁻¹ := by
  classical
  rw [Matrix.nonsing_inv_eq_ringInverse]
  by_cases hA : IsUnit A
  · have hM : IsUnit (matrixEquiv A) :=
      (MulEquiv.isUnit_map matrixEquiv).mpr hA
    have hleft : matrixEquiv (Ring.inverse A)*matrixEquiv A = 1 := by
      rw [← map_mul, Ring.inverse_mul_cancel A hA, map_one]
    calc
      matrixEquiv (Ring.inverse A) = matrixEquiv (Ring.inverse A)*1 := by rw [mul_one]
      _ = matrixEquiv (Ring.inverse A)*(matrixEquiv A*Ring.inverse (matrixEquiv A)) := by
        rw [Ring.mul_inverse_cancel _ hM]
      _ = Ring.inverse (matrixEquiv A) := by rw [← mul_assoc, hleft, one_mul]
  · have hM : ¬IsUnit (matrixEquiv A) := by
      simpa only [MulEquiv.isUnit_map] using hA
    rw [Ring.inverse_non_unit _ hA, map_zero, Ring.inverse_non_unit _ hM]

theorem inverse_adjugate (A : V →L[ℂ] V) :
    Ring.inverse A = (determinant A)⁻¹ • adjugate A := by
  classical
  apply matrixEquiv.injective
  rw [matrixEquiv_inverse, Matrix.inv_def, Ring.inverse_eq_inv,
    map_smul, ← matrixEquiv_determinant]
  change _ = (matrixEquiv A).det⁻¹ • matrixEquiv (matrixEquiv.symm ((matrixEquiv A).adjugate))
  rw [AlgEquiv.apply_symm_apply]

theorem adjugate_analyticAt (A : ℂ → V →L[ℂ] V) (z : ℂ)
    (hA : AnalyticAt ℂ A z) : AnalyticAt ℂ (fun w => adjugate (A w)) z := by
  classical
  have hm : ∀ i j, AnalyticAt ℂ (fun w => matrixEquiv (A w) i j) z := by
    intro i j
    simpa only [matrixEquiv_apply, LinearMap.toMatrix_apply] using
      coordinate_analyticAt (Module.finBasis ℂ V) A z hA i j
  exact ((fromMatrix (V := V)).analyticAt _).comp (matrix_adjugate_analyticAt _ z hm)

/-- The actual inverse is meromorphic even if the determinant vanishes
identically: in that case total inversion is zero locally. -/
theorem inverse_meromorphicAt (A : ℂ → V →L[ℂ] V) (z : ℂ)
    (hA : AnalyticAt ℂ A z) : MeromorphicAt (fun w => Ring.inverse (A w)) z := by
  have hd := (determinant_analyticAt A z hA).meromorphicAt.inv
  have hn := (adjugate_analyticAt A z hA).meromorphicAt
  simpa only [inverse_adjugate] using hd.smul hn

theorem inverse_meromorphicOn (A : ℂ → V →L[ℂ] V) (U : Set ℂ)
    (hA : AnalyticOnNhd ℂ A U) : MeromorphicOn (fun w => Ring.inverse (A w)) U := by
  intro z hz
  exact inverse_meromorphicAt A z (hA z hz)

theorem inverse_analyticAt (A : ℂ → V →L[ℂ] V) (z : ℂ)
    (hA : AnalyticAt ℂ A z) (hu : IsUnit (A z)) :
    AnalyticAt ℂ (fun w => Ring.inverse (A w)) z := by
  have hd := (determinant_analyticAt A z hA).inv
    ((isUnit_iff_determinant_ne_zero (A z)).mp hu)
  have ht := hd.smul (adjugate_analyticAt A z hA)
  simpa only [inverse_adjugate] using ht

theorem local_unit_dichotomy (A : ℂ → V →L[ℂ] V) (z : ℂ)
    (hA : AnalyticAt ℂ A z) :
    (∀ᶠ w in 𝓝 z, ¬IsUnit (A w)) ∨ ∀ᶠ w in 𝓝[≠] z, IsUnit (A w) := by
  rcases (determinant_analyticAt A z hA).eventually_eq_zero_or_eventually_ne_zero
    with hzero | hnonzero
  · left
    filter_upwards [hzero] with w hw
    rw [isUnit_iff_determinant_ne_zero, hw]
    simp
  · right
    exact hnonzero.mono (fun w hw => (isUnit_iff_determinant_ne_zero (A w)).mpr hw)

/-- One actual invertible value on a connected analytic domain excludes
the identically singular alternative at every point of that domain. -/
theorem punctured_isUnit_of_basepoint (A : ℂ → V →L[ℂ] V) (U : Set ℂ)
    (hA : AnalyticOnNhd ℂ A U) (hU : IsPreconnected U)
    (zbase : ℂ) (hbase : zbase ∈ U) (hu : IsUnit (A zbase))
    (z : ℂ) (hz : z ∈ U) : ∀ᶠ w in 𝓝[≠] z, IsUnit (A w) := by
  have hd : AnalyticOnNhd ℂ (fun w => determinant (A w)) U :=
    fun w hw => determinant_analyticAt A w (hA w hw)
  rcases (hd z hz).eventually_eq_zero_or_eventually_ne_zero with hzero | hnonzero
  · have he : (fun w => determinant (A w)) =ᶠ[𝓝 z] 0 := by
      simpa only [Pi.zero_apply] using hzero
    have hall := hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz he
    exact False.elim (((isUnit_iff_determinant_ne_zero (A zbase)).mp hu) (hall hbase))
  · exact hnonzero.mono (fun w hw => (isUnit_iff_determinant_ne_zero (A w)).mpr hw)

theorem inverse_order_negative (A : ℂ → V →L[ℂ] V) (z : ℂ)
    (hA : AnalyticAt ℂ A z) (hu : ∀ᶠ w in 𝓝[≠] z, IsUnit (A w))
    (hnot : ¬IsUnit (A z)) : (inverse_meromorphicAt A z hA).order < 0 := by
  by_contra hnegative
  obtain ⟨C,hC⟩ := (inverse_meromorphicAt A z hA).tendsto_nhds_of_order_nonneg
    (le_of_not_gt hnegative)
  have hAt := hA.continuousAt.tendsto.mono_left
    (show 𝓝[≠] z ≤ 𝓝 z from nhdsWithin_le_nhds)
  have hleft : A z*C = 1 := by
    have ht : Tendsto (fun w => A w*Ring.inverse (A w)) (𝓝[≠] z) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hu] with w hw
      exact (Ring.mul_inverse_cancel (A w) hw).symm
    exact tendsto_nhds_unique (hAt.mul hC) ht
  have hright : C*A z = 1 := by
    have ht : Tendsto (fun w => Ring.inverse (A w)*A w) (𝓝[≠] z) (𝓝 1) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [hu] with w hw
      exact (Ring.inverse_mul_cancel (A w) hw).symm
    exact tendsto_nhds_unique (hC.mul hAt) ht
  exact hnot ⟨⟨A z,C,hleft,hright⟩,rfl⟩

theorem inverse_order_negative_of_basepoint (A : ℂ → V →L[ℂ] V) (U : Set ℂ)
    (hA : AnalyticOnNhd ℂ A U) (hU : IsPreconnected U)
    (zbase : ℂ) (hbase : zbase ∈ U) (hu : IsUnit (A zbase))
    (z : ℂ) (hz : z ∈ U) (hnot : ¬IsUnit (A z)) :
    (inverse_meromorphicAt A z (hA z hz)).order < 0 :=
  inverse_order_negative A z (hA z hz)
    (punctured_isUnit_of_basepoint A U hA hU zbase hbase hu z hz) hnot

end OQ14.FiniteMeromorphicInverse

#print axioms OQ14.FiniteMeromorphicInverse.matrix_determinant_analyticAt
#print axioms OQ14.FiniteMeromorphicInverse.matrix_adjugate_analyticAt
#print axioms OQ14.FiniteMeromorphicInverse.matrixEquiv_apply
#print axioms OQ14.FiniteMeromorphicInverse.matrixEquiv_determinant
#print axioms OQ14.FiniteMeromorphicInverse.matrixEquiv_inverse
#print axioms OQ14.FiniteMeromorphicInverse.inverse_adjugate
#print axioms OQ14.FiniteMeromorphicInverse.adjugate_analyticAt
#print axioms OQ14.FiniteMeromorphicInverse.inverse_meromorphicAt
#print axioms OQ14.FiniteMeromorphicInverse.inverse_meromorphicOn
#print axioms OQ14.FiniteMeromorphicInverse.inverse_analyticAt
#print axioms OQ14.FiniteMeromorphicInverse.local_unit_dichotomy
#print axioms OQ14.FiniteMeromorphicInverse.punctured_isUnit_of_basepoint
#print axioms OQ14.FiniteMeromorphicInverse.inverse_order_negative
#print axioms OQ14.FiniteMeromorphicInverse.inverse_order_negative_of_basepoint
