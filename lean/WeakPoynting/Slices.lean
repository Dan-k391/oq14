import WeakPoynting.Conservation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Actual plane slices of an integrable divergence-free flux

The vertical coordinate is x₂ and the transverse coordinates are x₀,x₁.
All slices below are genuine two-dimensional Lebesgue integrals. Coordinate
volume preservation and the tensor-test derivative calculation are proved.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace OQ14.FluxSlices

open MeasureTheory OQ14.Maxwell OQ14.WeakConservation
open scoped Topology ComplexConjugate

abbrev Plane := Fin 2 → ℝ

def split : Space ≃ᵐ ℝ × Plane :=
  (EuclideanSpace.measurableEquiv (Fin 3)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)

def axis : Space →L[ℝ] ℝ := EuclideanSpace.proj 2

def transverse : Space →L[ℝ] Plane :=
  ContinuousLinearMap.pi (fun j => EuclideanSpace.proj ((2 : Fin 3).succAbove j))

theorem split_apply (x : Space) : split x = (axis x, transverse x) := rfl

def splitHomeomorph : Space ≃ₜ ℝ × Plane where
  toEquiv := split.toEquiv
  continuous_toFun := axis.continuous.prodMk transverse.continuous
  continuous_invFun := by
    change Continuous (fun p : ℝ × Plane => (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ((2 : Fin 3).insertNth p.1 p.2))
    exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
      (Continuous.finInsertNth (π := fun _ : Fin 3 => ℝ) 2 continuous_fst continuous_snd)

theorem split_measurePreserving : MeasurePreserving split :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3))

theorem join_coordinates (z : ℝ) (q : Plane) :
    (fun j => split.symm (z, q) j) = ![q 0, q 1, z] := by
  funext j
  fin_cases j <;> rfl

theorem coordinate_Fubini (f : Space → ℝ) (hf : Integrable f) :
    (∫ x, f x) = ∫ z, ∫ q : Plane, f (split.symm (z, q)) := by
  have hi : Integrable (fun p : ℝ × Plane => f (split.symm p)) :=
    ((MeasurePreserving.symm split split_measurePreserving).integrable_comp_emb
      split.symm.measurableEmbedding).mpr hf
  exact ((MeasurePreserving.symm split split_measurePreserving).integral_comp' f).symm.trans
    (integral_prod _ hi)

theorem slice_integrable (f : Space → ℝ) (hf : Integrable f) :
    Integrable (fun z : ℝ => ∫ q : Plane, f (split.symm (z, q))) := by
  have hi : Integrable (fun p : ℝ × Plane => f (split.symm p)) :=
    ((MeasurePreserving.symm split split_measurePreserving).integrable_comp_emb
      split.symm.measurableEmbedding).mpr hf
  exact hi.integral_prod_left

structure PlaneTest where
  function : Plane → ℝ
  regular : ContDiff ℝ 1 function
  compact : HasCompactSupport function

structure LineTest (I : Set ℝ) where
  function : ℝ → ℝ
  regular : ContDiff ℝ 1 function
  compact : HasCompactSupport function
  inside : tsupport function ⊆ I

def tensorFunction {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) (x : Space) : ℝ :=
  θ.function (axis x) * ψ.function (transverse x)

theorem tensor_regular {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) :
    ContDiff ℝ 1 (tensorFunction ψ θ) :=
  (θ.regular.comp axis.contDiff).mul (ψ.regular.comp transverse.contDiff)

theorem tensor_compact {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) :
    HasCompactSupport (tensorFunction ψ θ) := by
  have hc : HasCompactSupport (fun p : ℝ × Plane => θ.function p.1 * ψ.function p.2) := by
    apply HasCompactSupport.of_support_subset_isCompact (θ.compact.prod ψ.compact)
    intro p hp
    have hh := mul_ne_zero_iff.mp hp
    exact ⟨subset_tsupport _ hh.1, subset_tsupport _ hh.2⟩
  exact hc.comp_homeomorph splitHomeomorph

theorem tensor_inside {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) :
    tsupport (tensorFunction ψ θ) ⊆ axis ⁻¹' I := by
  have hs : tsupport (tensorFunction ψ θ) ⊆ axis ⁻¹' tsupport θ.function := by
    apply closure_minimal _ (isClosed_closure.preimage axis.continuous)
    intro x hx
    exact subset_tsupport _ (mul_ne_zero_iff.mp hx).1
  exact hs.trans (Set.preimage_mono θ.inside)

def tensorTest {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) : RealTest (axis ⁻¹' I) where
  function := tensorFunction ψ θ
  regular := tensor_regular ψ θ
  compact := tensor_compact ψ θ
  inside := tensor_inside ψ θ

theorem tensor_transverse_support {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) :
    tsupport (tensorFunction ψ θ) ⊆ transverse ⁻¹' tsupport ψ.function := by
  apply closure_minimal _ (isClosed_closure.preimage transverse.continuous)
  intro x hx
  exact subset_tsupport _ (mul_ne_zero_iff.mp hx).2

def tensorTestOn {I : Set ℝ} {Ω : Set Space} (ψ : PlaneTest) (θ : LineTest I)
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω) : RealTest Ω where
  function := tensorFunction ψ θ
  regular := tensor_regular ψ θ
  compact := tensor_compact ψ θ
  inside := fun _ hx => hbox ⟨tensor_inside ψ θ hx, tensor_transverse_support ψ θ hx⟩

theorem tensor_partial {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I)
    (x : Space) (j : Fin 3) :
    fderiv ℝ (tensorFunction ψ θ) x (basis j) =
      deriv θ.function (axis x) * axis (basis j) * ψ.function (transverse x) +
      θ.function (axis x) * fderiv ℝ ψ.function (transverse x) (transverse (basis j)) := by
  have hθ := (θ.regular.differentiable (by norm_num) (axis x)).hasDerivAt.comp_hasFDerivAt x
    axis.hasFDerivAt
  have hψ := (ψ.regular.differentiable (by norm_num) (transverse x)).hasFDerivAt.comp x
    transverse.hasFDerivAt
  have h := congrArg (fun L : Space →L[ℝ] ℝ => L (basis j)) (hθ.mul hψ).fderiv
  simpa [tensorFunction, Function.comp_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc,
    add_comm] using h

def planePartial (ψ : PlaneTest) (j : Fin 2) (q : Plane) : ℝ :=
  fderiv ℝ ψ.function q (Pi.single j 1)

theorem planePartial_continuous (ψ : PlaneTest) (j : Fin 2) :
    Continuous (planePartial ψ j) :=
  (ψ.regular.continuous_fderiv le_rfl).clm_apply continuous_const

theorem planePartial_compact (ψ : PlaneTest) (j : Fin 2) :
    HasCompactSupport (planePartial ψ j) := ψ.compact.fderiv_apply ℝ _

theorem axis_join (z : ℝ) (q : Plane) : axis (split.symm (z, q)) = z := by
  exact congrArg Prod.fst (split.apply_symm_apply (z, q))

theorem transverse_join (z : ℝ) (q : Plane) : transverse (split.symm (z, q)) = q := by
  exact congrArg Prod.snd (split.apply_symm_apply (z, q))

theorem transverse_basis_zero : transverse (basis 0) = Pi.single 0 1 := by
  ext j
  fin_cases j <;> simp [transverse, basis, EuclideanSpace.single_apply]
  all_goals decide

theorem transverse_basis_one : transverse (basis 1) = Pi.single 1 1 := by
  ext j
  fin_cases j <;> simp [transverse, basis, EuclideanSpace.single_apply]
  all_goals decide

theorem transverse_basis_two : transverse (basis 2) = 0 := by
  ext j
  fin_cases j <;> simp [transverse, basis, EuclideanSpace.single_apply]

theorem tensor_partial_zero {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) (x : Space) :
    fderiv ℝ (tensorFunction ψ θ) x (basis 0) =
      θ.function (axis x) * planePartial ψ 0 (transverse x) := by
  rw [tensor_partial, transverse_basis_zero]
  simp [axis, basis, EuclideanSpace.single_apply, planePartial]

theorem tensor_partial_one {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) (x : Space) :
    fderiv ℝ (tensorFunction ψ θ) x (basis 1) =
      θ.function (axis x) * planePartial ψ 1 (transverse x) := by
  rw [tensor_partial, transverse_basis_one]
  simp [axis, basis, EuclideanSpace.single_apply, planePartial]

theorem tensor_partial_two {I : Set ℝ} (ψ : PlaneTest) (θ : LineTest I) (x : Space) :
    fderiv ℝ (tensorFunction ψ θ) x (basis 2) =
      deriv θ.function (axis x) * ψ.function (transverse x) := by
  rw [tensor_partial, transverse_basis_two]
  simp [axis, basis, EuclideanSpace.single_apply]

theorem axis_weight_integrable (f : Space → ℝ) (hf : Integrable f)
    (θ : ℝ → ℝ) (hθ : Continuous θ) (hcθ : HasCompactSupport θ) :
    Integrable (fun x => θ (axis x) * f x) := by
  obtain ⟨C, hC⟩ := hθ.bounded_above_of_compact_support hcθ
  exact hf.bdd_mul (hθ.comp axis.continuous).aestronglyMeasurable
    ⟨C, fun x => hC (axis x)⟩

theorem transverse_weight_integrable (f : Space → ℝ) (hf : Integrable f)
    (ψ : Plane → ℝ) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => ψ (transverse x) * f x) := by
  obtain ⟨C, hC⟩ := hψ.bounded_above_of_compact_support hcψ
  exact hf.bdd_mul (hψ.comp transverse.continuous).aestronglyMeasurable
    ⟨C, fun x => hC (transverse x)⟩

theorem weighted_coordinate_Fubini (f : Space → ℝ) (hf : Integrable f)
    (θ : ℝ → ℝ) (hθ : Continuous θ) (hcθ : HasCompactSupport θ) :
    (∫ x, θ (axis x) * f x) =
      ∫ z, θ z * (∫ q : Plane, f (split.symm (z, q))) := by
  rw [coordinate_Fubini _ (axis_weight_integrable f hf θ hθ hcθ)]
  simp_rw [axis_join, integral_const_mul]

abbrev RealFlux := Space → Fin 3 → ℝ

def verticalDensity (ψ : PlaneTest) (P : RealFlux) (x : Space) : ℝ :=
  ψ.function (transverse x) * P x 2

def transverseDensity (ψ : PlaneTest) (P : RealFlux) (x : Space) : ℝ :=
  planePartial ψ 0 (transverse x) * P x 0 +
  planePartial ψ 1 (transverse x) * P x 1

def fluxSlice (ψ : PlaneTest) (P : RealFlux) (z : ℝ) : ℝ :=
  ∫ q : Plane, verticalDensity ψ P (split.symm (z, q))

def derivativeSlice (ψ : PlaneTest) (P : RealFlux) (z : ℝ) : ℝ :=
  ∫ q : Plane, transverseDensity ψ P (split.symm (z, q))

theorem verticalDensity_integrable (ψ : PlaneTest) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (verticalDensity ψ P) :=
  transverse_weight_integrable _ (hP 2) ψ.function ψ.regular.continuous ψ.compact

theorem transverseDensity_integrable (ψ : PlaneTest) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (transverseDensity ψ P) :=
  (transverse_weight_integrable _ (hP 0) _ (planePartial_continuous ψ 0)
    (planePartial_compact ψ 0)).add
  (transverse_weight_integrable _ (hP 1) _ (planePartial_continuous ψ 1)
    (planePartial_compact ψ 1))

theorem fluxSlice_integrable (ψ : PlaneTest) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (fluxSlice ψ P) :=
  slice_integrable _ (verticalDensity_integrable ψ P hP)

theorem derivativeSlice_integrable (ψ : PlaneTest) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j)) : Integrable (derivativeSlice ψ P) :=
  slice_integrable _ (transverseDensity_integrable ψ P hP)

/-- Actual distributional zero divergence on Ω, tested with real compact C1 scalars. -/
def HasZeroDistributionalDivergence (Ω : Set Space) (P : RealFlux) : Prop :=
  ∀ χ : RealTest Ω,
    (∫ x, fderiv ℝ χ.function x (basis 0) * P x 0 +
      fderiv ℝ χ.function x (basis 1) * P x 1 +
      fderiv ℝ χ.function x (basis 2) * P x 2) = 0

/-- A literal distributional derivative relation, not an assumed representative. -/
def HasWeakDerivativeOn (I : Set ℝ) (F G : ℝ → ℝ) : Prop :=
  ∀ θ : LineTest I, (∫ z, deriv θ.function z * F z + θ.function z * G z) = 0

/-- Three-dimensional weak zero divergence implies the actual one-dimensional
weak derivative formula for the plane-integrated flux, with the transverse term. -/
theorem fluxSlice_weak_derivative {I : Set ℝ} {Ω : Set Space} (ψ : PlaneTest) (P : RealFlux)
    (hP : ∀ j, Integrable (fun x => P x j))
    (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (hdiv : HasZeroDistributionalDivergence Ω P) :
    HasWeakDerivativeOn I (fluxSlice ψ P) (derivativeSlice ψ P) := by
  intro θ
  have hh := hdiv (tensorTestOn ψ θ hbox)
  have hθd : Continuous (deriv θ.function) := θ.regular.continuous_deriv le_rfl
  have hcθd : HasCompactSupport (deriv θ.function) := θ.compact.deriv
  have hv := verticalDensity_integrable ψ P hP
  have ht := transverseDensity_integrable ψ P hP
  have heq : (fun x => fderiv ℝ (tensorTestOn ψ θ hbox).function x (basis 0) * P x 0 +
      fderiv ℝ (tensorTestOn ψ θ hbox).function x (basis 1) * P x 1 +
      fderiv ℝ (tensorTestOn ψ θ hbox).function x (basis 2) * P x 2) =
      (fun x => deriv θ.function (axis x) * verticalDensity ψ P x +
        θ.function (axis x) * transverseDensity ψ P x) := by
    funext x
    dsimp only [tensorTestOn]
    rw [tensor_partial_zero, tensor_partial_one, tensor_partial_two]
    dsimp only [verticalDensity, transverseDensity]
    ring
  rw [heq, integral_add (axis_weight_integrable _ hv _ hθd hcθd)
    (axis_weight_integrable _ ht _ θ.regular.continuous θ.compact),
    weighted_coordinate_Fubini _ hv _ hθd hcθd,
    weighted_coordinate_Fubini _ ht _ θ.regular.continuous θ.compact] at hh
  have hf : Integrable (fun z => deriv θ.function z * fluxSlice ψ P z) :=
    (fluxSlice_integrable ψ P hP).bdd_mul hθd.aestronglyMeasurable
      (hθd.bounded_above_of_compact_support hcθd)
  have hg : Integrable (fun z => θ.function z * derivativeSlice ψ P z) :=
    (derivativeSlice_integrable ψ P hP).bdd_mul θ.regular.continuous.aestronglyMeasurable
      (θ.regular.continuous.bounded_above_of_compact_support θ.compact)
  rw [integral_add hf hg]
  exact hh

def zeroExtendedPower (Ω : Set Space) (E H : DomainCurl.HCurl Ω) : RealFlux :=
  fun x j => Ω.indicator
    (fun y => realPower (fun z i => E.val.1 i z) (fun z i => H.val.1 i z) y j) x

theorem conjugate_product_integrable (u v : WeakCurl.L2Scalar) :
    Integrable (fun x => u x * conj (v x)) := by
  apply (WeakGreen.scalarProduct_integrable u (WeakPower.conjScalar v)).congr
  filter_upwards [WeakPower.conjScalar_ae v] with x hx
  rw [hx]

theorem L2_realPower_integrable (E H : WeakCurl.L2Vector) (j : Fin 3) :
    Integrable (fun x => realPower (fun y i => E i y) (fun y i => H i y) x j) := by
  have h (i l : Fin 3) := conjugate_product_integrable (E i) (H l)
  fin_cases j
  · simpa only [realPower, cross_apply, conjugate, Matrix.cons_val_zero] using
      (((h 1 2).sub (h 2 1)).re.div_const 2)
  · simpa only [realPower, cross_apply, conjugate, Matrix.cons_val_one] using
      (((h 2 0).sub (h 0 2)).re.div_const 2)
  · simpa only [realPower, cross_apply, conjugate, Matrix.cons_val_two] using
      (((h 0 1).sub (h 1 0)).re.div_const 2)

theorem extended_power_ae {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (E H : DomainCurl.HCurl Ω) (j : Fin 3) :
    (fun x => realPower
      (fun y i => CurlCutoff.extendVector Ω hΩ E.val.1 i y)
      (fun y i => CurlCutoff.extendVector Ω hΩ H.val.1 i y) x j) =ᵐ[volume]
    (fun x => zeroExtendedPower Ω E H x j) := by
  have he := ae_all_iff.mpr (fun i => CurlCutoff.extendScalar_ae Ω hΩ (E.val.1 i))
  have hh := ae_all_iff.mpr (fun i => CurlCutoff.extendScalar_ae Ω hΩ (H.val.1 i))
  filter_upwards [he, hh] with x he hh
  by_cases hx : x ∈ Ω
  · simp only [Set.indicator_of_mem hx] at he hh
    simp only [zeroExtendedPower, Set.indicator_of_mem hx, realPower, CurlCutoff.extendVector,
      he, hh]
  · simp only [Set.indicator_of_not_mem hx] at he hh
    simp [zeroExtendedPower, Set.indicator_of_not_mem hx, realPower, CurlCutoff.extendVector,
      he, hh, conjugate, cross_apply]
    fin_cases j <;> rfl

theorem zeroExtendedPower_integrable {Ω : Set Space} (hΩ : MeasurableSet Ω)
    (E H : DomainCurl.HCurl Ω) (j : Fin 3) :
    Integrable (fun x => zeroExtendedPower Ω E H x j) :=
  (L2_realPower_integrable (CurlCutoff.extendVector Ω hΩ E.val.1)
    (CurlCutoff.extendVector Ω hΩ H.val.1) j).congr (extended_power_ae hΩ E H j)

/-- The actual regional weak Maxwell theorem supplies the distributional
divergence premise used in the slicing theorem after zero extension of the flux. -/
theorem maxwell_zeroExtendedPower_divergence {Ω : Set Space} (hΩ : IsOpen Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    HasZeroDistributionalDivergence Ω (zeroExtendedPower Ω E H) := by
  intro χ
  have heq : (fun x => fderiv ℝ χ.function x (basis 0) * zeroExtendedPower Ω E H x 0 +
      fderiv ℝ χ.function x (basis 1) * zeroExtendedPower Ω E H x 1 +
      fderiv ℝ χ.function x (basis 2) * zeroExtendedPower Ω E H x 2) =
      Ω.indicator (testPower χ (fun y j => E.val.1 j y) (fun y j => H.val.1 j y)) := by
    funext x
    by_cases hx : x ∈ Ω <;> simp [zeroExtendedPower, testPower, hx]
  rw [heq, integral_indicator hΩ.measurableSet]
  exact weak_real_power_conservation hΩ χ ω μ ε E H hM

/-- Actual weak Maxwell fields have integrable plane flux and its weak axial
derivative, for every compact transverse aperture whose axial collar lies in Ω. -/
theorem maxwell_flux_slices {Ω : Set Space} {I : Set ℝ} (hΩ : IsOpen Ω)
    (ψ : PlaneTest) (hbox : axis ⁻¹' I ∩ transverse ⁻¹' tsupport ψ.function ⊆ Ω)
    (ω : ℝ) (μ ε : Space → ℝ) (E H : DomainCurl.HCurl Ω)
    (hM : WeakMaxwell ω μ ε E H) :
    Integrable (fluxSlice ψ (zeroExtendedPower Ω E H)) ∧
    Integrable (derivativeSlice ψ (zeroExtendedPower Ω E H)) ∧
    HasWeakDerivativeOn I (fluxSlice ψ (zeroExtendedPower Ω E H))
      (derivativeSlice ψ (zeroExtendedPower Ω E H)) := by
  have hi := zeroExtendedPower_integrable hΩ.measurableSet E H
  exact ⟨fluxSlice_integrable ψ _ hi, derivativeSlice_integrable ψ _ hi,
    fluxSlice_weak_derivative ψ _ hi hbox (maxwell_zeroExtendedPower_divergence hΩ ω μ ε E H hM)⟩

end OQ14.FluxSlices

#print axioms OQ14.FluxSlices.split_measurePreserving
#print axioms OQ14.FluxSlices.join_coordinates
#print axioms OQ14.FluxSlices.coordinate_Fubini
#print axioms OQ14.FluxSlices.slice_integrable
#print axioms OQ14.FluxSlices.tensor_regular
#print axioms OQ14.FluxSlices.tensor_compact
#print axioms OQ14.FluxSlices.tensor_inside
#print axioms OQ14.FluxSlices.tensor_partial
#print axioms OQ14.FluxSlices.weighted_coordinate_Fubini
#print axioms OQ14.FluxSlices.fluxSlice_integrable
#print axioms OQ14.FluxSlices.derivativeSlice_integrable
#print axioms OQ14.FluxSlices.fluxSlice_weak_derivative
#print axioms OQ14.FluxSlices.L2_realPower_integrable
#print axioms OQ14.FluxSlices.zeroExtendedPower_integrable
#print axioms OQ14.FluxSlices.maxwell_zeroExtendedPower_divergence
#print axioms OQ14.FluxSlices.maxwell_flux_slices
