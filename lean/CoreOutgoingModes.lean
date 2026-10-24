import CoreWeakLinear
import OutgoingFreeDyadic
import OutgoingGeometricTail

/-! The vacuum outgoing modes as an explicit weak Maxwell family: the electric and magnetic mode fields of
degree `l` are the formulas `outE`, `outH` of the outgoing Hankel state; they are continuous off the origin
and satisfy the weak first and second Maxwell equations on every open set avoiding the origin. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.CoreOutgoingModes
open MeasureTheory Filter Set Metric Complex OQ14.Maxwell OQ14.SourceRemotePlaneBand OQ14.CoreWeakSeries
  OQ14.CoreWeakLinear OQ14.BackgroundModeMaxwell OQ14.HarmonicPolynomial OQ14.SphereHarmonicBasis
  OQ14.VectorHarmonicNormalization
open OQ14.ModalAlgebra (xi xiD)
open scoped Topology ComplexConjugate

/-! ### The vacuum data and the mode formulas -/

theorem vacuum_data (l : ℕ) :
    SourceCoreReaction.vacuum (VacuumOutgoingBounds.data l) = VacuumOutgoingBounds.data l := rfl

theorem sigma_data (l : ℕ) (r : ℝ) : SourceRadialSystem.sigma (VacuumOutgoingBounds.data l) r = 1 := by
  by_cases h : r ≤ 1
  · simp [SourceRadialSystem.sigma, SourceRadialSystem.extend, VacuumOutgoingBounds.data, h]
  · simp [SourceRadialSystem.sigma, SourceRadialSystem.extend, VacuumOutgoingBounds.data, h]

theorem electric_data (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) :
    SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) P x i = -Complex.I * outE l P x i :=
  vacE_eq (VacuumOutgoingBounds.data l) P x i

theorem magnetic_data (l : ℕ) (P : Poly) (x : Space) (i : Fin 3) :
    SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) P x i = -Complex.I * outH l P x i :=
  vacH_eq (VacuumOutgoingBounds.data l) P x i

theorem weakCurlPairing_eq (F : Field) (i : Fin 3) (f : DynamicSource.Test) :
    weakCurlPairing F f.val i = MagneticResponse.curlPair (MaterialMaxwell.fieldPair F) i f := by
  fin_cases i <;> simp [weakCurlPairing, MagneticResponse.curlPair, MaterialMaxwell.fieldPair,
    WeakCurl.next, WeakCurl.previous, DynamicSource.testPartial, GradientProjection.pderivative_apply]

theorem fieldPair_neg (F : Field) (i : Fin 3) (f : DynamicSource.Test) :
    MaterialMaxwell.fieldPair (fun x j => -F x j) i f = -MaterialMaxwell.fieldPair F i f := by
  have := fieldPair_const_mul (-1 : ℂ) F i f
  simpa using this

/-! ### The weak Maxwell equations of the outgoing modes -/

theorem weak_electric_data (l : ℕ) (P : Poly) (Ω : Set Space)
    (h0 : ∀ x ∈ Ω, x ≠ 0) :
    WeakOn Ω (SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) P)
      (SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) P) := by
  intro i f hf
  have h0' : (0 : Space) ∉ tsupport (f.val : Space → ℂ) := fun h => h0 0 (hf h) rfl
  have hw := congrFun (SourceUnclippedMaxwell.first_weak_maxwell (VacuumOutgoingBounds.data l)
    (by intro g hg; simp [VacuumOutgoingBounds.data] at hg) P f.val (f.val.smooth 2) f.property h0') i
  rw [← weakCurlPairing_eq, hw]
  unfold MaterialMaxwell.fieldPair
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem weak_magnetic_data (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l)
    (hh : formalLaplacian P = 0) (Ω : Set Space) (h0 : ∀ x ∈ Ω, x ≠ 0) :
    WeakOn Ω (SourceUnclippedMaxwell.magnetic (VacuumOutgoingBounds.data l) P)
      (fun x i => -SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) P x i) := by
  intro i f hf
  have h0' : (0 : Space) ∉ tsupport (f.val : Space → ℂ) := fun h => h0 0 (hf h) rfl
  have hw := congrFun (SourceUnclippedMaxwell.second_weak_maxwell (VacuumOutgoingBounds.data l) P hp hh
    f.val (f.val.smooth 1) f.property h0') i
  rw [← weakCurlPairing_eq, hw, fieldPair_neg]
  unfold MaterialMaxwell.fieldPair
  have hfun : (∫ x, -Complex.I * SourceRadialSystem.sigma (VacuumOutgoingBounds.data l) ‖x‖ *
      SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) P x i * (f.val : Space → ℂ) x) =
      ∫ x, (-Complex.I) * (SourceUnclippedMaxwell.electric (VacuumOutgoingBounds.data l) P x i *
        (f.val : Space → ℂ) x) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [sigma_data]
    ring
  rw [hfun, integral_const_mul]
  ring

theorem weak_out_tm (l : ℕ) (P : Poly) (Ω : Set Space) (h0 : ∀ x ∈ Ω, x ≠ 0) :
    WeakOn Ω (fun x i => outE l P x i) (fun x i => outH l P x i) :=
  weakOn_of_scaled (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero) _ _
    (fun x i => electric_data l P x i) (fun x i => magnetic_data l P x i)
    (weak_electric_data l P Ω h0)

theorem weak_out_te (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (hh : formalLaplacian P = 0)
    (Ω : Set Space) (h0 : ∀ x ∈ Ω, x ≠ 0) :
    WeakOn Ω (fun x i => outH l P x i) (fun x i => -outE l P x i) :=
  weakOn_of_scaled (-Complex.I) (neg_ne_zero.mpr Complex.I_ne_zero) _ _
    (fun x i => magnetic_data l P x i)
    (fun x i => by rw [electric_data]; ring)
    (weak_magnetic_data l P hp hh Ω h0)

/-! ### Continuity of the mode formulas off the origin -/

theorem continuousAt_xiD (l : ℕ) (z : ℂ) (hz : z ≠ 0) : ContinuousAt (xiD l) z := by
  have hp : ContinuousAt (OQ14.ModalAlgebra.p l) z :=
    (OQ14.ModalAlgebra.hankelPoly_hasDerivAt l Complex.I z hz).continuousAt
  have hpD : ContinuousAt (OQ14.ModalAlgebra.pD l) z :=
    (OQ14.ModalAlgebra.hankelPolyD_hasDerivAt l Complex.I z hz).continuousAt
  have he : ContinuousAt (fun w : ℂ => Complex.exp (Complex.I * w)) z :=
    (continuous_const.mul continuous_id).cexp.continuousAt
  unfold OQ14.ModalAlgebra.xiD
  exact (continuousAt_const.mul he).mul ((continuousAt_const.mul hp).add hpD)

theorem continuousAt_norm_cast (x : Space) : ContinuousAt (fun y : Space => (‖y‖ : ℂ)) x :=
  (Complex.continuous_ofReal.comp continuous_norm).continuousAt

theorem continuousAt_xi_norm (l : ℕ) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y : Space => xi l (‖y‖ : ℂ)) x := by
  have hz : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  exact ContinuousAt.comp (g := xi l) (f := fun y : Space => (‖y‖ : ℂ))
    (OQ14.ModalAlgebra.xi_hasDerivAt l (‖x‖ : ℂ) hz).continuousAt (continuousAt_norm_cast x)

theorem continuousAt_xiD_norm (l : ℕ) (x : Space) (hx : x ≠ 0) :
    ContinuousAt (fun y : Space => xiD l (‖y‖ : ℂ)) x := by
  have hz : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  exact ContinuousAt.comp (g := xiD l) (f := fun y : Space => (‖y‖ : ℂ))
    (continuousAt_xiD l (‖x‖ : ℂ) hz) (continuousAt_norm_cast x)

theorem continuous_coord (i : Fin 3) : Continuous (fun y : Space => ((y i : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

theorem continuous_dcoord_cE (P : Poly) (a : Fin 3) :
    Continuous (fun y : Space => dcoord (complexEvaluate P) y a) :=
  (contDiff_iff_contDiffAt.mpr fun _ =>
    ExteriorClassical.partial_smooth (complexEvaluate_regular P).contDiffAt a).continuous

theorem continuous_angularToroidal (P : Poly) (i : Fin 3) :
    Continuous (fun y : Space => DebyeRadialTrace.angularToroidal P y i) := by
  have hT (a b c d : Fin 3) : Continuous (fun y : Space =>
      dcoord (complexEvaluate P) y a * ((y b : ℝ) : ℂ) - dcoord (complexEvaluate P) y c * ((y d : ℝ) : ℂ)) :=
    ((continuous_dcoord_cE P a).mul (continuous_coord b)).sub
      ((continuous_dcoord_cE P c).mul (continuous_coord d))
  fin_cases i
  · exact hT 1 2 2 1
  · exact hT 2 0 0 2
  · exact hT 0 1 1 0

theorem continuousAt_outE (l : ℕ) (P : Poly) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    ContinuousAt (fun y => outE l P y i) x := by
  have hn0 : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  have hn := continuousAt_norm_cast x
  have hxi := continuousAt_xi_norm l x hx
  have hxiD := continuousAt_xiD_norm l x hx
  have hd : ContinuousAt (fun y : Space => dcoord (complexEvaluate P) y i) x :=
    (continuous_dcoord_cE P i).continuousAt
  have hc : ContinuousAt (fun y : Space => complexEvaluate P y) x :=
    (complexEvaluate_regular P).continuous.continuousAt
  have hy : ContinuousAt (fun y : Space => ((y i : ℝ) : ℂ)) x := (continuous_coord i).continuousAt
  unfold outE Eform
  exact ((hxiD.div (hn.pow l) (pow_ne_zero _ hn0)).mul hd).add
    ((((continuousAt_const.mul ((continuousAt_const.mul hxi).div (hn.pow _) (pow_ne_zero _ hn0))).sub
      ((continuousAt_const.mul hxiD).div (hn.pow _) (pow_ne_zero _ hn0))).mul hy).mul hc)

theorem continuousAt_outH (l : ℕ) (P : Poly) (x : Space) (hx : x ≠ 0) (i : Fin 3) :
    ContinuousAt (fun y => outH l P y i) x := by
  have hn0 : (‖x‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr hx)
  have hn := continuousAt_norm_cast x
  have hxi := continuousAt_xi_norm l x hx
  unfold outH Hform
  exact (continuousAt_const.mul (hxi.div (hn.pow _) (pow_ne_zero _ hn0))).mul
    (continuous_angularToroidal P i).continuousAt

theorem continuousOn_outE (l : ℕ) (P : Poly) (Ω : Set Space) (h0 : ∀ x ∈ Ω, x ≠ 0) (i : Fin 3) :
    ContinuousOn (fun y => outE l P y i) Ω :=
  fun x hx => (continuousAt_outE l P x (h0 x hx) i).continuousWithinAt

theorem continuousOn_outH (l : ℕ) (P : Poly) (Ω : Set Space) (h0 : ∀ x ∈ Ω, x ≠ 0) (i : Fin 3) :
    ContinuousOn (fun y => outH l P y i) Ω :=
  fun x hx => (continuousAt_outH l P x (h0 x hx) i).continuousWithinAt

/-- The polarized outgoing pair: the electric part `α outE + β outH` and magnetic part `α outH - β outE`
of the two polarizations with coefficients `α`, `β` satisfy the weak first Maxwell equation. -/
theorem weak_out_pair (l : ℕ) (P : Poly) (hp : P.IsHomogeneous l) (hh : formalLaplacian P = 0)
    (Ω : Set Space) (h0 : ∀ x ∈ Ω, x ≠ 0) (α β : ℂ) :
    WeakOn Ω (fun x i => α * outE l P x i + β * outH l P x i)
      (fun x i => α * outH l P x i - β * outE l P x i) :=
  weakOn_combo _ _ α β (continuousOn_outE l P Ω h0) (continuousOn_outH l P Ω h0)
    (weak_out_tm l P Ω h0) (weak_out_te l P hp hh Ω h0)

end OQ14.CoreOutgoingModes

#print axioms OQ14.CoreOutgoingModes.vacuum_data
#print axioms OQ14.CoreOutgoingModes.sigma_data
#print axioms OQ14.CoreOutgoingModes.electric_data
#print axioms OQ14.CoreOutgoingModes.magnetic_data
#print axioms OQ14.CoreOutgoingModes.weakCurlPairing_eq
#print axioms OQ14.CoreOutgoingModes.fieldPair_neg
#print axioms OQ14.CoreOutgoingModes.weak_electric_data
#print axioms OQ14.CoreOutgoingModes.weak_magnetic_data
#print axioms OQ14.CoreOutgoingModes.weak_out_tm
#print axioms OQ14.CoreOutgoingModes.weak_out_te
#print axioms OQ14.CoreOutgoingModes.continuousAt_xiD
#print axioms OQ14.CoreOutgoingModes.continuousAt_norm_cast
#print axioms OQ14.CoreOutgoingModes.continuousAt_xi_norm
#print axioms OQ14.CoreOutgoingModes.continuousAt_xiD_norm
#print axioms OQ14.CoreOutgoingModes.continuous_coord
#print axioms OQ14.CoreOutgoingModes.continuous_dcoord_cE
#print axioms OQ14.CoreOutgoingModes.continuous_angularToroidal
#print axioms OQ14.CoreOutgoingModes.continuousAt_outE
#print axioms OQ14.CoreOutgoingModes.continuousAt_outH
#print axioms OQ14.CoreOutgoingModes.continuousOn_outE
#print axioms OQ14.CoreOutgoingModes.continuousOn_outH
#print axioms OQ14.CoreOutgoingModes.weak_out_pair
