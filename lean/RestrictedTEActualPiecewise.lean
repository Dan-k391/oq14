import RestrictedTEActualCore
import BackgroundFluxMajorant
import SourcePairedNormSmallness

/-! Assembly plumbing for the actual plane fields outside the core.

The actual plane fields of the paired device are the assembled core fields on the open core `‖ξ‖ < Rin` and
abstract outside fields `out`, `outH` beyond it.  This module proves everything that is independent of the analytic
content of the outside fields:

* `piecewiseE`: the field family with value `core n r x ξ` for `‖ξ‖ < Rin r` and `out n r x ξ` otherwise (linear,
  with measurable coordinates when both pieces are); with the cut-off device core fields it agrees with the
  assembled core fields on the open core, so `CoreAgreement` reduces to the measurability of the outside fields
  and the tail majorant (`coreAgreement_of_out`);
* `tail_of_two_majorants`: a core majorant and an outside majorant of the plane flux give the tail field;
* `outside_majorant_of_decomp`: the outside majorant from the radial/tangential decompositions of the outside
  fields (`SourceRemotePlaneBand.Decomp`, `flux_bound_of_decomp`), from a decomposition of a sum of a background
  and a radiated field (`outside_decomp_of_sum`), and from the uniform decomposition of the TE background field on
  the unit-power sphere of an orthonormal span (`background_decomp_span`, by linearity of the background in the
  input and the audited `background_decomp_majorant`);
* `solution_bounded_on_sphere`: the inclusion part of the combined solution (`inclPart_eq_inclSolution`) is bounded
  uniformly in the shell index on the unit-power sphere of the span;
* `tail_field_of_two_majorants`: the `tail` field of `CoreAgreement` for the piecewise fields;
* `actual_counted_subspaces_of_pieces`: the counted-subspace theorem through the fixed square from the core
  majorant, the outside decomposition hypotheses and the twist identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
namespace OQ14.RestrictedTEActualPiecewise
open MeasureTheory Filter Topology Metric Set
open scoped ComplexConjugate

abbrev FieldMap := OQ14.RestrictedTEActualFields.FieldMap
abbrev Vec := OQ14.RestrictedTEActualCore.Vec

/-! ### The piecewise fields -/

/-- The field family equal to `core n r` on the open disk `‖ξ‖ < Rin r` and to `out n r` outside it. -/
def piecewiseE (Rin : ℕ → ℝ) (core out : ℕ → ℕ → FieldMap) (n r : ℕ) : FieldMap where
  toFun x ξ := if ‖ξ‖ < Rin r then core n r x ξ else out n r x ξ
  map_add' x w := by
    funext ξ
    by_cases h : ‖ξ‖ < Rin r
    · simp only [h, if_true, Pi.add_apply]
      exact congrFun (map_add (core n r) x w) ξ
    · simp only [h, if_false, Pi.add_apply]
      exact congrFun (map_add (out n r) x w) ξ
  map_smul' z x := by
    funext ξ
    by_cases h : ‖ξ‖ < Rin r
    · simp only [h, if_true, Pi.smul_apply, RingHom.id_apply]
      exact congrFun (map_smul (core n r) z x) ξ
    · simp only [h, if_false, Pi.smul_apply, RingHom.id_apply]
      exact congrFun (map_smul (out n r) z x) ξ

theorem piecewiseE_apply_lt (Rin : ℕ → ℝ) (core out : ℕ → ℕ → FieldMap) (n r : ℕ) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (h : ‖ξ‖ < Rin r) : piecewiseE Rin core out n r x ξ = core n r x ξ := by
  change (if ‖ξ‖ < Rin r then core n r x ξ else out n r x ξ) = _
  rw [if_pos h]

theorem piecewiseE_apply_ge (Rin : ℕ → ℝ) (core out : ℕ → ℕ → FieldMap) (n r : ℕ) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (h : Rin r ≤ ‖ξ‖) : piecewiseE Rin core out n r x ξ = out n r x ξ := by
  change (if ‖ξ‖ < Rin r then core n r x ξ else out n r x ξ) = _
  rw [if_neg (not_lt.mpr h)]

/-- The piecewise field has a.e.-strongly measurable coordinates when both pieces do. -/
theorem piecewiseE_meas (Rin : ℕ → ℝ) (core out : ℕ → ℕ → FieldMap)
    (hc : ∀ n r x i, AEStronglyMeasurable (fun ξ => core n r x ξ i) volume)
    (ho : ∀ n r x i, AEStronglyMeasurable (fun ξ => out n r x ξ i) volume) (n r : ℕ) (x : Vec) (i : Fin 3) :
    AEStronglyMeasurable (fun ξ => piecewiseE Rin core out n r x ξ i) volume := by
  classical
  have hs : MeasurableSet {ξ : PlaneInverseCube.Plane | ‖ξ‖ < Rin r} :=
    (isOpen_lt continuous_norm continuous_const).measurableSet
  have h := AEStronglyMeasurable.piecewise (μ := volume) (s := {ξ : PlaneInverseCube.Plane | ‖ξ‖ < Rin r})
    (f := fun ξ => core n r x ξ i) (g := fun ξ => out n r x ξ i) hs (hc n r x i).restrict (ho n r x i).restrict
  refine h.congr (Eventually.of_forall (fun ξ => ?_))
  by_cases hξ : ‖ξ‖ < Rin r
  · beta_reduce
    rw [Set.piecewise_eq_of_mem _ _ _ (show ξ ∈ {ξ : PlaneInverseCube.Plane | ‖ξ‖ < Rin r} from hξ),
      piecewiseE_apply_lt Rin core out n r x ξ hξ]
  · beta_reduce
    rw [Set.piecewise_eq_of_not_mem _ _ _ (show ξ ∉ {ξ : PlaneInverseCube.Plane | ‖ξ‖ < Rin r} from hξ),
      piecewiseE_apply_ge Rin core out n r x ξ (not_lt.mp hξ)]

/-- The flux of the piecewise fields is the flux of the core fields inside the disk. -/
theorem piecewise_flux_lt (Rin : ℕ → ℝ) (coreE coreH outE outH : ℕ → ℕ → FieldMap) (n r : ℕ) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (h : ‖ξ‖ < Rin r) :
    OQ14.RestrictedTEActualFields.fieldFlux (piecewiseE Rin coreE outE n r) (piecewiseE Rin coreH outH n r) x ξ =
      OQ14.RestrictedTEActualFields.fieldFlux (coreE n r) (coreH n r) x ξ := by
  unfold OQ14.RestrictedTEActualFields.fieldFlux
  rw [piecewiseE_apply_lt Rin coreE outE n r x ξ h, piecewiseE_apply_lt Rin coreH outH n r x ξ h]

/-- The flux of the piecewise fields is the flux of the outside fields outside the disk. -/
theorem piecewise_flux_ge (Rin : ℕ → ℝ) (coreE coreH outE outH : ℕ → ℕ → FieldMap) (n r : ℕ) (x : Vec)
    (ξ : PlaneInverseCube.Plane) (h : Rin r ≤ ‖ξ‖) :
    OQ14.RestrictedTEActualFields.fieldFlux (piecewiseE Rin coreE outE n r) (piecewiseE Rin coreH outH n r) x ξ =
      OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ := by
  unfold OQ14.RestrictedTEActualFields.fieldFlux
  rw [piecewiseE_apply_ge Rin coreE outE n r x ξ h, piecewiseE_apply_ge Rin coreH outH n r x ξ h]

/-! ### Assembly of the tail from a core majorant and an outside majorant -/

/-- **Tail assembly.**  A majorant `C1/‖ξ‖³` of the flux of the core fields for `ρ1 ≤ ‖ξ‖ < Rin r` and a majorant
`C2/‖ξ‖³` of the flux of the outside fields for `Rin r ≤ ‖ξ‖` give the majorant of the flux of the piecewise
fields for `ρ1 ≤ ‖ξ‖`.  (The sets of inputs are arbitrary.) -/
theorem tail_of_two_majorants (Rin : ℕ → ℝ) (coreE coreH outE outH : ℕ → ℕ → FieldMap) (n : ℕ) (S : Set Vec)
    (hT1 : ∃ (C1 ρ1 : ℝ) (r1 : ℕ), ∀ r ≥ r1, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖ξ‖ < Rin r →
      ‖OQ14.RestrictedTEActualFields.fieldFlux (coreE n r) (coreH n r) x ξ‖ ≤ C1 / ‖ξ‖ ^ 3)
    (hT2 : ∃ (C2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, Rin r ≤ ‖ξ‖ →
      ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2 / ‖ξ‖ ^ 3) :
    ∃ (C ρ1 : ℝ) (r1 : ℕ), ∀ r ≥ r1, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
      ‖OQ14.RestrictedTEActualFields.fieldFlux (piecewiseE Rin coreE outE n r) (piecewiseE Rin coreH outH n r) x ξ‖ ≤
        C / ‖ξ‖ ^ 3 := by
  obtain ⟨C1, ρ1, r1, h1⟩ := hT1
  obtain ⟨C2, r2, h2⟩ := hT2
  refine ⟨max C1 C2, ρ1, max r1 r2, fun r hr x hx ξ hξ => ?_⟩
  have hpos : 0 ≤ ‖ξ‖ ^ 3 := by positivity
  by_cases hlt : ‖ξ‖ < Rin r
  · rw [piecewise_flux_lt Rin coreE coreH outE outH n r x ξ hlt]
    exact (h1 r ((le_max_left _ _).trans hr) x hx ξ hξ hlt).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) hpos)
  · rw [piecewise_flux_ge Rin coreE coreH outE outH n r x ξ (not_lt.mp hlt)]
    exact (h2 r ((le_max_right _ _).trans hr) x hx ξ (not_lt.mp hlt)).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hpos)

/-! ### Agreement with the assembled core fields -/

section Agree
open OQ14.RestrictedTEPartnerSmallness OQ14.RestrictedTEActualCore

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℝ → ι → FourierL2.Space} {ρ χ R γ : ℝ}
  (hd : Device p ρ χ R γ) {q : ℝ} (hq : 1 < q) {b : ℝ} (hRb : R ≤ b)

/-- The piecewise electric field (cut-off device core, abstract outside) agrees with the assembled electric field on
the open core, for large shell index. -/
theorem piecewise_agreeE (out : ℕ → ℕ → FieldMap) (n : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
      ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
        piecewiseE (fun r => RadialPhaseLimit.radius r) (fun n r => deviceFieldE hd hq hRb n r) out n r x ξ =
          coreE q hq.le n r (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ := by
  filter_upwards [deviceFieldE_agree hd hq hRb n] with r hr x ξ hξ
  rw [piecewiseE_apply_lt (fun r => RadialPhaseLimit.radius r) (fun n r => deviceFieldE hd hq hRb n r) out n r x ξ hξ]
  exact hr x ξ hξ

theorem piecewise_agreeH (out : ℕ → ℕ → FieldMap) (n : ℕ) :
    ∀ᶠ r : ℕ in atTop, ∀ (x : Vec) (ξ : PlaneInverseCube.Plane),
      ‖ξ‖ < (SourcePairedInclusion.data q hq.le n r).R →
        piecewiseE (fun r => RadialPhaseLimit.radius r) (fun n r => deviceFieldH hd hq hRb n r) out n r x ξ =
          coreH q hq.le n r (deviceCoeff p ρ χ hd.hχ q n) (deviceData p ρ χ R hd.hρ hd.hχ hd.hi q hq n) x ξ := by
  filter_upwards [deviceFieldH_agree hd hq hRb n] with r hr x ξ hξ
  rw [piecewiseE_apply_lt (fun r => RadialPhaseLimit.radius r) (fun n r => deviceFieldH hd hq hRb n r) out n r x ξ hξ]
  exact hr x ξ hξ

end Agree

/-- **`CoreAgreement` reduces to the outside fields.**  For the concrete doubled device, the piecewise fields (cut-off
device core fields inside the disk of radius `radius r`, abstract outside fields beyond) satisfy `CoreAgreement` as
soon as the outside fields are measurable and the piecewise flux has the inverse-cube tail majorant. -/
theorem coreAgreement_of_out {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖OQ14.RestrictedTEDipoleProfile.abovePoint
      (OQ14.RestrictedTEConcreteDevice.hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) {q : ℝ} (hq : 1 < q)
    {b : ℝ} (hRb : R ≤ b) (outE outH : ℕ → ℕ → FieldMap)
    (hmeas : ∀ (n r : ℕ) (x : Vec) (i : Fin 3),
      AEStronglyMeasurable (fun ξ => outE n r x ξ i) volume ∧ AEStronglyMeasurable (fun ξ => outH n r x ξ i) volume)
    (htail : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C ρ1 : ℝ) (r1 : ℕ),
        ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
            ‖OQ14.RestrictedTEActualFields.fieldFlux
              (piecewiseE (fun r => RadialPhaseLimit.radius r)
                (fun n r => OQ14.RestrictedTEActualCore.deviceFieldE
                  (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r) outE n r)
              (piecewiseE (fun r => RadialPhaseLimit.radius r)
                (fun n r => OQ14.RestrictedTEActualCore.deviceFieldH
                  (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r) outH n r)
              x ξ‖ ≤ C / ‖ξ‖ ^ 3) :
    OQ14.RestrictedTEActualCore.CoreAgreement r0 y ρ χ h R hρ hχ hi q hq
      (piecewiseE (fun r => RadialPhaseLimit.radius r)
        (fun n r => OQ14.RestrictedTEActualCore.deviceFieldE
          (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r) outE)
      (piecewiseE (fun r => RadialPhaseLimit.radius r)
        (fun n r => OQ14.RestrictedTEActualCore.deviceFieldH
          (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r) outH) where
  meas := fun n r x i =>
    ⟨piecewiseE_meas _ _ _ (fun n r x i => (OQ14.RestrictedTEActualCore.deviceField_meas
        (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r x i).1)
      (fun n r x i => (hmeas n r x i).1) n r x i,
     piecewiseE_meas _ _ _ (fun n r x i => (OQ14.RestrictedTEActualCore.deviceField_meas
        (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r x i).2)
      (fun n r x i => (hmeas n r x i).2) n r x i⟩
  agreeE := fun n => piecewise_agreeE (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi)
    hq hRb outE n
  agreeH := fun n => piecewise_agreeH (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi)
    hq hRb outH n
  tail := htail

/-! ### The outside majorant from radial/tangential decompositions -/

section Outside
open OQ14.SourceRemotePlaneBand

theorem decomp_mono {K1 K2 K1' K2' : ℝ} {F : Maxwell.Vector} {x : Maxwell.Space} (h : Decomp K1 K2 F x)
    (h1 : K1 ≤ K1') (h2 : K2 ≤ K2') : Decomp K1' K2' F x := by
  obtain ⟨Et, Er, hF, hd, he, hE, hR⟩ := h
  exact ⟨Et, Er, hF, hd, he, hE.trans (div_le_div_of_nonneg_right h1 (norm_nonneg x)),
    hR.trans (div_le_div_of_nonneg_right h2 (by positivity))⟩

/-- **The outside majorant from decompositions.**  If the outside electric and magnetic fields of every input of
`S` split, at every plane point outside the disk, into a part orthogonal to the position of size `K1/‖ξ‖`
(`L1/‖ξ‖`) and a radial part of size `K2/‖ξ‖²` (`L2/‖ξ‖²`), with constants independent of the shell index, the normal
flux is at most `(2 K2 L1 + 2 K1 L2)/‖ξ‖³`. -/
theorem outside_majorant_of_decomp (Rin : ℕ → ℝ) (hRin : ∀ r, 0 < Rin r) (outE outH : ℕ → ℕ → FieldMap) (n : ℕ)
    (S : Set Vec)
    (hdec : ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, Rin r ≤ ‖ξ‖ →
      Decomp K1 K2 (outE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
        Decomp L1 L2 (outH n r x ξ) (MaxwellPlaneTail.planePoint ξ)) :
    ∃ (C2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, Rin r ≤ ‖ξ‖ →
      ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2 / ‖ξ‖ ^ 3 := by
  obtain ⟨K1, K2, L1, L2, r2, h⟩ := hdec
  refine ⟨2 * K2 * L1 + 2 * K1 * L2, r2, fun r hr x hx ξ hξ => ?_⟩
  have hpos : 0 < ‖MaxwellPlaneTail.planePoint ξ‖ := by
    rw [MaxwellPlaneTail.planePoint_norm]
    exact lt_of_lt_of_le (hRin r) hξ
  obtain ⟨hE, hH⟩ := h r hr x hx ξ hξ
  have := flux_bound_of_decomp (MaxwellPlaneTail.planePoint ξ) (by rfl) hpos _ _ K1 K2 L1 L2 hE hH
  rw [MaxwellPlaneTail.planePoint_norm] at this
  exact this

/-- **Decomposition of a sum.**  The outside fields are the sum of a background and a radiated field; the
background decomposes (constants independent of the shell index) beyond a radius `ρ₁`, the radiated field
decomposes outside the disk; since the disk radius tends to infinity the sum decomposes outside the disk. -/
theorem outside_decomp_of_sum (Rin : ℕ → ℝ) (hRinTop : Tendsto Rin atTop atTop) (outE outH : ℕ → ℕ → FieldMap)
    (n : ℕ) (S : Set Vec) (bgE bgH radE radH : ℕ → Vec → PlaneInverseCube.Plane → Maxwell.Vector)
    (hsum : ∀ (r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane), Rin r ≤ ‖ξ‖ →
      outE n r x ξ = bgE r x ξ + radE r x ξ ∧ outH n r x ξ = bgH r x ξ + radH r x ξ)
    (hbg : ∃ (ρ₁ K1 L1 L2 : ℝ), ∀ (r : ℕ), ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, ρ₁ ≤ ‖ξ‖ →
      Decomp K1 0 (bgE r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
        Decomp L1 L2 (bgH r x ξ) (MaxwellPlaneTail.planePoint ξ))
    (hrad : ∃ (K1' K2' L1' L2' : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, Rin r ≤ ‖ξ‖ →
      Decomp K1' K2' (radE r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
        Decomp L1' L2' (radH r x ξ) (MaxwellPlaneTail.planePoint ξ)) :
    ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ S, ∀ ξ : PlaneInverseCube.Plane, Rin r ≤ ‖ξ‖ →
      Decomp K1 K2 (outE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
        Decomp L1 L2 (outH n r x ξ) (MaxwellPlaneTail.planePoint ξ) := by
  obtain ⟨ρ₁, Kb, Lb1, Lb2, hb⟩ := hbg
  obtain ⟨Kr1, Kr2, Lr1, Lr2, r2, hr⟩ := hrad
  obtain ⟨r3, hr3⟩ := Filter.eventually_atTop.mp (hRinTop.eventually_ge_atTop ρ₁)
  refine ⟨Kb + Kr1, 0 + Kr2, Lb1 + Lr1, Lb2 + Lr2, max r2 r3, fun r hrr x hx ξ hξ => ?_⟩
  have hρ : ρ₁ ≤ ‖ξ‖ := (hr3 r ((le_max_right _ _).trans hrr)).trans hξ
  obtain ⟨hb1, hb2⟩ := hb r x hx ξ hρ
  obtain ⟨hr1, hr2'⟩ := hr r ((le_max_left _ _).trans hrr) x hx ξ hξ
  obtain ⟨e1, e2⟩ := hsum r x ξ hξ
  rw [e1, e2]
  exact ⟨decomp_add hb1 hr1, decomp_add hb2 hr2'⟩

end Outside

/-! ### The TE background field of a span, uniformly on the unit sphere -/

section Background
open OQ14.SourceRemotePlaneBand OQ14.BackgroundModeTE OQ14.BackgroundFluxMajorant

/-- A finite family sum with coefficient function `c` over the finset `s`. -/
def famSum (s : Finset SymmetricHarmonicJets.Index) (c : SymmetricHarmonicJets.Index → ℂ)
    (F : SymmetricHarmonicJets.Index → Maxwell.Field) : Maxwell.Field :=
  ∑ q ∈ s, c q • F q

theorem teCoeff_not_mem (C : Vec) (q : SymmetricHarmonicJets.Index) (hq : q ∉ C.support) : teCoeff C q = 0 := by
  have h : C q = 0 := Finsupp.not_mem_support_iff.mp hq
  simp [teCoeff, RestrictedTEIncoming.coefficient, h]

theorem teCoeff_comb (A B : Vec) (z : ℂ) (q : SymmetricHarmonicJets.Index) :
    teCoeff (A + z • B) q = teCoeff A q + z * teCoeff B q := by
  unfold teCoeff RestrictedTEIncoming.coefficient
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  ring

theorem famSum_extend (F : SymmetricHarmonicJets.Index → Maxwell.Field) (C : Vec)
    (S : Finset SymmetricHarmonicJets.Index) (hS : C.support ⊆ S) :
    famSum C.support (teCoeff C) F = famSum S (teCoeff C) F := by
  unfold famSum
  exact Finset.sum_subset hS (fun q _ hq => by rw [teCoeff_not_mem C q hq, zero_smul])

theorem famSum_comb (F : SymmetricHarmonicJets.Index → Maxwell.Field) (A B : Vec) (z : ℂ) :
    famSum (A + z • B).support (teCoeff (A + z • B)) F =
      famSum A.support (teCoeff A) F + z • famSum B.support (teCoeff B) F := by
  classical
  have hA : A.support ⊆ A.support ∪ B.support := Finset.subset_union_left
  have hB : B.support ⊆ A.support ∪ B.support := Finset.subset_union_right
  have hC : (A + z • B).support ⊆ A.support ∪ B.support := by
    intro q hq
    rcases Finset.mem_union.mp (Finsupp.support_add hq) with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finsupp.support_smul h)
  rw [famSum_extend F _ _ hC, famSum_extend F A _ hA, famSum_extend F B _ hB]
  unfold famSum
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [teCoeff_comb, add_smul, smul_smul]

/-- The TE background electric field of the physical stack at shell index `s` of a finite coefficient vector. -/
def bgFieldE (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) (A : Vec) : Maxwell.Field :=
  famBackground (physicalTE q (zero_lt_one.trans_le hq) n s) A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial

/-- The TE background magnetic field (the dual field of the TM structure) of the physical stack. -/
def bgFieldH (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) (A : Vec) : Maxwell.Field :=
  famBackgroundH (physicalTE q (zero_lt_one.trans_le hq) n s) A.support (teCoeff A) (fun q => q.val.1)
    RestrictedTEIncoming.polynomial

theorem bgFieldE_comb (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) (A B : Vec) (z : ℂ) :
    bgFieldE q hq n s (A + z • B) = bgFieldE q hq n s A + z • bgFieldE q hq n s B := by
  unfold bgFieldE famBackground
  exact famSum_comb _ A B z

theorem bgFieldH_comb (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) (A B : Vec) (z : ℂ) :
    bgFieldH q hq n s (A + z • B) = bgFieldH q hq n s A + z • bgFieldH q hq n s B := by
  unfold bgFieldH famBackgroundH
  exact famSum_comb _ A B z

theorem bgFieldE_zero (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) : bgFieldE q hq n s 0 = 0 := by
  unfold bgFieldE famBackground
  simp

theorem bgFieldH_zero (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) : bgFieldH q hq n s 0 = 0 := by
  unfold bgFieldH famBackgroundH
  simp

/-- The background electric field as a linear map of the input. -/
def bgLinE (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) : Vec →ₗ[ℂ] Maxwell.Field where
  toFun := bgFieldE q hq n s
  map_add' A B := by
    have := bgFieldE_comb q hq n s A B 1
    simpa using this
  map_smul' z A := by
    have := bgFieldE_comb q hq n s 0 A z
    simpa [bgFieldE_zero] using this

def bgLinH (q : ℝ) (hq : 1 ≤ q) (n s : ℕ) : Vec →ₗ[ℂ] Maxwell.Field where
  toFun := bgFieldH q hq n s
  map_add' A B := by
    have := bgFieldH_comb q hq n s A B 1
    simpa using this
  map_smul' z A := by
    have := bgFieldH_comb q hq n s 0 A z
    simpa [bgFieldH_zero] using this

/-- **Uniform decomposition of the TE background on the unit sphere of a span.**  For a finite family `B` of inputs
there are `ρ₁`, `K1`, `L1`, `L2` such that for every shell index `s`, every combination `∑ cf_k B_k` with
`‖cf_k‖ ≤ 1` and every point `y` with `ρ₁ ≤ ‖y‖`, the background electric field is orthogonal to `y` up to `K1/‖y‖`
and the background magnetic field splits into an orthogonal part `L1/‖y‖` and a radial part `L2/‖y‖²`. -/
theorem background_decomp_span (q : ℝ) (hq : 1 ≤ q) (n : ℕ) {κ : Type*} [Fintype κ] (B : κ → Vec) :
    ∃ ρ₁ K1 L1 L2 : ℝ, 0 < ρ₁ ∧ ∀ (s : ℕ) (cf : κ → ℂ), (∀ k, ‖cf k‖ ≤ 1) → ∀ y : Maxwell.Space, ρ₁ ≤ ‖y‖ →
      Decomp K1 0 (bgFieldE q hq n s (∑ k, cf k • B k) y) y ∧
        Decomp L1 L2 (bgFieldH q hq n s (∑ k, cf k • B k) y) y := by
  choose ρk Kk L1k L2k hρk hk using fun k => background_decomp_majorant q hq n (B k)
  refine ⟨(∑ k, ρk k) + 1, ∑ k, |Kk k|, ∑ k, |L1k k|, ∑ k, |L2k k|, by
    have : 0 ≤ ∑ k, ρk k := Finset.sum_nonneg (fun k _ => (hρk k).le)
    linarith, ?_⟩
  intro s cf hcf y hy
  have hyk (k : κ) : ρk k ≤ ‖y‖ := by
    have h1 : ρk k ≤ ∑ k, ρk k :=
      Finset.single_le_sum (f := fun k => ρk k) (fun k _ => (hρk k).le) (Finset.mem_univ k)
    linarith
  have eE : bgFieldE q hq n s (∑ k, cf k • B k) y = ∑ k, cf k • bgFieldE q hq n s (B k) y := by
    have := map_sum (bgLinE q hq n s) (fun k => cf k • B k) Finset.univ
    simp only [map_smul] at this
    change bgFieldE q hq n s (∑ k, cf k • B k) y = _
    have h2 : bgFieldE q hq n s (∑ k, cf k • B k) = ∑ k, cf k • bgFieldE q hq n s (B k) := this
    rw [h2]
    simp [Finset.sum_apply]
  have eH : bgFieldH q hq n s (∑ k, cf k • B k) y = ∑ k, cf k • bgFieldH q hq n s (B k) y := by
    have := map_sum (bgLinH q hq n s) (fun k => cf k • B k) Finset.univ
    simp only [map_smul] at this
    change bgFieldH q hq n s (∑ k, cf k • B k) y = _
    have h2 : bgFieldH q hq n s (∑ k, cf k • B k) = ∑ k, cf k • bgFieldH q hq n s (B k) := this
    rw [h2]
    simp [Finset.sum_apply]
  rw [eE, eH]
  have hE := decomp_sum Finset.univ (fun k => cf k • bgFieldE q hq n s (B k) y)
    (fun k => ‖cf k‖ * |Kk k|) (fun k => ‖cf k‖ * 0) y
    (fun k _ => decomp_smul (cf k) (decomp_mono (hk k s y (hyk k)).1 (le_abs_self _) le_rfl))
  have hH := decomp_sum Finset.univ (fun k => cf k • bgFieldH q hq n s (B k) y)
    (fun k => ‖cf k‖ * |L1k k|) (fun k => ‖cf k‖ * |L2k k|) y
    (fun k _ => decomp_smul (cf k) (decomp_mono (hk k s y (hyk k)).2 (le_abs_self _) (le_abs_self _)))
  refine ⟨decomp_mono hE ?_ ?_, decomp_mono hH ?_ ?_⟩
  · exact Finset.sum_le_sum (fun k _ => mul_le_of_le_one_left (abs_nonneg _) (hcf k))
  · simp
  · exact Finset.sum_le_sum (fun k _ => mul_le_of_le_one_left (abs_nonneg _) (hcf k))
  · exact Finset.sum_le_sum (fun k _ => mul_le_of_le_one_left (abs_nonneg _) (hcf k))

/-- The same on the unit-power sphere of the span of an orthonormal family. -/
theorem background_decomp_unit_sphere (q : ℝ) (hq : 1 ≤ q) (n : ℕ) {κ : Type*} [Fintype κ] (B : κ → Vec)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B k))) :
    ∃ ρ₁ K1 L1 L2 : ℝ, 0 < ρ₁ ∧ ∀ (s : ℕ) (x : Vec), x ∈ Submodule.span ℂ (Set.range B) →
      RestrictedTEIncoming.physicalPower x = 1 → ∀ y : Maxwell.Space, ρ₁ ≤ ‖y‖ →
        Decomp K1 0 (bgFieldE q hq n s x y) y ∧ Decomp L1 L2 (bgFieldH q hq n s x y) y := by
  obtain ⟨ρ₁, K1, L1, L2, hρ, h⟩ := background_decomp_span q hq n B
  refine ⟨ρ₁, K1, L1, L2, hρ, fun s x hx hp y hy => ?_⟩
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  exact h s cf (OQ14.RestrictedTEActualFields.unit_coeff_bound B horth cf hp) y hy

end Background

/-! ### The inclusion part of the combined solution on the unit sphere -/

section Solution
open OQ14.RestrictedTEActualCore

/-- The inclusion part of the combined solution of the paired device for the input `x`:
`(effective block)⁻¹` applied to the effective datum `fi + Si T Ss (shell block)⁻¹ fs`. -/
def inclSolution (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x : Vec) : VectorFourier.VectorL2 :=
  Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)
    (SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r x) (fiLin ci dci x))

theorem inclSolution_comb (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (x w : Vec) (z : ℂ) :
    inclSolution q hq n r ci dci b (x + z • w) =
      inclSolution q hq n r ci dci b x + z • inclSolution q hq n r ci dci b w := by
  have hd : SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r (x + z • w)) (fiLin ci dci (x + z • w)) =
      SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r x) (fiLin ci dci x) +
      z • SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r w) (fiLin ci dci w) := by
    unfold SourcePairedPlaneIdentification.effectiveDatum
    simp only [map_add, map_smul, smul_add]
    abel
  unfold inclSolution
  rw [hd, map_add, map_smul]

theorem inclSolution_zero (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) : inclSolution q hq n r ci dci b 0 = 0 := by
  unfold inclSolution SourcePairedPlaneIdentification.effectiveDatum
  simp

/-- The inclusion solution as a linear map of the input. -/
def inclLin (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) : Vec →ₗ[ℂ] VectorFourier.VectorL2 where
  toFun := inclSolution q hq n r ci dci b
  map_add' x w := by
    have := inclSolution_comb q hq n r ci dci b x w 1
    simpa using this
  map_smul' z x := by
    have := inclSolution_comb q hq n r ci dci b 0 x z
    simpa [inclSolution_zero] using this

/-- **The inclusion solution is bounded on the unit-power sphere of a span, uniformly in the shell index.**  If the
limiting effective block is a unit, then for a finite family `B` of inputs there are `U` and `r0` with
`‖inclSolution r x‖ ≤ U` for `r ≥ r0` and every combination `∑ cf_k B_k` with `‖cf_k‖ ≤ 1` (in particular for every
unit-power input of the span of an orthonormal family, `solution_bounded_on_sphere`). -/
theorem solution_bounded_of_coeffs (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b) (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0))
    {κ : Type*} [Fintype κ] (B : κ → Vec) :
    ∃ (U : ℝ) (r0 : ℕ), ∀ r ≥ r0, ∀ cf : κ → ℂ, (∀ k, ‖cf k‖ ≤ 1) →
      ‖inclSolution q hq n r ci dci b (∑ k, cf k • B k)‖ ≤ U := by
  have hconv (k : κ) := SourcePairedReduction.effective_solution_tendsto q hq n ci dci b hb0 hcar hL
    (fun r => SourcePairedPlaneIdentification.effectiveDatum (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r (B k)) (fiLin ci dci (B k)))
    (gLim q hq n ci dci (B k)) (effectiveDatum_conv q hq n ci dci b hcar (B k))
  set lim : κ → ℝ := fun k => ‖Ring.inverse (SourcePairedReduction.limitEffective q hq n ci dci b hb0)
    (gLim q hq n ci dci (B k))‖ with hlim
  have hev : ∀ᶠ r : ℕ in atTop, ∀ k : κ, ‖inclSolution q hq n r ci dci b (B k)‖ < lim k + 1 := by
    rw [Filter.eventually_all]
    intro k
    exact ((hconv k).norm).eventually (gt_mem_nhds (lt_add_one (lim k)))
  obtain ⟨r0, hr0⟩ := Filter.eventually_atTop.mp hev
  refine ⟨∑ k, (lim k + 1), r0, fun r hr cf hcf => ?_⟩
  have e : inclSolution q hq n r ci dci b (∑ k, cf k • B k) = ∑ k, cf k • inclSolution q hq n r ci dci b (B k) := by
    have := map_sum (inclLin q hq n r ci dci b) (fun k => cf k • B k) Finset.univ
    simp only [map_smul] at this
    exact this
  rw [e]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hcf k)).trans (hr0 r hr k).le

/-- The inclusion solution is bounded on the unit-power sphere of the span of an orthonormal family. -/
theorem solution_bounded_on_sphere (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb0 : 0 < b)
    (hcar : ∀ x ∈ dci.carrier, ‖x‖ ≤ b) (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci dci b hb0))
    {κ : Type*} [Fintype κ] (B : κ → Vec) (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B k))) :
    ∃ (U : ℝ) (r0 : ℕ), ∀ r ≥ r0, ∀ x ∈ Submodule.span ℂ (Set.range B),
      RestrictedTEIncoming.physicalPower x = 1 → ‖inclSolution q hq n r ci dci b x‖ ≤ U := by
  obtain ⟨U, r0, h⟩ := solution_bounded_of_coeffs q hq n ci dci b hb0 hcar hL B
  refine ⟨U, r0, fun r hr x hx hp => ?_⟩
  obtain ⟨cf, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hx
  exact h r hr cf (OQ14.RestrictedTEActualFields.unit_coeff_bound B horth cf hp)

end Solution

/-! ### The outside majorant from the background and the radiated decomposition -/

section Pieces
open OQ14.SourceRemotePlaneBand

/-- The decomposition hypotheses on the outside fields `outE`, `outH`: outside the disk they are the sum of the TE
background (`bgFieldE`, `bgFieldH` of the physical stack at shell index `r`) and a radiated field `radE`, `radH`
(`sumE`, `sumH`), and the radiated field splits into a part orthogonal to the position of size `K1/‖ξ‖` (`L1/‖ξ‖`)
and a radial part of size `K2/‖ξ‖²` (`L2/‖ξ‖²`), with constants independent of the shell index, on the unit-power
sphere of the span of every orthonormal family (`rad`). -/
structure OutsideDecomposition (q : ℝ) (hq : 1 ≤ q) (outE outH : ℕ → ℕ → FieldMap)
    (radE radH : ℕ → ℕ → Vec → PlaneInverseCube.Plane → Maxwell.Vector) : Prop where
  sumE : ∀ (n r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane), RadialPhaseLimit.radius r ≤ ‖ξ‖ →
    outE n r x ξ = bgFieldE q hq n r x (MaxwellPlaneTail.planePoint ξ) + radE n r x ξ
  sumH : ∀ (n r : ℕ) (x : Vec) (ξ : PlaneInverseCube.Plane), RadialPhaseLimit.radius r ≤ ‖ξ‖ →
    outH n r x ξ = bgFieldH q hq n r x (MaxwellPlaneTail.planePoint ξ) + radH n r x ξ
  rad : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
    Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
      ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
          Decomp K1 K2 (radE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
            Decomp L1 L2 (radH n r x ξ) (MaxwellPlaneTail.planePoint ξ)

/-- **The outside majorant (T2).**  From the sum structure, the uniform decomposition of the background on the
unit sphere of the span (`background_decomp_unit_sphere`) and the decomposition of the radiated field, the plane flux
of the outside fields is at most `C2/‖ξ‖³` outside the disk, for large shell index. -/
theorem outside_majorant_of_pieces (q : ℝ) (hq : 1 ≤ q) (outE outH : ℕ → ℕ → FieldMap)
    (radE radH : ℕ → ℕ → Vec → PlaneInverseCube.Plane → Maxwell.Vector)
    (hOD : OutsideDecomposition q hq outE outH radE radH) (n : ℕ) (N : Nat) (B : Fin N → Vec)
    (horth : Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)))
    (hradn : ∃ (K1 K2 L1 L2 : ℝ) (r2 : ℕ),
      ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
          Decomp K1 K2 (radE n r x ξ) (MaxwellPlaneTail.planePoint ξ) ∧
            Decomp L1 L2 (radH n r x ξ) (MaxwellPlaneTail.planePoint ξ)) :
    ∃ (C2 : ℝ) (r2 : ℕ), ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B),
      RestrictedTEIncoming.physicalPower x = 1 → ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
        ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2 / ‖ξ‖ ^ 3 := by
  set S : Set Vec := {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1} with hS
  obtain ⟨ρ₁, K1, L1, L2, hρ, hbg⟩ := background_decomp_unit_sphere q hq n B horth
  obtain ⟨K1', K2', L1', L2', r2', hr⟩ := hradn
  have hdec := outside_decomp_of_sum (fun r => RadialPhaseLimit.radius r) RadialPhaseLimit.radius_tendsto outE outH
    n S (fun r x ξ => bgFieldE q hq n r x (MaxwellPlaneTail.planePoint ξ))
    (fun r x ξ => bgFieldH q hq n r x (MaxwellPlaneTail.planePoint ξ)) (radE n) (radH n)
    (fun r x ξ hξ => ⟨hOD.sumE n r x ξ hξ, hOD.sumH n r x ξ hξ⟩)
    ⟨ρ₁, K1, L1, L2, fun r x hx ξ hξ => hbg r x hx.1 hx.2 (MaxwellPlaneTail.planePoint ξ)
      (by rw [MaxwellPlaneTail.planePoint_norm]; exact hξ)⟩
    ⟨K1', K2', L1', L2', r2', fun r hr' x hx ξ hξ => hr r hr' x hx.1 hx.2 ξ hξ⟩
  obtain ⟨C2, r2, h⟩ := outside_majorant_of_decomp (fun r => RadialPhaseLimit.radius r)
    (fun r => RadialPhaseLimit.radius_pos r) outE outH n S hdec
  exact ⟨C2, r2, fun r hr x hx hp ξ hξ => h r hr x ⟨hx, hp⟩ ξ hξ⟩

end Pieces

/-! ### The composite counted-subspace theorem -/

section Composite
open OQ14.RestrictedTEPassageTransfer OQ14.RestrictedTEActualCounting OQ14.RestrictedTEActualWindow
  OQ14.RestrictedTEDipoleProfile OQ14.RestrictedTEDipoleConcentration OQ14.RestrictedTEConcreteDevice
  OQ14.RestrictedTEConcreteDoubled OQ14.RestrictedTEPartnerBalls OQ14.RestrictedTEPlaneJets
  OQ14.RestrictedTEPartnerCount OQ14.RestrictedTEPartnerSmallness OQ14.ChannelMaterialThroughput
  OQ14.RestrictedTEActualSquare

/-- The core majorant (T1): inverse-cube majorant of the plane flux of the assembled core fields `coreE`, `coreH` of
the combined device on `ρ1 ≤ ‖ξ‖ < radius r`, uniform in the shell index on the unit-power sphere of the span of
every orthonormal family (for all large gain indices). -/
structure CoreMajorant {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ)
    (hρ : 0 < ρ) (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (q : ℝ) (hq : 1 < q) : Prop where
  maj : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
    Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C1 ρ1 : ℝ) (r1 : ℕ),
      ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
        ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖ξ‖ < RadialPhaseLimit.radius r →
          ‖crossProduct
              (OQ14.RestrictedTEActualCore.coreE q hq.le n r
                (deviceCoeff (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ hχ.le q n)
                (deviceData (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi q hq n) x ξ)
              (Maxwell.conjugate (OQ14.RestrictedTEActualCore.coreH q hq.le n r
                (deviceCoeff (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ hχ.le q n)
                (deviceData (fun a l => abovePoint (hpoint r0 y l) (h * a)) ρ χ R hρ hχ.le hi q hq n) x ξ)) 2‖ ≤
            C1 / ‖ξ‖ ^ 3

/-- The assembled electric plane field: cut-off device core fields inside the disk of radius `radius r`, abstract
outside fields beyond. -/
def deviceFieldsE {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) {q : ℝ}
    (hq : 1 < q) {b : ℝ} (hRb : R ≤ b) (outE : ℕ → ℕ → FieldMap) : ℕ → ℕ → FieldMap :=
  piecewiseE (fun r => RadialPhaseLimit.radius r)
    (fun n r => OQ14.RestrictedTEActualCore.deviceFieldE
      (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r) outE

/-- The assembled magnetic plane field. -/
def deviceFieldsH {ι : Type*} [Fintype ι] [DecidableEq ι] (r0 : ℝ) (y : ι → ℝ) (ρ χ h R : ℝ) (hρ : 0 < ρ)
    (hχ : 0 < χ)
    (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l, ‖abovePoint (hpoint r0 y l) (h * a)‖ + ρ ≤ R) (hρh : ρ < h) {q : ℝ}
    (hq : 1 < q) {b : ℝ} (hRb : R ≤ b) (outH : ℕ → ℕ → FieldMap) : ℕ → ℕ → FieldMap :=
  piecewiseE (fun r => RadialPhaseLimit.radius r)
    (fun n r => OQ14.RestrictedTEActualCore.deviceFieldH
      (OQ14.RestrictedTEActualCore.concrete_device r0 y ρ χ h R hρ hχ.le hρh hi) hq hRb n r) outH

/-- **Counted subspaces from the pieces.**  Let `twist` be a unitary linear automorphism of the finite input space
whose twist identity holds for every `q > 1` and all large `n`.  With the device parameters of the square theorem
and the physical family `A_k = twist⁻¹ B_k`, for every pair of outside fields `outE`, `outH` with measurable
coordinates, whose electric and magnetic parts outside the disk are the TE background plus a radiated field with
the radial/tangential decomposition (`OutsideDecomposition`), and every core majorant (`CoreMajorant`), the span of `A`
is counted through the square `Dsq L` for the assembled plane fields (the cut-off device core fields inside the
disk, the outside fields beyond), eventually in `n` and then in `r`. -/
theorem actual_counted_subspaces_of_pieces (εp : ℝ) (hεp : 1 < εp) (N : ℕ) (η δ : ℝ) (hη : 0 < η)
    (hηδ : η < δ) (τ : ℝ) (hτ : τ ≤ 1) (L : ℝ) (hL : 0 < L) (twist : Vec ≃ₗ[ℂ] Vec)
    (hu : OQ14.RestrictedTEActualCore.TwistUnitary twist)
    (htw : ∀ (q : ℝ) (hq : 1 < q), ∀ᶠ n : ℕ in atTop, ∀ x : Vec,
      BackgroundCoreTransmission.scaledCoeff x (OQ14.RestrictedTEActualCore.transInf q hq.le n) =
        ((q ^ n : ℝ) : ℂ) • twist x) :
    ∃ (q : ℝ) (hq : 1 < q) (χ : ℝ) (hχ : 0 < χ) (ρ h R : ℝ) (hρ : 0 < ρ) (hρh : ρ < h) (_ : 0 ≤ R)
      (hi : ∀ a, 0 < a → a ≤ 1 → ∀ l : Fin N,
        ‖abovePoint (hpoint (-L) (ysq N L) l) (h * a)‖ + ρ ≤ R)
      (A : Fin N → SymmetricHarmonicJets.Index →₀ ℂ),
      q ^ 2 ≤ εp ∧ 1 + χ ≤ εp ∧
      Orthonormal ℂ (fun k => RestrictedTEInput.input (A k)) ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range A)) = N ∧
      (∀ n : ℕ, ∀ᶠ r : ℕ in atTop, ∃ _ : max R 1 ≤ (SourcePairedInclusion.data q hq.le n r).R,
        ∀ x : FourierL2.Space,
          1 ≤ MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ∧
          MaterialMaxwell.dielectric (pairedCoeff q hq.le n r
            (deviceCoeff (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ hχ.le q n)) x ≤ εp) ∧
      ∀ (outE outH : ℕ → ℕ → FieldMap) (radE radH : ℕ → ℕ → Vec → PlaneInverseCube.Plane → Maxwell.Vector),
        (∀ (n r : ℕ) (x : Vec) (i : Fin 3), AEStronglyMeasurable (fun ξ => outE n r x ξ i) volume ∧
          AEStronglyMeasurable (fun ξ => outH n r x ξ i) volume) →
        OutsideDecomposition q hq.le outE outH radE radH →
        CoreMajorant (-L) (ysq N L) ρ χ h R hρ hχ hi q hq →
        ∀ᶠ n : ℕ in atTop, ∀ᶠ r : ℕ in atTop,
          IsCounted (Submodule.span ℂ (Set.range A))
            (actualScatter (fun a l => abovePoint (hpoint (-L) (ysq N L) l) (h * a)) ρ χ R (max R 1) hρ hχ.le
              (le_max_left R 1) hi q hq n r)
            (fun a => passage volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outH n r) a))
            (fun a => bypass volume (Dsq L) (OQ14.RestrictedTEActualFields.fieldFlux
              (deviceFieldsE (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE n r)
              (deviceFieldsH (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outH n r) a)) τ η δ := by
  obtain ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, h6⟩ :=
    OQ14.RestrictedTEActualCore.actual_counted_subspaces_of_core εp hεp N η δ hη hηδ τ hτ L hL twist hu htw
  refine ⟨q, hq, χ, hχ, ρ, h, R, hρ, hρh, hR, hi, A, h1, h2, h3, h4, h5, ?_⟩
  intro outE outH radE radH hmeas hOD hCM
  have hd := OQ14.RestrictedTEActualCore.concrete_device (-L) (ysq N L) ρ χ h R hρ hχ.le hρh hi
  refine h6 _ _ (coreAgreement_of_out (-L) (ysq N L) ρ χ h R hρ hχ hi hρh hq (le_max_left R 1) outE outH hmeas ?_)
  filter_upwards [hCM.maj, hOD.rad] with n hn1 hn2
  intro N' B horth
  obtain ⟨C1, ρ1, r1, hc⟩ := hn1 N' B horth
  obtain ⟨K1, K2, L1, L2, r2, hrad⟩ := hn2 N' B horth
  obtain ⟨C2, r2', hT2⟩ := outside_majorant_of_pieces q hq.le outE outH radE radH hOD n N' B horth
    ⟨K1, K2, L1, L2, r2, hrad⟩
  obtain ⟨rb, hrb⟩ := Filter.eventually_atTop.mp
    (SourcePairedReduction.eventually_inner_radius q hq.le n (max R 1))
  have hT1 : ∃ (C1' ρ1' : ℝ) (r1' : ℕ), ∀ r ≥ r1',
      ∀ x ∈ {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1},
      ∀ ξ : PlaneInverseCube.Plane, ρ1' ≤ ‖ξ‖ → ‖ξ‖ < RadialPhaseLimit.radius r →
        ‖OQ14.RestrictedTEActualFields.fieldFlux
          (OQ14.RestrictedTEActualCore.deviceFieldE hd hq (le_max_left R 1) n r)
          (OQ14.RestrictedTEActualCore.deviceFieldH hd hq (le_max_left R 1) n r) x ξ‖ ≤ C1' / ‖ξ‖ ^ 3 := by
    refine ⟨C1, ρ1, max r1 rb, fun r hr x hx ξ hξ hlt => ?_⟩
    have hbr := hrb r ((le_max_right _ _).trans hr)
    unfold OQ14.RestrictedTEActualFields.fieldFlux
    rw [OQ14.RestrictedTEActualCore.deviceFieldE_apply hd hq (le_max_left R 1) n r hbr x ξ hlt,
      OQ14.RestrictedTEActualCore.deviceFieldH_apply hd hq (le_max_left R 1) n r hbr x ξ hlt]
    exact hc r ((le_max_left _ _).trans hr) x hx.1 hx.2 ξ hξ hlt
  have hT2' : ∃ (C2' : ℝ) (r2'' : ℕ), ∀ r ≥ r2'',
      ∀ x ∈ {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1},
      ∀ ξ : PlaneInverseCube.Plane, RadialPhaseLimit.radius r ≤ ‖ξ‖ →
        ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2' / ‖ξ‖ ^ 3 :=
    ⟨C2, r2', fun r hr x hx ξ hξ => hT2 r hr x hx.1 hx.2 ξ hξ⟩
  obtain ⟨C, ρ1', r1', ht⟩ := tail_of_two_majorants (fun r => RadialPhaseLimit.radius r)
    (fun n r => OQ14.RestrictedTEActualCore.deviceFieldE hd hq (le_max_left R 1) n r)
    (fun n r => OQ14.RestrictedTEActualCore.deviceFieldH hd hq (le_max_left R 1) n r) outE outH n
    {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1} hT1 hT2'
  exact ⟨C, ρ1', r1', fun r hr x hx hp ξ hξ => ht r hr x ⟨hx, hp⟩ ξ hξ⟩

end Composite

/-! ### The tail field and the identification of the inclusion part -/

/-- **The tail field from two majorants.**  The `tail` field of `CoreAgreement` for the piecewise fields, from a core
majorant and an outside majorant on the unit-power sphere of the span of every orthonormal family. -/
theorem tail_field_of_two_majorants (Rin : ℕ → ℝ) (coreE coreH outE outH : ℕ → ℕ → FieldMap)
    (hT1 : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C1 ρ1 : ℝ) (r1 : ℕ),
        ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ → ‖ξ‖ < Rin r →
            ‖OQ14.RestrictedTEActualFields.fieldFlux (coreE n r) (coreH n r) x ξ‖ ≤ C1 / ‖ξ‖ ^ 3)
    (hT2 : ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C2 : ℝ) (r2 : ℕ),
        ∀ r ≥ r2, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, Rin r ≤ ‖ξ‖ →
            ‖OQ14.RestrictedTEActualFields.fieldFlux (outE n r) (outH n r) x ξ‖ ≤ C2 / ‖ξ‖ ^ 3) :
    ∀ᶠ n : ℕ in atTop, ∀ (N : Nat) (B : Fin N → Vec),
      Orthonormal ℂ (fun k => RestrictedTEInput.input (B k)) → ∃ (C ρ1 : ℝ) (r1 : ℕ),
        ∀ r ≥ r1, ∀ x ∈ Submodule.span ℂ (Set.range B), RestrictedTEIncoming.physicalPower x = 1 →
          ∀ ξ : PlaneInverseCube.Plane, ρ1 ≤ ‖ξ‖ →
            ‖OQ14.RestrictedTEActualFields.fieldFlux (piecewiseE Rin coreE outE n r)
              (piecewiseE Rin coreH outH n r) x ξ‖ ≤ C / ‖ξ‖ ^ 3 := by
  filter_upwards [hT1, hT2] with n h1 h2 N B horth
  obtain ⟨C, ρ1, r1, h⟩ := tail_of_two_majorants Rin coreE coreH outE outH n
    {x | x ∈ Submodule.span ℂ (Set.range B) ∧ RestrictedTEIncoming.physicalPower x = 1}
    (by
      obtain ⟨C1, ρ1, r1, hc⟩ := h1 N B horth
      exact ⟨C1, ρ1, r1, fun r hr x hx ξ hξ hlt => hc r hr x hx.1 hx.2 ξ hξ hlt⟩)
    (by
      obtain ⟨C2, r2, hc⟩ := h2 N B horth
      exact ⟨C2, r2, fun r hr x hx ξ hξ => hc r hr x hx.1 hx.2 ξ hξ⟩)
  exact ⟨C, ρ1, r1, fun r hr x hx hp ξ hξ => h r hr x ⟨hx, hp⟩ ξ hξ⟩

section InclPart
open OQ14.RestrictedTEActualCore

/-- The inclusion part of the combined solution (`shellPart`/`inclPart` block decomposition) is `inclSolution`, for
shell indices at which the inclusion is inside the inner radius and the effective block is a unit. -/
theorem inclPart_eq_inclSolution (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : StaticCoefficient.Coefficient)
    (dci : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hb : b < (SourcePairedInclusion.data q hq n r).R)
    (hci : ∀ y : FourierL2.Space, y ∉ closedBall (0 : FourierL2.Space) b →
      ci.value (VectorFourier.coordinateMap y) = 0)
    (hE : IsUnit (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b)) (x : Vec) :
    SourcePairedPlaneIdentification.inclPart (SourcePairedInclusion.shell q hq n r) ci
        (SourcePairedInclusion.data q hq n r).X (fiLin ci dci x)
        (MaterialField.solution (ShellInclusionVolume.add (SourcePairedInclusion.shell q hq n r) ci) 1
          (SourcePairedInclusion.data q hq n r).X (fsLin q hq n r x + fiLin ci dci x)) =
      inclSolution q hq n r ci dci b x := by
  have hd := SourcePairedInclusion.disjoint q hq n r ci b hb.le hci
  have hfs0 : StaticCoefficient.sqrtMultiplier ci (fsLin q hq n r x) = 0 :=
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero ci (SourcePairedInclusion.shell q hq n r)
      hd.symm (RestrictedTEPlaneLocal.electric x) _ (fs_isDatum q hq n r x)
  have hfi0 : StaticCoefficient.sqrtMultiplier (SourcePairedInclusion.shell q hq n r) (fiLin ci dci x) = 0 :=
    SourcePairedPlaneIdentification.sqrtMultiplier_isDatum_zero (SourcePairedInclusion.shell q hq n r) ci hd
      (RestrictedTEPlaneLocal.electric x) _ (fi_isDatum ci dci x)
  exact SourcePairedPlaneIdentification.inclPart_eq_effective q hq n r ci b hb hci hE (fsLin q hq n r x)
    (fiLin ci dci x) hfi0 hfs0

end InclPart

end OQ14.RestrictedTEActualPiecewise
#print axioms OQ14.RestrictedTEActualPiecewise.piecewiseE_apply_lt
#print axioms OQ14.RestrictedTEActualPiecewise.piecewiseE_apply_ge
#print axioms OQ14.RestrictedTEActualPiecewise.piecewiseE_meas
#print axioms OQ14.RestrictedTEActualPiecewise.piecewise_flux_lt
#print axioms OQ14.RestrictedTEActualPiecewise.piecewise_flux_ge
#print axioms OQ14.RestrictedTEActualPiecewise.tail_of_two_majorants
#print axioms OQ14.RestrictedTEActualPiecewise.piecewise_agreeE
#print axioms OQ14.RestrictedTEActualPiecewise.piecewise_agreeH
#print axioms OQ14.RestrictedTEActualPiecewise.coreAgreement_of_out
#print axioms OQ14.RestrictedTEActualPiecewise.decomp_mono
#print axioms OQ14.RestrictedTEActualPiecewise.outside_majorant_of_decomp
#print axioms OQ14.RestrictedTEActualPiecewise.outside_decomp_of_sum
#print axioms OQ14.RestrictedTEActualPiecewise.teCoeff_not_mem
#print axioms OQ14.RestrictedTEActualPiecewise.teCoeff_comb
#print axioms OQ14.RestrictedTEActualPiecewise.famSum_extend
#print axioms OQ14.RestrictedTEActualPiecewise.famSum_comb
#print axioms OQ14.RestrictedTEActualPiecewise.bgFieldE_comb
#print axioms OQ14.RestrictedTEActualPiecewise.bgFieldH_comb
#print axioms OQ14.RestrictedTEActualPiecewise.bgFieldE_zero
#print axioms OQ14.RestrictedTEActualPiecewise.bgFieldH_zero
#print axioms OQ14.RestrictedTEActualPiecewise.background_decomp_span
#print axioms OQ14.RestrictedTEActualPiecewise.background_decomp_unit_sphere
#print axioms OQ14.RestrictedTEActualPiecewise.inclSolution_comb
#print axioms OQ14.RestrictedTEActualPiecewise.inclSolution_zero
#print axioms OQ14.RestrictedTEActualPiecewise.solution_bounded_of_coeffs
#print axioms OQ14.RestrictedTEActualPiecewise.solution_bounded_on_sphere
#print axioms OQ14.RestrictedTEActualPiecewise.outside_majorant_of_pieces
#print axioms OQ14.RestrictedTEActualPiecewise.actual_counted_subspaces_of_pieces
#print axioms OQ14.RestrictedTEActualPiecewise.tail_field_of_two_majorants
#print axioms OQ14.RestrictedTEActualPiecewise.inclPart_eq_inclSolution
