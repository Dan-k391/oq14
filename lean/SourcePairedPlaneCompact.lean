import SourcePairedReactionField
import SourcePairedParityClosure

/-! Plane fields of the actual finite paired shells on compact sets: the free dyadic potential and the
shell-reaction field of the effective inclusion solutions converge uniformly on compacts at positive
distance from the carrier to the parity-device plane field with gain parameter q^n, and the effective
inclusion block of a half-turn symmetric inclusion commutes with the half-turn action. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourcePairedPlaneCompact
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.HalfTurnVectorAction OQ14.HalfTurnParityEquivariance
open scoped Topology
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Operator := VectorL2 →L[ℂ] VectorL2
abbrev Space := Maxwell.Space

/-- The effective inclusion block of the actual paired shell at shell index `r`: the own dynamic volume
block of the inclusion at radius `b` minus the inclusion-weighted shell reaction operator. -/
abbrev effectiveBlock (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ) : Operator :=
  DynamicVolume.volumeBlock ci 1 b - ShellInclusionReaction.reaction (SourcePairedInclusion.shell q hq n r) ci 1
    (SourcePairedInclusion.data q hq n r).X

/-- The plane electric field assembled from the actual finite paired-shell data: incident field, free
dyadic potential of the inclusion source, and the literal shell-reaction field. -/
def pairedPlaneElectric (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (u : VectorL2)
    (inc : Maxwell.Field) : Maxwell.Field :=
  fun x i => inc x i + ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x i +
    SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X u x i

/-! ### Part B: the free dyadic potential at positive distance from the carrier -/

theorem source_mem_carrier (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (v : VectorL2)
    (j : Fin 3) (y : Space) (h : DynamicVolume.source ci v j y ≠ 0) : y ∈ d.carrier := by
  by_contra hy
  exact h (by simp [DynamicVolume.source, d.carrierZero y hy])

theorem response_sub_bound (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
    (K : Space → ℂ) (hK : Measurable K) (C : ℝ) (hC0 : 0 ≤ C) (x : Space)
    (hC : ∀ y ∈ d.carrier, ‖K (x - y)‖ ≤ C) (u v : VectorL2) (j : Fin 3) :
    ‖KernelConvolution.response K (DynamicVolume.source ci u j) x -
        KernelConvolution.response K (DynamicVolume.source ci v j) x‖ ≤
      C * ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u - v‖) := by
  have hu := DynamicVolume.source_integrable ci u d.radius d.ballZero j
  have hv := DynamicVolume.source_integrable ci v d.radius d.ballZero j
  have hw := DynamicVolume.source_integrable ci (u - v) d.radius d.ballZero j
  have hbu : ∀ y, DynamicVolume.source ci u j y ≠ 0 → ‖K (x - y)‖ ≤ C :=
    fun y hy => hC y (source_mem_carrier ci d u j y hy)
  have hbv : ∀ y, DynamicVolume.source ci v j y ≠ 0 → ‖K (x - y)‖ ≤ C :=
    fun y hy => hC y (source_mem_carrier ci d v j y hy)
  have hbw : ∀ y, DynamicVolume.source ci (u - v) j y ≠ 0 → ‖K (x - y)‖ ≤ C :=
    fun y hy => hC y (source_mem_carrier ci d (u - v) j y hy)
  have e : KernelConvolution.response K (DynamicVolume.source ci u j) x -
      KernelConvolution.response K (DynamicVolume.source ci v j) x =
      KernelConvolution.response K (DynamicVolume.source ci (u - v) j) x := by
    unfold KernelConvolution.response
    rw [← integral_sub (ScalarRadiation.source_integrand_integrable K _ hK hu x C hbu)
      (ScalarRadiation.source_integrand_integrable K _ hK hv x C hbv)]
    apply integral_congr_ae
    filter_upwards [SourcePairedReactionField.source_sub_ae ci u v j] with y hy
    rw [hy]
    ring
  rw [e]
  have h1 := ScalarRadiation.response_norm_bound K _ hK hw x C hbw
  have h2 := SourcePairedReactionField.source_mass' ci d (u - v) j
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)

/-- Lipschitz bound of the free dyadic potential in the weighted vector, uniform over all points at
distance at least `η` from the carrier. -/
theorem electric_sub_bound (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (η : ℝ) (hη : 0 < η)
    (x : Space) (hx : ∀ y ∈ d.carrier, η ≤ ‖x - y‖) (u v : VectorL2) (i : Fin 3) :
    ‖ExteriorContinuity.electric 1 (DynamicVolume.source ci u) x i -
        ExteriorContinuity.electric 1 (DynamicVolume.source ci v) x i‖ ≤
      3 * (NewtonStripMaxwell.electricBound 1 (2 * η) *
        ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u - v‖)) := by
  simp only [ExteriorContinuity.electric]
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  have hC0 : 0 ≤ NewtonStripMaxwell.electricBound 1 (2 * η) := by
    unfold NewtonStripMaxwell.electricBound NewtonStripMaxwell.remainderBound
    positivity
  have h2η : 0 < 2 * η := by linarith
  have h : ∀ j : Fin 3, ‖KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source ci u j) x -
      KernelConvolution.response (fun z => DyadicKernel.dyadic 1 z i j)
        (DynamicVolume.source ci v j) x‖ ≤
      NewtonStripMaxwell.electricBound 1 (2 * η) *
        ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u - v‖) := fun j =>
    response_sub_bound ci d (fun z => DyadicKernel.dyadic 1 z i j) (PlaneSourceKernel.dyadic_measurable 1 i j)
      _ hC0 x (fun y hy => NewtonStripMaxwell.electric_bound 1 (2 * η) h2η (x - y)
        (by have := hx y hy; linarith) i j) u v j
  calc _ ≤ ∑ _j : Fin 3, NewtonStripMaxwell.electricBound 1 (2 * η) *
        ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u - v‖) :=
      Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp

theorem free_electric_tendsto_uniform (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
    (η : ℝ) (hη : 0 < η) (u : ℕ → VectorL2) (u0 : VectorL2) (hu : Tendsto u atTop (𝓝 u0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖ExteriorContinuity.electric 1 (DynamicVolume.source ci (u r)) x i -
        ExteriorContinuity.electric 1 (DynamicVolume.source ci u0) x i‖ ≤ ε := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 3 * (NewtonStripMaxwell.electricBound 1 (2 * η) *
      (Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier))) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ NewtonStripMaxwell.electricBound 1 (2 * η) := by
      unfold NewtonStripMaxwell.electricBound NewtonStripMaxwell.remainderBound
      positivity
    positivity
  have hpos : 0 < ε / (M + 1) := by positivity
  have hev := (Metric.tendsto_nhds.mp hu) (ε / (M + 1)) hpos
  filter_upwards [hev] with r hr x hx i
  have h1 := electric_sub_bound ci d η hη x hx (u r) u0 i
  have h2 : ‖u r - u0‖ ≤ ε / (M + 1) := by
    have := hr
    rw [dist_eq_norm] at this
    exact this.le
  have h3 : 3 * (NewtonStripMaxwell.electricBound 1 (2 * η) *
      ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u r - u0‖)) = M * ‖u r - u0‖ := by
    rw [hM]
    ring
  rw [h3] at h1
  refine h1.trans ?_
  calc M * ‖u r - u0‖ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left h2 hM0
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

/-! ### Part C: the assembled plane electric field on compacts at positive distance from the carrier -/

section Convergence
variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) (hsym : Symmetric ci)
include hb hcar hsym

/-- The shell-reaction field of the effective inclusion solutions of half-turn-fixed data converges
uniformly on balls to the parity combination of the plane reaction fields of the parity solution. -/
theorem reactionField_tendsto_parity (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
    (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n))) (f : VectorL2) (hf : U f = f) (ρ0 : ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X (Ring.inverse (effectiveBlock q hq n r ci b) f) x i -
        ((((q ^ (2 * n) : ℝ) : ℂ) - 1) * ParityPlaneFields.electric true 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i +
          ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * ParityPlaneFields.electric false 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i)‖ ≤ ε := by
  have hlim := SourcePairedParityClosure.paired_shell_solutions_tendsto_parity q hq n ci d b hb hcar hsym
    hL hu f hf
  filter_upwards [SourcePairedReactionField.reactionField_tendsto_uniform_compact q hq n ci d b hcar ρ0
    _ _ hlim ε hε] with r hr x hx i
  have hl := SourcePairedReactionField.limitField_eq_parity q n ci
    (ParityMaterialField.solution d 1 (q ^ n) f) d.radius d.ballZero
    (SourcePairedParityClosure.source_invariantAE_of_fixed ci hsym d (q ^ n) hu f hf) x i
  rw [← hl]
  exact hr x hx i

/-- Uniform convergence on compacts at positive distance from the carrier of the assembled plane
electric field of the effective inclusion solutions to the parity-device total electric field with
gain parameter `q ^ n`. -/
theorem pairedPlaneElectric_tendsto_uniform
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
    (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n))) (f : VectorL2) (hf : U f = f)
    (inc : Maxwell.Field) (ρ0 η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖pairedPlaneElectric q hq n r ci (Ring.inverse (effectiveBlock q hq n r ci b) f) inc x i -
        ParityPlaneFields.totalElectric 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) inc x i‖ ≤ ε := by
  have hlim := SourcePairedParityClosure.paired_shell_solutions_tendsto_parity q hq n ci d b hb hcar hsym
    hL hu f hf
  have hA := reactionField_tendsto_parity q hq n ci d b hb hcar hsym hL hu f hf ρ0 (ε / 2) (half_pos hε)
  have hB := free_electric_tendsto_uniform ci d η hη
    (fun r => Ring.inverse (effectiveBlock q hq n r ci b) f) _ hlim (ε / 2) (half_pos hε)
  filter_upwards [hA, hB] with r hr hfree x hx hxη i
  have e1 : ((q ^ n) ^ 2 : ℝ) = q ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have e2 : ((q ^ n)⁻¹ ^ 2 : ℝ) = (q ^ (2 * n))⁻¹ := by rw [inv_pow, e1]
  have key : pairedPlaneElectric q hq n r ci (Ring.inverse (effectiveBlock q hq n r ci b) f) inc x i -
        ParityPlaneFields.totalElectric 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) inc x i =
      (ExteriorContinuity.electric 1 (DynamicVolume.source ci (Ring.inverse (effectiveBlock q hq n r ci b) f)) x i -
        ExteriorContinuity.electric 1
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i) +
      (SourcePairedReactionField.reactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X (Ring.inverse (effectiveBlock q hq n r ci b) f) x i -
        ((((q ^ (2 * n) : ℝ) : ℂ) - 1) * ParityPlaneFields.electric true 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i +
          ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * ParityPlaneFields.electric false 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i)) := by
    unfold pairedPlaneElectric ParityPlaneFields.totalElectric
    rw [e1, e2]
    push_cast
    ring
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hfree x hxη i) (hr x hx i)
    _ = ε := by ring

end Convergence

/-! ### Part A: half-turn invariance of the actual effective inclusion solutions -/

theorem coefficient_symmetric (d : SourceRadialSystem.Data) (M : ℝ) (hM : 1 ≤ M)
    (hs : ∀ g ∈ d.gs, 1 ≤ g.σ ∧ g.σ ≤ M) :
    Symmetric (SourceMaterialCoefficient.coefficient d M hM hs) := by
  intro x
  rw [SourceMaterialCoefficient.value_physical, SourceMaterialCoefficient.value_physical]
  unfold SourceMaterialCoefficient.susceptibility
  rw [rot.norm_map]

/-- The actual radial paired-shell coefficient is half-turn symmetric. -/
theorem shell_symmetric (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) :
    Symmetric (SourcePairedInclusion.shell q hq n r) :=
  coefficient_symmetric _ _ _ _

/-- The operator commutes with the half-turn action. -/
def HalfTurnComm (A : Operator) : Prop := ∀ u : VectorL2, U (A u) = A (U u)

theorem HalfTurnComm.mul {A B : Operator} (hA : HalfTurnComm A) (hB : HalfTurnComm B) :
    HalfTurnComm (A * B) := by
  intro u
  simp only [ContinuousLinearMap.mul_apply]
  rw [hA, hB]

theorem HalfTurnComm.sub {A B : Operator} (hA : HalfTurnComm A) (hB : HalfTurnComm B) :
    HalfTurnComm (A - B) := by
  intro u
  simp only [ContinuousLinearMap.sub_apply, map_sub]
  rw [hA, hB]

theorem halfTurnComm_one : HalfTurnComm (1 : Operator) := by
  intro u
  simp

/-- The ring inverse of an operator commuting with the half-turn action commutes with it. -/
theorem HalfTurnComm.inverse {A : Operator} (hA : HalfTurnComm A) : HalfTurnComm (Ring.inverse A) := by
  by_cases hu : IsUnit A
  · intro u
    have h1 : ∀ v, A (Ring.inverse A v) = v := fun v =>
      congrArg (fun L : Operator => L v) (Ring.mul_inverse_cancel A hu)
    have h2 : ∀ v, Ring.inverse A (A v) = v := fun v =>
      congrArg (fun L : Operator => L v) (Ring.inverse_mul_cancel A hu)
    have h3 : A (U (Ring.inverse A u)) = U u := by rw [← hA, h1]
    calc U (Ring.inverse A u) = Ring.inverse A (A (U (Ring.inverse A u))) := (h2 _).symm
      _ = Ring.inverse A (U u) := by rw [h3]
  · intro u
    rw [Ring.inverse_non_unit A hu]
    simp

/-- Almost-everywhere form of the sandwiched truncated dyadic operator with two different weights. -/
theorem actual2 (a b : Coefficient) (u : VectorL2) (k R : ℝ)
    (ha : ∀ x : Space, x ∉ closedBall 0 R → a.value (VectorFourier.coordinateMap x) = 0)
    (hb : ∀ x : Space, x ∉ closedBall 0 R → b.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => StaticCoefficient.sqrtMultiplier a (DynamicConvolution.operator k (2 * R)
        (StaticCoefficient.sqrtMultiplier b u)) (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (a.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x - y) i j * DynamicVolume.source b u j y := by
  have hs := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae a
      (DynamicConvolution.operator k (2 * R) (StaticCoefficient.sqrtMultiplier b u)))
  have hd := DynamicConvolution.operator_ae_convolution k (2 * R) (StaticCoefficient.sqrtMultiplier b u)
    (StaticNewton.material_source_integrable b u (closedBall 0 R) (isCompact_closedBall 0 R) hb) i
  filter_upwards [hs, hd] with x hx hy
  change (StaticCoefficient.sqrtMultiplier a (DynamicConvolution.operator k (2 * R)
    (StaticCoefficient.sqrtMultiplier b u))) (VectorFourier.coordinateMap x) i = _
  rw [hx]
  change (Real.sqrt (a.value (VectorFourier.coordinateMap x)) : ℂ) *
    (DynamicConvolution.operator k (2 * R) (StaticCoefficient.sqrtMultiplier b u))
      (VectorFourier.coordinateMap x) i = _
  rw [hy]
  by_cases hxb : x ∈ closedBall (0 : Space) R
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [DynamicVolume.truncated_source_convolution]
    apply integral_congr_ae
    filter_upwards with y
    exact DynamicVolume.kernel_source_eq b u k R hb i j x y hxb
  · simp [ha x hxb]

/-- Abstract equivariance of kernel operators of the form `S_a K S_b` with two symmetric weights. -/
theorem kernel_comm2 (a b : Coefficient) (ha : Symmetric a) (hb : Symmetric b)
    (T : VectorL2 →L[ℂ] VectorL2) (K : Space → Space → Fin 3 → Fin 3 → ℂ)
    (hK : ∀ x y i j, K (rot x) (rot y) i j = (o i : ℂ) * (o j : ℂ) * K x y i j)
    (hT : ∀ u i, (fun x => T u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (a.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3, ∫ y, K x y i j * DynamicVolume.source b u j y) (u : VectorL2) :
    U (T u) = T (U u) := by
  apply vector_ext_pt
  intro i
  have I1 (x : Space) (j : Fin 3) : (∫ y, K (rot x) y i j * DynamicVolume.source b u j y) =
      (o i : ℂ) * (o j : ℂ) * ∫ y, K x (rot y) i j * DynamicVolume.source b u j y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have := hK x (rot y) i j
    rw [rot_rot] at this
    rw [this]
    ring
  have I2 (x : Space) (j : Fin 3) : (∫ y, K x y i j * DynamicVolume.source b (U u) j y) =
      (o j : ℂ) * ∫ y, K x (rot y) i j * DynamicVolume.source b u j y := by
    have h3 : (∫ y, K x y i j * DynamicVolume.source b (U u) j y) =
        ∫ y, (o j : ℂ) * (K x y i j * DynamicVolume.source b u j (rot y)) := by
      apply integral_congr_ae
      filter_upwards [source_U b hb u j] with y hy
      rw [hy]
      ring
    have h4 := rot_mp.integral_comp rot.toHomeomorph.measurableEmbedding
      (fun y' => K x (rot y') i j * DynamicVolume.source b u j y')
    simp only [rot_rot] at h4
    rw [h3, integral_const_mul]
    congr 1
  filter_upwards [U_ae (T u) i, ae_rot (hT u i), hT (U u) i] with x h1 h2 h3
  rw [h1, h3, h2, ha x]
  simp only [I1, I2]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have := o_sq_c i
  linear_combination ((Real.sqrt (a.value (VectorFourier.coordinateMap x)) : ℂ) * (o j : ℂ) *
    ∫ y, K x (rot y) i j * DynamicVolume.source b u j y) * this

/-- The off-diagonal and diagonal weighted blocks `S_a K S_b` of the coefficient-independent
dynamic-minus-static kernel commute with the half-turn action. -/
theorem sandwich_comm (a b : Coefficient) (ha : Symmetric a) (hb : Symmetric b) (k R : ℝ)
    (hsa : ∀ x : Space, x ∉ closedBall 0 R → a.value (VectorFourier.coordinateMap x) = 0)
    (hsb : ∀ x : Space, x ∉ closedBall 0 R → b.value (VectorFourier.coordinateMap x) = 0) :
    HalfTurnComm (StaticCoefficient.sqrtMultiplier a * ShellInclusionVolume.kernel k R *
      StaticCoefficient.sqrtMultiplier b) := by
  intro u
  have hT := kernel_comm2 a b ha hb
    (StaticCoefficient.sqrtMultiplier a ∘L DynamicConvolution.operator k (2 * R) ∘L
      StaticCoefficient.sqrtMultiplier b)
    (fun x y i j => DyadicKernel.remainder k (x - y) i j)
    (fun x y i j => by
      show DyadicKernel.remainder k (rot x - rot y) i j =
        (o i : ℂ) * (o j : ℂ) * DyadicKernel.remainder k (x - y) i j
      rw [← map_sub]
      exact remainder_rot k (x - y) i j)
    (fun u i => actual2 a b u k R hsa hsb i) u
  simp only [ContinuousLinearMap.comp_apply] at hT
  simp only [ContinuousLinearMap.mul_apply, ShellInclusionVolume.kernel, ContinuousLinearMap.sub_apply,
    map_sub]
  rw [hT, sqrtMultiplier_comm a ha, U_physicalProjection, sqrtMultiplier_comm b hb]

theorem volumeBlock_comm (c : Coefficient) (hc : Symmetric c) (k R : ℝ)
    (hR : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) :
    HalfTurnComm (DynamicVolume.volumeBlock c k R) := by
  rw [ShellInclusionVolume.volumeBlock_eq_sandwich]
  exact halfTurnComm_one.sub (sandwich_comm c c hc hc k R hR hR)

/-- The inclusion-weighted shell reaction operator of half-turn symmetric shell and inclusion with
supports in the ball of radius `R` commutes with the half-turn action. -/
theorem reaction_comm (cs ci : Coefficient) (hs : Symmetric cs) (hi : Symmetric ci) (k R : ℝ)
    (hcs : ∀ x : Space, x ∉ closedBall 0 R → cs.value (VectorFourier.coordinateMap x) = 0)
    (hci : ∀ x : Space, x ∉ closedBall 0 R → ci.value (VectorFourier.coordinateMap x) = 0) :
    HalfTurnComm (ShellInclusionReaction.reaction cs ci k R) := by
  have e : ShellInclusionReaction.reaction cs ci k R =
      (StaticCoefficient.sqrtMultiplier ci * ShellInclusionVolume.kernel k R *
          StaticCoefficient.sqrtMultiplier cs) *
        Ring.inverse (DynamicVolume.volumeBlock cs k R) *
        (StaticCoefficient.sqrtMultiplier cs * ShellInclusionVolume.kernel k R *
          StaticCoefficient.sqrtMultiplier ci) := by
    unfold ShellInclusionReaction.reaction ShellInclusionReaction.scatteredGreen
    simp only [mul_assoc]
  rw [e]
  exact ((sandwich_comm ci cs hi hs k R hci hcs).mul (volumeBlock_comm cs hs k R hcs).inverse).mul
    (sandwich_comm cs ci hs hi k R hcs hci)

theorem invariantAE_of_fixed (ci : Coefficient) (hsym : Symmetric ci) (v : VectorL2) (hv : U v = v) :
    HalfTurnReactionBridgeAE.InvariantAE (SourcePairedWallKernelAE.sourceField ci v) := by
  intro j
  filter_upwards [source_invariant_ae ci hsym v hv j] with y hy
  simp only [SourcePairedWallKernelAE.sourceField]
  rw [← HalfTurnReactionKernel.rotation_eq]
  change DynamicVolume.source ci v j (rot y) = _
  rw [hy]
  simp only [o]
  push_cast
  ring

section Paired
variable (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (b : ℝ)
  (hsym : Symmetric ci) (hb : b ≤ (SourcePairedInclusion.data q hq n r).R)
  (hci : ∀ x : Space, x ∉ closedBall 0 b → ci.value (VectorFourier.coordinateMap x) = 0)
include hsym hb hci

/-- The effective inclusion block of the actual paired shell commutes with the half-turn action. -/
theorem effectiveBlock_comm : HalfTurnComm (effectiveBlock q hq n r ci b) :=
  (volumeBlock_comm ci hsym 1 b hci).sub
    (reaction_comm _ ci (shell_symmetric q hq n r) hsym 1 _
      (fun x hx => SourcePairedInclusion.shell_support q hq n r x hx)
      (fun x hx => SourcePairedInclusion.inclusion_support q hq n r ci b hb hci x hx))

/-- The effective inclusion solution of half-turn-fixed data is half-turn fixed. -/
theorem effective_solution_fixed (f : VectorL2) (hf : U f = f) :
    U (Ring.inverse (effectiveBlock q hq n r ci b) f) = Ring.inverse (effectiveBlock q hq n r ci b) f := by
  rw [(effectiveBlock_comm q hq n r ci b hsym hb hci).inverse f, hf]

/-- Hence the weighted source of the effective inclusion solution is almost everywhere half-turn
invariant. -/
theorem effective_solution_invariantAE (f : VectorL2) (hf : U f = f) :
    HalfTurnReactionBridgeAE.InvariantAE (SourcePairedWallKernelAE.sourceField ci
      (Ring.inverse (effectiveBlock q hq n r ci b) f)) :=
  invariantAE_of_fixed ci hsym _ (effective_solution_fixed q hq n r ci b hsym hb hci f hf)

end Paired

theorem eventually_effective_solution_invariantAE (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b)
    (hsym : Symmetric ci) (f : VectorL2) (hf : U f = f) :
    ∀ᶠ r : ℕ in atTop,
      U (Ring.inverse (effectiveBlock q hq n r ci b) f) = Ring.inverse (effectiveBlock q hq n r ci b) f ∧
        HalfTurnReactionBridgeAE.InvariantAE (SourcePairedWallKernelAE.sourceField ci
          (Ring.inverse (effectiveBlock q hq n r ci b) f)) := by
  filter_upwards [SourcePairedReduction.eventually_inner_radius q hq n b] with r hr
  have hci := SourcePairedReduction.inclusion_vanish ci d b hcar
  exact ⟨effective_solution_fixed q hq n r ci b hsym hr.le hci f hf,
    effective_solution_invariantAE q hq n r ci b hsym hr.le hci f hf⟩

/-! ### Part D: the magnetic side

The free magnetic potential of the inclusion source is controlled exactly like the electric one.  No
magnetic analogue of the shell reaction kernel exists in the tree (see the review), so the assembled
magnetic field is only given as a conditional interface in which the magnetic shell-reaction field
family is an explicit hypothesis. -/

/-- Lipschitz bound of the free magnetic potential in the weighted vector, uniform over all points at
distance at least `η` from the carrier. -/
theorem magnetic_sub_bound (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (η : ℝ) (hη : 0 < η)
    (x : Space) (hx : ∀ y ∈ d.carrier, η ≤ ‖x - y‖) (u v : VectorL2) (i : Fin 3) :
    ‖MagneticResponse.magnetic 1 (DynamicVolume.source ci u) x i -
        MagneticResponse.magnetic 1 (DynamicVolume.source ci v) x i‖ ≤
      2 * (NewtonStripMaxwell.gradientBound 1 (2 * η) *
        ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u - v‖)) := by
  have hC0 : 0 ≤ NewtonStripMaxwell.gradientBound 1 (2 * η) := by
    unfold NewtonStripMaxwell.gradientBound
    positivity
  have h2η : 0 < 2 * η := by linarith
  have hA := response_sub_bound ci d (fun z => GreenKernel.phiGradient 1 z (WeakCurl.next i))
    (KernelGradient.gradient_measurable 1 (WeakCurl.next i)) _ hC0 x
    (fun y hy => NewtonStripMaxwell.gradient_bound 1 (2 * η) h2η (x - y)
      (by have := hx y hy; linarith) (WeakCurl.next i)) u v (WeakCurl.previous i)
  have hB := response_sub_bound ci d (fun z => GreenKernel.phiGradient 1 z (WeakCurl.previous i))
    (KernelGradient.gradient_measurable 1 (WeakCurl.previous i)) _ hC0 x
    (fun y hy => NewtonStripMaxwell.gradient_bound 1 (2 * η) h2η (x - y)
      (by have := hx y hy; linarith) (WeakCurl.previous i)) u v (WeakCurl.next i)
  simp only [MagneticResponse.magnetic]
  rw [← mul_sub, norm_mul]
  have hn : ‖-(Complex.I * ((1 : ℝ) : ℂ))‖ = 1 := by simp
  rw [hn, one_mul]
  have e : (KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.next i))
        (DynamicVolume.source ci u (WeakCurl.previous i)) x -
      KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.previous i))
        (DynamicVolume.source ci u (WeakCurl.next i)) x) -
      (KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.next i))
        (DynamicVolume.source ci v (WeakCurl.previous i)) x -
      KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.previous i))
        (DynamicVolume.source ci v (WeakCurl.next i)) x) =
      (KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.next i))
        (DynamicVolume.source ci u (WeakCurl.previous i)) x -
      KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.next i))
        (DynamicVolume.source ci v (WeakCurl.previous i)) x) -
      (KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.previous i))
        (DynamicVolume.source ci u (WeakCurl.next i)) x -
      KernelConvolution.response (fun z => GreenKernel.phiGradient 1 z (WeakCurl.previous i))
        (DynamicVolume.source ci v (WeakCurl.next i)) x) := by ring
  rw [e]
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ _ := add_le_add hA hB
    _ = _ := by ring

theorem free_magnetic_tendsto_uniform (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
    (η : ℝ) (hη : 0 < η) (u : ℕ → VectorL2) (u0 : VectorL2) (hu : Tendsto u atTop (𝓝 u0))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖MagneticResponse.magnetic 1 (DynamicVolume.source ci (u r)) x i -
        MagneticResponse.magnetic 1 (DynamicVolume.source ci u0) x i‖ ≤ ε := by
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * (NewtonStripMaxwell.gradientBound 1 (2 * η) *
      (Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier))) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by
    rw [hM]
    have : 0 ≤ NewtonStripMaxwell.gradientBound 1 (2 * η) := by
      unfold NewtonStripMaxwell.gradientBound
      positivity
    positivity
  have hpos : 0 < ε / (M + 1) := by positivity
  have hev := (Metric.tendsto_nhds.mp hu) (ε / (M + 1)) hpos
  filter_upwards [hev] with r hr x hx i
  have h1 := magnetic_sub_bound ci d η hη x hx (u r) u0 i
  have h2 : ‖u r - u0‖ ≤ ε / (M + 1) := by
    have := hr
    rw [dist_eq_norm] at this
    exact this.le
  have h3 : 2 * (NewtonStripMaxwell.gradientBound 1 (2 * η) *
      ((Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u r - u0‖)) = M * ‖u r - u0‖ := by
    rw [hM]
    ring
  rw [h3] at h1
  refine h1.trans ?_
  calc M * ‖u r - u0‖ ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left h2 hM0
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith

/-- Conditional magnetic assembly.  The hypothesis `hM` (uniform convergence on balls of a family `M r`
of magnetic shell-reaction fields to the parity combination of the plane magnetic reaction fields) is
exactly the part for which no magnetic paired-shell kernel exists in the tree; given it, the assembled
magnetic field converges uniformly on compacts at positive distance from the carrier to the parity
total magnetic field. -/
theorem pairedPlaneMagnetic_tendsto_of_reaction (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (inc : Maxwell.Field) (B : ℝ)
    (u : ℕ → VectorL2) (u0 : VectorL2) (hu : Tendsto u atTop (𝓝 u0)) (M : ℕ → Maxwell.Field)
    (ρ0 η : ℝ) (hη : 0 < η)
    (hM : ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖M r x i - (((B ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic true 1 (DynamicVolume.source ci u0) x i +
        ((B⁻¹ ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic false 1 (DynamicVolume.source ci u0) x i)‖ ≤ ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖(inc x i + MagneticResponse.magnetic 1 (DynamicVolume.source ci (u r)) x i + M r x i) -
        ParityPlaneFields.totalMagnetic 1 B (DynamicVolume.source ci u0) inc x i‖ ≤ ε := by
  have hB := free_magnetic_tendsto_uniform ci d η hη u u0 hu (ε / 2) (half_pos hε)
  filter_upwards [hM (ε / 2) (half_pos hε), hB] with r hr hfree x hx hxη i
  have key : (inc x i + MagneticResponse.magnetic 1 (DynamicVolume.source ci (u r)) x i + M r x i) -
      ParityPlaneFields.totalMagnetic 1 B (DynamicVolume.source ci u0) inc x i =
      (MagneticResponse.magnetic 1 (DynamicVolume.source ci (u r)) x i -
        MagneticResponse.magnetic 1 (DynamicVolume.source ci u0) x i) +
      (M r x i - (((B ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic true 1 (DynamicVolume.source ci u0) x i +
        ((B⁻¹ ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic false 1 (DynamicVolume.source ci u0) x i)) := by
    unfold ParityPlaneFields.totalMagnetic
    ring
  rw [key]
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add (hfree x hxη i) (hr x hx i)
    _ = ε := by ring

end OQ14.SourcePairedPlaneCompact
#print axioms OQ14.SourcePairedPlaneCompact.source_mem_carrier
#print axioms OQ14.SourcePairedPlaneCompact.response_sub_bound
#print axioms OQ14.SourcePairedPlaneCompact.electric_sub_bound
#print axioms OQ14.SourcePairedPlaneCompact.free_electric_tendsto_uniform
#print axioms OQ14.SourcePairedPlaneCompact.reactionField_tendsto_parity
#print axioms OQ14.SourcePairedPlaneCompact.pairedPlaneElectric_tendsto_uniform
#print axioms OQ14.SourcePairedPlaneCompact.coefficient_symmetric
#print axioms OQ14.SourcePairedPlaneCompact.shell_symmetric
#print axioms OQ14.SourcePairedPlaneCompact.HalfTurnComm.mul
#print axioms OQ14.SourcePairedPlaneCompact.HalfTurnComm.sub
#print axioms OQ14.SourcePairedPlaneCompact.halfTurnComm_one
#print axioms OQ14.SourcePairedPlaneCompact.HalfTurnComm.inverse
#print axioms OQ14.SourcePairedPlaneCompact.actual2
#print axioms OQ14.SourcePairedPlaneCompact.kernel_comm2
#print axioms OQ14.SourcePairedPlaneCompact.sandwich_comm
#print axioms OQ14.SourcePairedPlaneCompact.volumeBlock_comm
#print axioms OQ14.SourcePairedPlaneCompact.reaction_comm
#print axioms OQ14.SourcePairedPlaneCompact.invariantAE_of_fixed
#print axioms OQ14.SourcePairedPlaneCompact.effectiveBlock_comm
#print axioms OQ14.SourcePairedPlaneCompact.effective_solution_fixed
#print axioms OQ14.SourcePairedPlaneCompact.effective_solution_invariantAE
#print axioms OQ14.SourcePairedPlaneCompact.eventually_effective_solution_invariantAE
#print axioms OQ14.SourcePairedPlaneCompact.magnetic_sub_bound
#print axioms OQ14.SourcePairedPlaneCompact.free_magnetic_tendsto_uniform
#print axioms OQ14.SourcePairedPlaneCompact.pairedPlaneMagnetic_tendsto_of_reaction
