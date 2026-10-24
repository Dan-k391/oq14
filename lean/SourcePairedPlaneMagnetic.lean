import SourcePairedPlaneCompact

/-! The magnetic side of the compact plane-field convergence of the actual finite paired shells: the
shell magnetic reaction kernel and field, the curl identity for the shell electric reaction kernel in the
hollow core, the first-order jet convergence of the paired kernels, the identification of the limit with
the parity magnetic reaction fields, and the assembled magnetic plane field. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace OQ14.SourcePairedPlaneMagnetic
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

section S0
open MeasureTheory Set Metric Filter OQ14.Maxwell
open OQ14.SphereReactionKernel OQ14.SphereAngularSymmetry OQ14.SphereWaveCalculus
open OQ14.HalfTurnMaxwellParity OQ14.HalfTurnReactionKernel OQ14.HalfTurnReactionBridge
open OQ14.HalfTurnReactionBridgeAE
open scoped Topology InnerProductSpace

/-! ### The magnetic tensor `K`: oddness and half-turn covariance -/

theorem K_neg (k : ℝ) (x : Space) (i j : Fin 3) :
    SphereMagneticKernel.K k (-x) i j = -SphereMagneticKernel.K k x i j := by
  let L := LinearIsometryEquiv.neg ℝ (E := Space)
  have ha (θ : Sphere) : SphereMagneticKernel.transverse i j (sphereMap L θ) =
      -SphereMagneticKernel.transverse i j θ := by
    unfold SphereMagneticKernel.transverse SphereWaveCalculus.coordinate
    change ((-θ.val (WeakCurl.next i) : ℝ) : ℂ) * _ - ((-θ.val (WeakCurl.previous i) : ℝ) : ℂ) * _ = _
    push_cast
    ring
  have hw (θ : Sphere) : wave k (-x) (sphereMap L θ) = wave k x θ := by
    unfold wave
    change Complex.exp (((k * ⟪-θ.val, -x⟫_ℝ : ℝ) : ℂ) * Complex.I) = _
    rw [inner_neg_neg]
  have hc := (measurePreserving_sphereMap L).integral_comp (sphereMap L).measurableEmbedding
    (fun θ => SphereMagneticKernel.transverse i j θ * wave k (-x) θ)
  change (∫ θ : Sphere, SphereMagneticKernel.transverse i j (sphereMap L θ) *
    wave k (-x) (sphereMap L θ) ∂surface) = _ at hc
  simp only [ha, hw, neg_mul, integral_neg] at hc
  change -(∫ θ : Sphere, SphereMagneticKernel.transverse i j θ * wave k x θ ∂surface) =
    ∫ θ : Sphere, SphereMagneticKernel.transverse i j θ * wave k (-x) θ ∂surface at hc
  unfold SphereMagneticKernel.K moment
  rw [← hc]
  ring

theorem K_rotation (k : ℝ) (x : Space) (i j : Fin 3) :
    SphereMagneticKernel.K k (HarmonicHalfTurn.rotation x) i j =
      (sign i : ℂ) * (sign j : ℂ) * SphereMagneticKernel.K k x i j := by
  have ha (θ : Sphere) : SphereMagneticKernel.transverse i j (sphereMap HarmonicHalfTurn.rotation θ) =
      (sign i : ℂ) * (sign j : ℂ) * SphereMagneticKernel.transverse i j θ := by
    unfold SphereMagneticKernel.transverse SphereWaveCalculus.coordinate
    change ((HarmonicHalfTurn.rotation θ.val (WeakCurl.next i) : ℝ) : ℂ) * _ -
      ((HarmonicHalfTurn.rotation θ.val (WeakCurl.previous i) : ℝ) : ℂ) * _ = _
    simp only [rotation_coordinate, Complex.ofReal_mul, Complex.ofReal_neg]
    fin_cases i <;> fin_cases j <;> simp [sign, WeakCurl.next, WeakCurl.previous]
  have hw (θ : Sphere) : wave k (HarmonicHalfTurn.rotation x) (sphereMap HarmonicHalfTurn.rotation θ) =
      wave k x θ := by
    unfold wave
    congr 3
    exact congrArg (fun t : ℝ => k * t) (HarmonicHalfTurn.rotation.inner_map_map θ x)
  have hc := (measurePreserving_sphereMap HarmonicHalfTurn.rotation).integral_comp
    (sphereMap HarmonicHalfTurn.rotation).measurableEmbedding
    (fun θ => SphereMagneticKernel.transverse i j θ * wave k (HarmonicHalfTurn.rotation x) θ)
  change (∫ θ : Sphere, SphereMagneticKernel.transverse i j (sphereMap HarmonicHalfTurn.rotation θ) *
    wave k (HarmonicHalfTurn.rotation x) (sphereMap HarmonicHalfTurn.rotation θ) ∂surface) = _ at hc
  simp only [ha, hw, mul_assoc, integral_const_mul] at hc
  change (sign i : ℂ) * ((sign j : ℂ) * (∫ θ : Sphere, SphereMagneticKernel.transverse i j θ *
    wave k x θ ∂surface)) = ∫ θ : Sphere, SphereMagneticKernel.transverse i j θ *
      wave k (HarmonicHalfTurn.rotation x) θ ∂surface at hc
  unfold SphereMagneticKernel.K moment
  rw [← hc]
  ring

/-! ### The magnetic potential, the central and wall magnetic integrals -/

/-- The volume potential of the magnetic tensor `K`. -/
def magPotential (k : ℝ) (ρ : Maxwell.Field) : Maxwell.Field := fun x i =>
  ∑ j : Fin 3, ∫ y : Space, SphereMagneticKernel.K k (x - y) i j * ρ y j

theorem integrable_K (k : ℝ) (ρ : Maxwell.Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (x : Space) (i j : Fin 3) :
    Integrable (fun y => SphereMagneticKernel.K k (x - y) i j * ρ y j) :=
  (hρ j).bdd_mul ((SphereMagneticKernel.K_continuous k i j).comp
    (continuous_const.sub continuous_id)).aestronglyMeasurable
    ⟨entryBound k, fun _ => SphereMagneticKernel.K_bound k _ i j⟩

theorem integrable_K_add (k : ℝ) (ρ : Maxwell.Field) (hρ : ∀ j, Integrable (fun y => ρ y j))
    (x : Space) (i j : Fin 3) :
    Integrable (fun y => SphereMagneticKernel.K k (x + y) i j * ρ y j) :=
  (hρ j).bdd_mul ((SphereMagneticKernel.K_continuous k i j).comp
    (continuous_const.add continuous_id)).aestronglyMeasurable
    ⟨entryBound k, fun _ => SphereMagneticKernel.K_bound k _ i j⟩

theorem magPotential_invariant_ae (k : ℝ) (ρ : Maxwell.Field) (hρ : InvariantAE ρ) :
    Invariant (magPotential k ρ) := by
  intro x i
  change (∑ j : Fin 3, ∫ y : Space, SphereMagneticKernel.K k (halfTurn x - y) i j * ρ y j) = _
  have he (j : Fin 3) : (∫ y : Space, SphereMagneticKernel.K k (halfTurn x - y) i j * ρ y j) =
      -(sign i : ℂ) * (∫ y : Space, SphereMagneticKernel.K k (x - y) i j * ρ y j) := by
    have hc := HarmonicHalfTurn.rotation.measurePreserving.integral_comp
      HarmonicHalfTurn.rotation.toHomeomorph.measurableEmbedding
      (fun y : Space => SphereMagneticKernel.K k (halfTurn x - y) i j * ρ y j)
    rw [← hc, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hρ j] with y hy
    rw [← rotation_eq, ← map_sub, K_rotation, rotation_eq, hy]
    have hs : (sign j : ℂ) ^ 2 = 1 := by unfold sign; split_ifs <;> norm_num
    linear_combination -((sign i : ℂ) * SphereMagneticKernel.K k (x - y) i j * ρ y j) * hs
  simp_rw [he]
  rw [← Finset.mul_sum]
  rfl

theorem magPotential_neg (k : ℝ) (ρ : Maxwell.Field) (x : Space) (i : Fin 3) :
    magPotential k ρ (-x) i = -∑ j : Fin 3, ∫ y : Space, SphereMagneticKernel.K k (x + y) i j * ρ y j := by
  unfold magPotential
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards with y
  rw [show -x - y = -(x + y) by abel, K_neg]
  ring

/-- Central-inversion magnetic kernel: the curl image of the central electric kernel. -/
def centralMag (e : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) : ℂ :=
  (Complex.I / 2) * (SphereMagneticKernel.K k (x - y) i j +
    (if e then 1 else -1 : ℂ) * SphereMagneticKernel.K k (x + y) i j)

theorem integrable_centralMag (e : Bool) (k : ℝ) (ρ : Maxwell.Field)
    (hρ : ∀ j, Integrable (fun y => ρ y j)) (x : Space) (i j : Fin 3) :
    Integrable (fun y => centralMag e k x y i j * ρ y j) := by
  have h1 := integrable_K k ρ hρ x i j
  have h2 := integrable_K_add k ρ hρ x i j
  have : (fun y => centralMag e k x y i j * ρ y j) = fun y =>
      (Complex.I / 2) * (SphereMagneticKernel.K k (x - y) i j * ρ y j) +
        ((Complex.I / 2) * (if e then 1 else -1 : ℂ)) * (SphereMagneticKernel.K k (x + y) i j * ρ y j) := by
    funext y
    simp only [centralMag]
    ring
  rw [this]
  exact (h1.const_mul _).add (h2.const_mul _)

theorem centralMag_integral (e : Bool) (k : ℝ) (ρ : Maxwell.Field)
    (hρ : ∀ j, Integrable (fun y => ρ y j)) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, centralMag e k x y i j * ρ y j) =
      (Complex.I / 2) * (magPotential k ρ x i -
        (if e then 1 else -1 : ℂ) * magPotential k ρ (-x) i) := by
  have he (j : Fin 3) : (∫ y : Space, centralMag e k x y i j * ρ y j) =
      (Complex.I / 2) * ((∫ y : Space, SphereMagneticKernel.K k (x - y) i j * ρ y j) +
        (if e then 1 else -1 : ℂ) * (∫ y : Space, SphereMagneticKernel.K k (x + y) i j * ρ y j)) := by
    have hp := integrable_K_add k ρ hρ x i j
    simp_rw [centralMag, mul_assoc, add_mul]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_add (integrable_K k ρ hρ x i j) (hp.const_mul _), integral_const_mul]
  simp_rw [he]
  rw [magPotential_neg]
  unfold magPotential
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem wallMag_integral (e : Bool) (k : ℝ) (ρ : Maxwell.Field)
    (hρ : ∀ j, Integrable (fun y => ρ y j)) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, SphereMagneticParity.magneticReaction e k x y i j * ρ y j) =
      (Complex.I / 2) * (magPotential k ρ x i -
        (if e then -1 else 1 : ℂ) * (sign i : ℂ) * magPotential k ρ (reflect x) i) := by
  have he (j : Fin 3) : (∫ y : Space, SphereMagneticParity.magneticReaction e k x y i j * ρ y j) =
      (Complex.I / 2) * ((∫ y : Space, SphereMagneticKernel.K k (x - y) i j * ρ y j) -
        ((if e then -1 else 1 : ℂ) * (sign i : ℂ)) *
          (∫ y : Space, SphereMagneticKernel.K k (reflect x - y) i j * ρ y j)) := by
    simp_rw [SphereMagneticParity.magneticReaction, mul_assoc, sub_mul]
    simp_rw [mul_assoc]
    rw [integral_const_mul, integral_sub (integrable_K k ρ hρ x i j)
      (((integrable_K k ρ hρ (reflect x) i j).const_mul _).const_mul _), integral_const_mul,
      integral_const_mul]
  simp_rw [he]
  unfold magPotential
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]

theorem centralMag_eq_wall_ae (e : Bool) (k : ℝ) (ρ : Maxwell.Field)
    (hρ : ∀ j, Integrable (fun y => ρ y j)) (hs : InvariantAE ρ) (x : Space) (i : Fin 3) :
    (∑ j : Fin 3, ∫ y : Space, centralMag e k x y i j * ρ y j) =
      ∑ j : Fin 3, ∫ y : Space, SphereMagneticParity.magneticReaction e k x y i j * ρ y j := by
  rw [centralMag_integral e k ρ hρ, wallMag_integral e k ρ hρ,
    inversion_wall _ (magPotential_invariant_ae k ρ hs)]
  cases e <;> simp

/-! ### The limit magnetic kernel and its parity identification -/

/-- The limiting magnetic kernel of the paired shells. -/
def limitMagKernel (q : ℝ) (n : ℕ) (x y : Space) (i j : Fin 3) : ℂ :=
  (((q ^ (2 * n) : ℝ) : ℂ) - 1) * centralMag true 1 x y i j +
    ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * centralMag false 1 x y i j

/-- The magnetic field of the limiting kernel. -/
def limitMagField (q : ℝ) (n : ℕ) (ci : Coefficient) (u : VectorL2) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y : Space, limitMagKernel q n x y i j * DynamicVolume.source ci u j y

/-- On almost-everywhere half-turn invariant sources the limit magnetic field is the gain combination
`(q^(2n)-1) * magnetic true + (q^(-2n)-1) * magnetic false` of the parity wall magnetic reaction fields. -/
theorem limitMagField_eq_parity (q : ℝ) (n : ℕ) (ci : Coefficient) (u : VectorL2) (b : ℝ)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (hinv : InvariantAE (SourcePairedWallKernelAE.sourceField ci u)) (x : Space) (i : Fin 3) :
    limitMagField q n ci u x i =
      (((q ^ (2 * n) : ℝ) : ℂ) - 1) * ParityPlaneFields.magnetic true 1 (DynamicVolume.source ci u) x i +
        ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) *
          ParityPlaneFields.magnetic false 1 (DynamicVolume.source ci u) x i := by
  have hρ : ∀ j, Integrable (fun y => SourcePairedWallKernelAE.sourceField ci u y j) := fun j =>
    DynamicVolume.source_integrable ci u b hci j
  have hlin : limitMagField q n ci u x i =
      (((q ^ (2 * n) : ℝ) : ℂ) - 1) * (∑ j : Fin 3, ∫ y : Space,
        centralMag true 1 x y i j * SourcePairedWallKernelAE.sourceField ci u y j) +
      ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * (∑ j : Fin 3, ∫ y : Space,
        centralMag false 1 x y i j * SourcePairedWallKernelAE.sourceField ci u y j) := by
    unfold limitMagField
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have i1 := integrable_centralMag true 1 _ hρ x i j
    have i2 := integrable_centralMag false 1 _ hρ x i j
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (i1.const_mul _) (i2.const_mul _)]
    apply integral_congr_ae
    filter_upwards with y
    simp only [limitMagKernel, SourcePairedWallKernelAE.sourceField]
    ring
  rw [hlin, centralMag_eq_wall_ae true 1 _ hρ hinv x i, centralMag_eq_wall_ae false 1 _ hρ hinv x i]
  rfl

/-! ### The curl of the limit electric kernel is `I` times the limit magnetic kernel -/

theorem J_differentiableAt (k : ℝ) (x : Space) (i j : Fin 3) :
    DifferentiableAt ℝ (fun z => J k z i j) x := by
  have ha : Continuous (fun θ : Sphere => amplitude θ i j) :=
    continuous_const.sub ((coordinate_continuous i).mul (coordinate_continuous j))
  exact ((moment_hasFDerivAt _ ha 2 (fun θ => amplitude_bound θ i j) k x).const_mul _).differentiableAt

theorem dcoord_sub_const (f : Space → ℂ) (y x : Space) (c : Fin 3) :
    dcoord (fun x' => f (x' - y)) x c = dcoord f (x - y) c := by
  unfold dcoord
  have : (fun x' => f (x' - y)) = fun x' => f (x' + -y) := by
    funext x'
    rw [sub_eq_add_neg]
  rw [this, fderiv_comp_add_right]
  rw [sub_eq_add_neg]

theorem dcoord_add_const (f : Space → ℂ) (y x : Space) (c : Fin 3) :
    dcoord (fun x' => f (x' + y)) x c = dcoord f (x + y) c := by
  unfold dcoord
  rw [fderiv_comp_add_right]

theorem curl_eq (F : Space → Fin 3 → ℂ) (w : Space) (i : Fin 3) :
    curl F w i = dcoord (fun z => F z (WeakCurl.previous i)) w (WeakCurl.next i) -
      dcoord (fun z => F z (WeakCurl.next i)) w (WeakCurl.previous i) := by
  fin_cases i <;> rfl

theorem central_differentiableAt (e : Bool) (y : Space) (a j : Fin 3) (x : Space) :
    DifferentiableAt ℝ (fun x' => central e 1 x' y a j) x := by
  have h1 : DifferentiableAt ℝ (fun x' => J 1 (x' - y) a j) x :=
    DifferentiableAt.comp (g := fun z => J 1 z a j) x (J_differentiableAt 1 (x - y) a j)
      (differentiableAt_id.sub_const y)
  have h2 : DifferentiableAt ℝ (fun x' => J 1 (x' + y) a j) x :=
    DifferentiableAt.comp (g := fun z => J 1 z a j) x (J_differentiableAt 1 (x + y) a j)
      (differentiableAt_id.add_const y)
  unfold central
  exact (h1.add (h2.const_mul _)).const_mul _

theorem dcoord_central (e : Bool) (y : Space) (a j : Fin 3) (x : Space) (c : Fin 3) :
    dcoord (fun x' => central e 1 x' y a j) x c = (Complex.I / 2) *
      (dcoord (fun z => J 1 z a j) (x - y) c +
        (if e then 1 else -1 : ℂ) * dcoord (fun z => J 1 z a j) (x + y) c) := by
  have h1 : DifferentiableAt ℝ (fun x' => J 1 (x' - y) a j) x :=
    DifferentiableAt.comp (g := fun z => J 1 z a j) x (J_differentiableAt 1 (x - y) a j)
      (differentiableAt_id.sub_const y)
  have h2 : DifferentiableAt ℝ (fun x' => J 1 (x' + y) a j) x :=
    DifferentiableAt.comp (g := fun z => J 1 z a j) x (J_differentiableAt 1 (x + y) a j)
      (differentiableAt_id.add_const y)
  have hc : (fun x' => central e 1 x' y a j) = fun x' => (Complex.I / 2) *
      (J 1 (x' - y) a j + (if e then 1 else -1 : ℂ) * J 1 (x' + y) a j) := rfl
  rw [hc, partial_const_mul (h1.add (h2.const_mul _)), partial_add h1 (h2.const_mul _),
    partial_const_mul h2, dcoord_sub_const (fun z => J 1 z a j), dcoord_add_const (fun z => J 1 z a j)]

theorem central_curl (e : Bool) (y x : Space) (i j : Fin 3) :
    dcoord (fun x' => central e 1 x' y (WeakCurl.previous i) j) x (WeakCurl.next i) -
      dcoord (fun x' => central e 1 x' y (WeakCurl.next i) j) x (WeakCurl.previous i) =
        Complex.I * centralMag e 1 x y i j := by
  rw [dcoord_central, dcoord_central]
  have h1 := SphereMagneticKernel.curl_J 1 (x - y) i j
  have h2 := SphereMagneticKernel.curl_J 1 (x + y) i j
  rw [curl_eq] at h1 h2
  unfold centralMag
  simp only [Complex.ofReal_one, mul_one] at h1 h2
  linear_combination (Complex.I / 2) * h1 + (Complex.I / 2) * (if e then 1 else -1 : ℂ) * h2

/-- The curl in the first variable of the limit electric kernel is `I` times the limit magnetic kernel. -/
theorem limit_kernel_curl (q : ℝ) (n : ℕ) (x y : Space) (i j : Fin 3) :
    dcoord (fun x' => VectorLimitIdentification.kernel q n (WeakCurl.previous i) j (x', y)) x
        (WeakCurl.next i) -
      dcoord (fun x' => VectorLimitIdentification.kernel q n (WeakCurl.next i) j (x', y)) x
        (WeakCurl.previous i) = Complex.I * limitMagKernel q n x y i j := by
  have hk (a : Fin 3) : (fun x' => VectorLimitIdentification.kernel q n a j (x', y)) = fun x' =>
      (((q ^ (2 * n) : ℝ) : ℂ) - 1) * central true 1 x' y a j +
        ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * central false 1 x' y a j := by
    funext x'
    exact paired_kernel q n x' y a j
  rw [hk, hk]
  have d1 (a : Fin 3) := central_differentiableAt true y a j x
  have d2 (a : Fin 3) := central_differentiableAt false y a j x
  rw [partial_add ((d1 _).const_mul _) ((d2 _).const_mul _), partial_const_mul (d1 _),
    partial_const_mul (d2 _), partial_add ((d1 _).const_mul _) ((d2 _).const_mul _),
    partial_const_mul (d1 _), partial_const_mul (d2 _)]
  have c1 := central_curl true y x i j
  have c2 := central_curl false y x i j
  unfold limitMagKernel
  linear_combination (((q ^ (2 * n) : ℝ) : ℂ) - 1) * c1 + ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * c2

end S0

section S1
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.GreenKernel OQ14.KernelConvolution
open scoped Topology

/-! ### Differentiation under the integral for a source in a shell and an observation point in its hole -/

theorem hollow_bound (q : Space → ℂ) (L : Space → Space →L[ℝ] ℂ)
    (hq : ∀ z, z ≠ 0 → ContinuousAt q z) (hL : ∀ z, z ≠ 0 → ContinuousAt L z)
    (R1 R2 : ℝ) (x : Space) (hx : ‖x‖ < R1) :
    ∃ a B : ℝ, 0 < a ∧ ∀ z ∈ ball x a, ∀ y : Space, R1 ≤ ‖y‖ → ‖y‖ ≤ R2 →
      z - y ≠ 0 ∧ ‖L (z - y)‖ ≤ B ∧ ‖q (z - y)‖ ≤ B := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (R1 - ‖x‖) / 2 := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha]; linarith
  have hsep (z y : Space) (hz : z ∈ closedBall x a) (hy : R1 ≤ ‖y‖) : a ≤ ‖z - y‖ := by
    have hd : ‖x - z‖ ≤ a := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    have h1 := norm_sub_norm_le y z
    have h2 := norm_sub_norm_le z x
    rw [norm_sub_rev] at h2 h1
    linarith
  have hK : IsCompact (closedBall x a ×ˢ (closedBall (0 : Space) R2 \ ball (0 : Space) R1)) :=
    (isCompact_closedBall x a).prod ((isCompact_closedBall (0 : Space) R2).diff isOpen_ball)
  have hne (p : Space × Space) (hp : p ∈ closedBall x a ×ˢ (closedBall (0 : Space) R2 \ ball (0 : Space) R1)) :
      p.1 - p.2 ≠ 0 := by
    have hy : R1 ≤ ‖p.2‖ := by
      have := hp.2.2
      simpa only [mem_ball, dist_zero_right, not_lt] using this
    exact norm_pos_iff.mp (hapos.trans_le (hsep p.1 p.2 hp.1 hy))
  have hcL : ContinuousOn (fun p : Space × Space => L (p.1 - p.2))
      (closedBall x a ×ˢ (closedBall (0 : Space) R2 \ ball (0 : Space) R1)) := by
    intro p hp
    exact ((hL (p.1 - p.2) (hne p hp)).comp (f := fun r : Space × Space => r.1 - r.2)
      (continuous_fst.sub continuous_snd).continuousAt).continuousWithinAt
  have hcq : ContinuousOn (fun p : Space × Space => q (p.1 - p.2))
      (closedBall x a ×ˢ (closedBall (0 : Space) R2 \ ball (0 : Space) R1)) := by
    intro p hp
    exact ((hq (p.1 - p.2) (hne p hp)).comp (f := fun r : Space × Space => r.1 - r.2)
      (continuous_fst.sub continuous_snd).continuousAt).continuousWithinAt
  obtain ⟨B1, hB1⟩ := hK.exists_bound_of_continuousOn hcL
  obtain ⟨B2, hB2⟩ := hK.exists_bound_of_continuousOn hcq
  refine ⟨a, max B1 B2, hapos, fun z hz y hy1 hy2 => ?_⟩
  have hzc : z ∈ closedBall x a := ball_subset_closedBall hz
  have hyc : y ∈ closedBall (0 : Space) R2 \ ball (0 : Space) R1 := by
    refine ⟨?_, ?_⟩
    · simpa only [mem_closedBall, dist_zero_right] using hy2
    · simpa only [mem_ball, dist_zero_right, not_lt] using hy1
  have hp : (z, y) ∈ closedBall x a ×ˢ (closedBall (0 : Space) R2 \ ball (0 : Space) R1) := ⟨hzc, hyc⟩
  exact ⟨hne (z, y) hp, (hB1 (z, y) hp).trans (le_max_left _ _), (hB2 (z, y) hp).trans (le_max_right _ _)⟩

theorem response_hasFDerivAt_hollow (q : Space → ℂ) (L : Space → Space →L[ℝ] ℂ)
    (hq : Measurable q) (hLm : Measurable L)
    (hL : ∀ z, z ≠ 0 → ContinuousAt L z)
    (hd : ∀ z, z ≠ 0 → HasFDerivAt q (L z) z)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (R1 R2 : ℝ)
    (hc : ∀ y, ρ y ≠ 0 → R1 ≤ ‖y‖ ∧ ‖y‖ ≤ R2) (x : Space) (hx : ‖x‖ < R1) :
    Integrable (fun y => ρ y • L (x - y)) ∧
      HasFDerivAt (response q ρ) (∫ y, ρ y • L (x - y)) x := by
  obtain ⟨a, B, ha, hB⟩ := hollow_bound q L (fun z hz => (hd z hz).continuousAt) hL R1 R2 x hx
  have hm (z : Space) : AEStronglyMeasurable (fun y => ρ y • L (z - y)) :=
    hρ.aestronglyMeasurable.smul
      (hLm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hb (y z : Space) (hz : z ∈ ball x a) : ‖ρ y • L (z - y)‖ ≤ ‖ρ y‖ * B := by
    rw [_root_.norm_smul (ρ y) (L (z - y))]
    by_cases hy : ρ y = 0
    · simp [hy]
    · exact mul_le_mul_of_nonneg_left ((hB z hz y (hc y hy).1 (hc y hy).2).2.1.trans (le_refl B))
        (norm_nonneg _)
  have hi : Integrable (fun y => ρ y • L (x - y)) :=
    (hρ.norm.mul_const B).mono' (hm x) (Eventually.of_forall (fun y => hb y x (mem_ball_self ha)))
  have hiq : Integrable (fun y => ρ y * q (x - y)) := by
    apply (hρ.norm.mul_const B).mono'
      (hρ.aestronglyMeasurable.mul (hq.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    filter_upwards with y
    by_cases hy : ρ y = 0
    · simp [hy]
    · show ‖ρ y * q (x - y)‖ ≤ ‖ρ y‖ * B
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB x (mem_ball_self ha) y (hc y hy).1 (hc y hy).2).2.2
        (norm_nonneg _)
  refine ⟨hi, ?_⟩
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z y => ρ y * q (z - y))
    (F' := fun z y => ρ y • L (z - y))
    (bound := fun y => ‖ρ y‖ * B) ha
  · exact Eventually.of_forall (fun z => hρ.aestronglyMeasurable.mul
      (hq.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
  · exact hiq
  · exact hm x
  · exact Eventually.of_forall (fun y z hz => hb y z hz)
  · exact hρ.norm.mul_const B
  · filter_upwards with y
    intro z hz
    by_cases hy : ρ y = 0
    · simp only [hy, zero_mul]
      have hz0 : (0 : ℂ) • L (z - y) = (0 : Space →L[ℝ] ℂ) :=
        _root_.zero_smul ℂ (L (z - y))
      rw [hz0]
      exact hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) z
    · have h := (hd (z - y) (hB z hz y (hc y hy).1 (hc y hy).2).1).comp z
        ((hasFDerivAt_id z).sub_const y)
      simpa only [ContinuousLinearMap.comp_id] using h.const_mul (ρ y)

/-- Differentiation under the integral sign for a source supported in the shell `R1 <= |z| <= R2` at an
observation point `x` in the hole `|x| < R1`: the response is differentiable and its partial derivatives
are the responses of the partial derivatives of the kernel. -/
theorem response_dcoord_hollow (q : Space → ℂ) (hq : Measurable q)
    (hqs : ∀ z, z ≠ 0 → ContDiffAt ℝ (⊤ : ℕ∞) q z)
    (ρ : Space → ℂ) (hρ : Integrable ρ) (R1 R2 : ℝ)
    (hc : ∀ y, ρ y ≠ 0 → R1 ≤ ‖y‖ ∧ ‖y‖ ≤ R2) (x : Space) (hx : ‖x‖ < R1) (c : Fin 3) :
    Integrable (fun y => ρ y * dcoord q (x - y) c) ∧ DifferentiableAt ℝ (response q ρ) x ∧
      dcoord (response q ρ) x c = ∫ y, ρ y * dcoord q (x - y) c := by
  have hd : ∀ z, z ≠ 0 → HasFDerivAt q (fderiv ℝ q z) z := fun z hz =>
    ((hqs z hz).differentiableAt (by simp)).hasFDerivAt
  have hL : ∀ z, z ≠ 0 → ContinuousAt (fderiv ℝ q) z := fun z hz =>
    ((hqs z hz).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuousAt
  obtain ⟨hi, hfd⟩ := response_hasFDerivAt_hollow q (fderiv ℝ q) hq (measurable_fderiv ℝ q) hL hd ρ hρ
    R1 R2 hc x hx
  have hev : Integrable (fun y => (ρ y • fderiv ℝ q (x - y)) (basis c)) :=
    (ContinuousLinearMap.apply ℝ ℂ (basis c)).integrable_comp hi
  have e : (fun y => (ρ y • fderiv ℝ q (x - y)) (basis c)) = fun y => ρ y * dcoord q (x - y) c := by
    funext y
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rfl
  rw [e] at hev
  refine ⟨hev, hfd.differentiableAt, ?_⟩
  unfold dcoord
  rw [hfd.fderiv, ContinuousLinearMap.integral_apply hi]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### The curl of the free dyadic is the magnetic dyadic -/

theorem dcoord_dyadic (k : ℝ) (w : Space) (hw : w ≠ 0) (a h c : Fin 3) :
    dcoord (fun z => DyadicKernel.dyadic k z a h) w c =
      (k : ℂ) ^ 2 * (if a = h then 1 else 0 : ℂ) * phiGradient k w c +
        dcoord (fun z => phiHessian k z a h) w c := by
  have hp : DifferentiableAt ℝ (phi k) w := (phi_contDiffAt k w hw).differentiableAt (by simp)
  have hH : DifferentiableAt ℝ (fun z => phiHessian k z a h) w :=
    (ExteriorSmooth.hessian_contDiffAt k a h w hw).differentiableAt (by simp)
  have e : (fun z => DyadicKernel.dyadic k z a h) =
      fun z => ((k : ℂ) ^ 2 * (if a = h then 1 else 0 : ℂ)) * phi k z + phiHessian k z a h := by
    funext z
    unfold DyadicKernel.dyadic
    ring
  rw [e, partial_add (hp.const_mul _) hH, partial_const_mul hp, phi_partial k w hw c]

theorem hessian_partial_symm (k : ℝ) (w : Space) (hw : w ≠ 0) (a h c : Fin 3) :
    dcoord (fun z => phiHessian k z a h) w c = dcoord (fun z => phiHessian k z c h) w a := by
  have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => phiGradient k y h) w :=
    ExteriorSmooth.gradient_contDiffAt k h w hw
  have e (b : Fin 3) : (fun z => phiHessian k z b h) =ᶠ[nhds w]
      fun z => dcoord (fun y => phiGradient k y h) z b := by
    filter_upwards [eventually_ne_nhds hw] with z hz
    exact (phiGradient_partial k z hz b h).symm
  have e1 : dcoord (fun z => phiHessian k z a h) w c =
      dcoord (fun z => dcoord (fun y => phiGradient k y h) z a) w c := by
    change (fderiv ℝ (fun z => phiHessian k z a h) w) (basis c) =
      (fderiv ℝ (fun z => dcoord (fun y => phiGradient k y h) z a) w) (basis c)
    rw [(e a).fderiv_eq]
  have e2 : dcoord (fun z => phiHessian k z c h) w a =
      dcoord (fun z => dcoord (fun y => phiGradient k y h) z c) w a := by
    change (fderiv ℝ (fun z => phiHessian k z c h) w) (basis a) =
      (fderiv ℝ (fun z => dcoord (fun y => phiGradient k y h) z c) w) (basis a)
    rw [(e c).fderiv_eq]
  rw [e1, e2]
  exact ExteriorClassical.partial_comm_at hg c a

theorem dyadic_curl (k : ℝ) (w : Space) (hw : w ≠ 0) (i h : Fin 3) :
    dcoord (fun z => DyadicKernel.dyadic k z (WeakCurl.previous i) h) w (WeakCurl.next i) -
      dcoord (fun z => DyadicKernel.dyadic k z (WeakCurl.next i) h) w (WeakCurl.previous i) =
        (Complex.I * (k : ℂ)) * SphereMagneticKernel.magneticDyadic k w i h := by
  rw [dcoord_dyadic k w hw, dcoord_dyadic k w hw,
    hessian_partial_symm k w hw (WeakCurl.previous i) h (WeakCurl.next i)]
  unfold SphereMagneticKernel.magneticDyadic
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  linear_combination ((k : ℂ) ^ 2 * (phiGradient k w (WeakCurl.next i) *
    (if WeakCurl.previous i = h then (1 : ℂ) else 0) -
      phiGradient k w (WeakCurl.previous i) * (if WeakCurl.next i = h then (1 : ℂ) else 0))) * hI


/-! ### The shell magnetic reaction kernel and the curl of the shell electric reaction kernel -/

/-- The shell magnetic reaction kernel: the magnetic dyadic integral of the shell polarization of the
shell solution driven by the free field of the dipole column `(y,j)`; the exact magnetic counterpart of
`ShellReactionIdentification.reactionKernel`. -/
def magneticReactionKernel (cs : Coefficient) (R Rin X : ℝ) (x y : Space) (i j : Fin 3) : ℂ :=
  ∑ h : Fin 3, ∫ z : Space, DynamicVolume.source cs
    (Ring.inverse (DynamicVolume.volumeBlock cs 1 R) (ShellReactionIdentification.freeDatum cs Rin X y j)) h z *
      SphereMagneticKernel.magneticDyadic 1 (x - z) i h

/-- The shell magnetic reaction field of a weighted vector `u` of the inclusion. -/
def magneticReactionField (cs ci : Coefficient) (R Rin X : ℝ) (u : VectorL2) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y : Space, magneticReactionKernel cs R Rin X x y i j * DynamicVolume.source ci u j y

theorem magnetic_eq_sum (k : ℝ) (ρ : Fin 3 → Space → ℂ) (x : Space) (i : Fin 3) :
    MagneticResponse.magnetic k ρ x i =
      ∑ h : Fin 3, ∫ z : Space, ρ h z * SphereMagneticKernel.magneticDyadic k (x - z) i h := by
  have aux (r g : Space → ℂ) (c : ℂ) : (∫ z, r z * (c * g z)) = c * ∫ z, r z * g z := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  fin_cases i <;>
    simp [MagneticResponse.magnetic, SphereMagneticKernel.magneticDyadic, WeakCurl.next, WeakCurl.previous,
      Fin.sum_univ_three, response, integral_neg, aux] <;> ring

theorem dcoord_sum {f : Fin 3 → Space → ℂ} {x : Space} (hf : ∀ h, DifferentiableAt ℝ (f h) x) (c : Fin 3) :
    dcoord (fun x' => ∑ h, f h x') x c = ∑ h, dcoord (f h) x c := by
  have hd : HasFDerivAt (fun x' => ∑ h : Fin 3, f h x') (∑ h : Fin 3, fderiv ℝ (f h) x) x :=
    HasFDerivAt.sum (fun h _ => (hf h).hasFDerivAt)
  unfold dcoord
  rw [hd.fderiv]
  simp [ContinuousLinearMap.sum_apply]

theorem shell_source_support (cs : Coefficient) (X R1 : ℝ)
    (hin : ∀ z : Space, ‖z‖ < R1 → cs.value (VectorFourier.coordinateMap z) = 0)
    (hout : ∀ z : Space, X < ‖z‖ → cs.value (VectorFourier.coordinateMap z) = 0)
    (w : VectorL2) (h : Fin 3) (z : Space) (hz : DynamicVolume.source cs w h z ≠ 0) :
    R1 ≤ ‖z‖ ∧ ‖z‖ ≤ X := by
  constructor
  · by_contra h1
    push_neg at h1
    exact hz (by simp [DynamicVolume.source, hin z h1])
  · by_contra h1
    push_neg at h1
    exact hz (by simp [DynamicVolume.source, hout z h1])

/-- In the hollow core the curl in the first variable of the shell electric reaction kernel is `I` times
the shell magnetic reaction kernel. -/
theorem reactionKernel_curl (cs : Coefficient) (R Rin X R1 : ℝ)
    (hin : ∀ z : Space, ‖z‖ < R1 → cs.value (VectorFourier.coordinateMap z) = 0)
    (hout : ∀ z : Space, X < ‖z‖ → cs.value (VectorFourier.coordinateMap z) = 0)
    (y x : Space) (hx : ‖x‖ < R1) (i j : Fin 3) :
    dcoord (fun x' => ShellReactionIdentification.reactionKernel cs R Rin X x' y (WeakCurl.previous i) j) x
        (WeakCurl.next i) -
      dcoord (fun x' => ShellReactionIdentification.reactionKernel cs R Rin X x' y (WeakCurl.next i) j) x
        (WeakCurl.previous i) = Complex.I * magneticReactionKernel cs R Rin X x y i j := by
  obtain ⟨P, hP⟩ : ∃ P : VectorL2, P = Ring.inverse (DynamicVolume.volumeBlock cs 1 R)
    (ShellReactionIdentification.freeDatum cs Rin X y j) := ⟨_, rfl⟩
  have hcs : ∀ z : Space, z ∉ closedBall (0 : Space) X → cs.value (VectorFourier.coordinateMap z) = 0 := by
    intro z hz
    apply hout
    simpa only [mem_closedBall, dist_zero_right, not_le] using hz
  have hρ (h : Fin 3) : Integrable (DynamicVolume.source cs P h) := DynamicVolume.source_integrable cs P X hcs h
  have hsupp (h : Fin 3) (z : Space) (hz : DynamicVolume.source cs P h z ≠ 0) : R1 ≤ ‖z‖ ∧ ‖z‖ ≤ X :=
    shell_source_support cs X R1 hin hout P h z hz
  have hrk (a : Fin 3) : (fun x' => ShellReactionIdentification.reactionKernel cs R Rin X x' y a j) =
      fun x' => ∑ h : Fin 3, response (fun w => DyadicKernel.dyadic 1 w a h) (DynamicVolume.source cs P h) x' := by
    funext x'
    simp only [ShellReactionIdentification.reactionKernel, response, hP]
  have hdd (a h : Fin 3) := response_dcoord_hollow (fun w => DyadicKernel.dyadic 1 w a h)
    (PlaneSourceKernel.dyadic_measurable 1 a h) (fun z hz => ExteriorSmooth.dyadic_contDiffAt 1 a h z hz)
    (DynamicVolume.source cs P h) (hρ h) R1 X (hsupp h) x hx
  rw [hrk (WeakCurl.previous i), hrk (WeakCurl.next i),
    dcoord_sum (fun h => (hdd (WeakCurl.previous i) h 0).2.1),
    dcoord_sum (fun h => (hdd (WeakCurl.next i) h 0).2.1)]
  unfold magneticReactionKernel
  rw [← hP, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro h _
  rw [(hdd (WeakCurl.previous i) h (WeakCurl.next i)).2.2, (hdd (WeakCurl.next i) h (WeakCurl.previous i)).2.2,
    ← integral_sub (hdd (WeakCurl.previous i) h (WeakCurl.next i)).1
      (hdd (WeakCurl.next i) h (WeakCurl.previous i)).1, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : DynamicVolume.source cs P h z = 0
  · simp [hz]
  · have hw : x - z ≠ 0 := by
      have h1 := (hsupp h z hz).1
      intro h0
      have : x = z := sub_eq_zero.mp h0
      rw [this] at hx
      linarith
    have := dyadic_curl 1 (x - z) hw i h
    simp only [Complex.ofReal_one, mul_one] at this
    rw [← mul_sub, this]
    ring

end S1

section S2
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SourceRadialSystem OQ14.SourcePairedGeometry
open OQ14.RadialFiniteLimit OQ14.RadialPhaseLimit OQ14.HarmonicSpatialMajorant
open OQ14.SourceDielectricModes OQ14.SourceModeDatum OQ14.SphereHarmonicHilbert OQ14.SourceTensorSeries
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

/-! ### Joint differentiability of the actual paired tensor in the core region -/

/-- The physical vector-mode series is differentiable on the open ball on which its first-order
derivative majorant is summable (the first-order companion of `SourceTensorJets.series_derivative`). -/
theorem series_differentiableAt (d : Data) (q M B : ℝ) (hq : 1 ≤ q) (hM : 1 ≤ M)
    (hR : 4 ≤ d.R) (hB : 1 ≤ B) (ht : Real.exp 1 * B ≤ d.R) (hX : d.X ≤ 2 * d.R)
    (hs : ∀ g ∈ d.gs, 1 ≤ g.σ ∧ g.σ ≤ M) (hdisp : ∀ g ∈ d.gs, g.q ^ 2 = g.σ) (hqp : ∀ g ∈ d.gs, g.q ≤ q)
    (b : ℝ) (hb : 0 < b) (hbB : degreeScale (1 + 2) b ≤ B)
    (p : Space × Space) (hp : ‖p‖ < b) (i j : Fin 3) :
    DifferentiableAt ℝ (series d i j) p := by
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have htm (g : RadialStack.Layer) (hg : g ∈ d.gs) : 1 ≤ g.σ ∧ g.σ ≤ M ∧ g.q ^ 2 ≤ M :=
    ⟨(hs g hg).1, (hs g hg).2, by rw [hdisp g hg]; exact (hs g hg).2⟩
  have hte := SourceTensorJets.te_bounds d q M hM hs hdisp hqp
  let C := 2 ^ 1 * (DebyeJetBounds.scale 1 b) ^ 2
  let U := PhysicalReactionSeries.indexMajorant C q M (d.X - d.R) B 6
  have hU : Summable U := PhysicalReactionSeries.indexMajorant_summable C q M (d.X - d.R) B 6
    (by dsimp [C]; positivity) (zero_le_one.trans hB)
  have hbound (s : ℕ) (hsN : s ≤ 1) (a : TotalIndex) (x : Space × Space) (hx : x ∈ ball (0 : Space × Space) b) :
      ‖iteratedFDeriv ℝ s (term d a i j) x‖ ≤ 2 * U a := by
    rw [term, iteratedFDeriv_add_apply
      ((VectorReactionTerms.term_smooth true a i j d.gs d.R d.X d.hR).contDiffAt.of_le (by exact_mod_cast le_top))
      ((VectorReactionTerms.term_smooth false a i j (d.gs.map teLayer) d.R d.X d.hR).contDiffAt.of_le
        (by exact_mod_cast le_top))]
    have h1 := VectorReactionTerms.actual_joint_jet_bound true a i j d.chain q M (d.X - d.R) B
      hq hM0 hR hB ht hX le_rfl htm hqp 1 s hsN b hb.le hbB x (mem_ball_zero_iff.mp hx).le
    have h2 := VectorReactionTerms.actual_joint_jet_bound false a i j (te_chain d.chain) q M (d.X - d.R) B
      hq hM0 hR hB ht hX le_rfl hte.1 hte.2 1 s hsN b hb.le hbB x (mem_ball_zero_iff.mp hx).le
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by
      dsimp [U, PhysicalReactionSeries.indexMajorant, C]
      ring))
  have hu2 : Summable (fun a => 2 * U a) := hU.mul_left 2
  have hf0 : Summable (fun a : TotalIndex => term d a i j 0) := by
    refine Summable.of_norm_bounded _ hu2 (fun a => ?_)
    have := hbound 0 (by norm_num) a 0 (mem_ball_self hb)
    rwa [norm_iteratedFDeriv_zero] at this
  have hd : HasFDerivAt (fun y => ∑' a : TotalIndex, term d a i j y)
      (∑' a : TotalIndex, fderiv ℝ (term d a i j) p) p :=
    hasFDerivAt_tsum_of_isPreconnected (f := fun a => term d a i j)
      (f' := fun a y => fderiv ℝ (term d a i j) y) hu2 isOpen_ball
      (convex_ball (0 : Space × Space) b).isPreconnected
      (fun a y _ => (((SourceTensorJets.term_smooth d a i j).differentiable (by simp)) y).hasFDerivAt)
      (fun a y hy => by
        show ‖fderiv ℝ (term d a i j) y‖ ≤ 2 * U a
        have h := hbound 1 le_rfl a y hy
        rw [← norm_iteratedFDeriv_zero (f := fderiv ℝ (term d a i j)) (x := y) (𝕜 := ℝ),
          norm_iteratedFDeriv_fderiv]
        exact h)
      (mem_ball_self hb) hf0 (mem_ball_zero_iff.mpr hp)
  exact hd.differentiableAt


/-- For large shell index the actual paired tensor is differentiable at every point of the compact
region. -/
theorem eventually_kernel_differentiableAt (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (b : ℝ) (hb : 0 ≤ b)
    (i j : Fin 3) :
    ∀ᶠ r : ℕ in atTop, ∀ p : Region b, DifferentiableAt ℝ (SourcePairedTensor.kernel q hq n r i j) p.val := by
  let B := max 1 (max (degreeScale 2 (b + 1)) (degreeScale 3 (b + 1)))
  let T := max 2 (2 * (B * AngularExteriorBounds.base))
  have hB : 1 ≤ B := le_max_left _ _
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hfB : degreeScale 2 (b + 1) ≤ B := (le_max_left _ _).trans (le_max_right _ _)
  have hdB : degreeScale 3 (b + 1) ≤ B := (le_max_right _ _).trans (le_max_right _ _)
  have hq2 : 1 ≤ q ^ 2 := by nlinarith
  filter_upwards [radius_tendsto.eventually (eventually_ge_atTop (4 : ℝ)),
    radius_tendsto.eventually (eventually_ge_atTop (Real.exp 1 * B)),
    radius_tendsto.eventually
      (eventually_ge_atTop (width (RadialPairedFamily.tm q (zero_lt_one.trans_le hq) n))),
    radius_tendsto.eventually (eventually_gt_atTop T),
    radius_tendsto.eventually (eventually_gt_atTop (b + 1))] with r hR he hwidth hT hbR
  intro p
  let d := physicalData q (zero_lt_one.trans_le hq) n r
  have hmat := physical_material_bounds q (zero_lt_one.trans_le hq) hq n r
  have hdisp := physical_dispersion q (zero_lt_one.trans_le hq) n r
  have hm (x : Space) : ((SourcePairedTensor.material q hq n r).value (VectorFourier.coordinateMap x) : ℂ) =
      sigma d ‖x‖ - 1 :=
    SourceMaterialCoefficient.value_complex d (q ^ 2) hq2 hmat x
  have hu : IsUnit (DynamicVolume.volumeBlock (SourcePairedTensor.material q hq n r) 1 d.X) :=
    SourceMaterialPartition.volumeBlock_isUnit d (q ^ 2) hq2 hmat 1 (by norm_num)
  have hX : d.X ≤ 2 * d.R := by change radius r + width _ ≤ 2 * radius r; linarith
  have hp : ‖p.val‖ < b + 1 := by have h := region_norm b p; linarith
  have hseq := SourceTensorSeries.kernel_eventually_series (SourcePairedTensor.material q hq n r) d hm hdisp hu
    (b + 1) B T (by linarith) hB0 hfB (le_max_left _ _) (le_max_right _ _) hT hbR p.val hp i j
  have hdiff := series_differentiableAt d q (q ^ 2) B hq hq2 hR hB he hX hmat hdisp
    (fun g hg => (physical_parameters q (zero_lt_one.trans_le hq) hq n r g hg).2.2.2) (b + 1) (by linarith)
    hdB p.val hp i j
  exact hdiff.congr_of_eventuallyEq hseq

end S2

section S3
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SphereReactionKernel OQ14.HalfTurnReactionBridge
open OQ14.SourceRadialSystem OQ14.SourcePairedGeometry
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

/-! ### Jets of the actual kernel and the partial derivatives in the first variable -/

theorem jet_one_apply (f : Space × Space → ℂ) (p : Space × Space) (v : Space × Space) :
    iteratedFDeriv ℝ 1 f p (fun _ => v) = fderiv ℝ f p v := by
  rw [iteratedFDeriv_one_apply]

theorem slice_fderiv (f : Space × Space → ℂ) (x y : Space) (hd : DifferentiableAt ℝ f (x, y)) (c : Fin 3) :
    dcoord (fun x' => f (x', y)) x c = fderiv ℝ f (x, y) (basis c, 0) := by
  have h := hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
  unfold dcoord
  have h2 : HasFDerivAt (fun x' => f (x', y))
      ((fderiv ℝ f (x, y)).comp (ContinuousLinearMap.inl ℝ Space Space)) x := h
  rw [h2.fderiv]
  rfl

theorem norm_basis_zero (c : Fin 3) : ‖((basis c, 0) : Space × Space)‖ = 1 := by
  simp [basis]

theorem norm_basis' (c : Fin 3) : ‖basis c‖ = 1 := by
  simp [basis]

theorem jet_bound (J : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => Space × Space) ℂ) (c : Fin 3) :
    ‖J (fun _ => ((basis c, 0) : Space × Space))‖ ≤ ‖J‖ := by
  have := J.le_opNorm (fun _ => ((basis c, 0) : Space × Space))
  simpa [norm_basis'] using this

theorem limit_kernel_differentiableAt (q : ℝ) (n : ℕ) (a j : Fin 3) (p : Space × Space) :
    DifferentiableAt ℝ (VectorLimitIdentification.kernel q n a j) p := by
  have e : VectorLimitIdentification.kernel q n a j = fun p' : Space × Space =>
      (((q ^ (2 * n) : ℝ) : ℂ) - 1) * ((Complex.I / 2) *
        (J 1 (p'.1 - p'.2) a j + (if true then 1 else -1 : ℂ) * J 1 (p'.1 + p'.2) a j)) +
      ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * ((Complex.I / 2) *
        (J 1 (p'.1 - p'.2) a j + (if false then 1 else -1 : ℂ) * J 1 (p'.1 + p'.2) a j)) := by
    funext p'
    exact paired_kernel q n p'.1 p'.2 a j
  have h1 : DifferentiableAt ℝ (fun p' : Space × Space => J 1 (p'.1 - p'.2) a j) p :=
    DifferentiableAt.comp (g := fun z => J 1 z a j) p (J_differentiableAt 1 (p.1 - p.2) a j)
      (differentiableAt_fst.sub differentiableAt_snd)
  have h2 : DifferentiableAt ℝ (fun p' : Space × Space => J 1 (p'.1 + p'.2) a j) p :=
    DifferentiableAt.comp (g := fun z => J 1 z a j) p (J_differentiableAt 1 (p.1 + p.2) a j)
      (differentiableAt_fst.add differentiableAt_snd)
  rw [e]
  exact (((h1.add (h2.const_mul _)).const_mul _).const_mul _).add
    (((h1.add (h2.const_mul _)).const_mul _).const_mul _)

theorem measurable_partial (f : Space × Space → ℂ) (x : Space) (v : Space × Space) :
    Measurable (fun y : Space => fderiv ℝ f (x, y) v) :=
  (ContinuousLinearMap.measurable_apply v).comp
    ((measurable_fderiv ℝ f).comp (measurable_const.prodMk measurable_id))

/-- `I` times the shell magnetic reaction kernel is the curl in the first variable of the paired
tensor, expressed through the first-order partial derivatives of the actual kernel (valid for `x`, `y`
in the open core ball of radius `R_r` when the actual kernel is differentiable at `(x,y)`). -/
theorem magneticReactionKernel_eq_jets (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (x y : Space) (i j : Fin 3)
    (hx : ‖x‖ < (SourcePairedInclusion.data q hq n r).R) (hy : ‖y‖ < (SourcePairedInclusion.data q hq n r).R)
    (hd1 : DifferentiableAt ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.previous i) j) (x, y))
    (hd2 : DifferentiableAt ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.next i) j) (x, y)) :
    Complex.I * magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
        (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
        (SourcePairedInclusion.data q hq n r).X x y i j =
      fderiv ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.previous i) j) (x, y)
          (basis (WeakCurl.next i), 0) -
        fderiv ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.next i) j) (x, y)
          (basis (WeakCurl.previous i), 0) := by
  have hcurl := reactionKernel_curl (SourcePairedInclusion.shell q hq n r)
    (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
    (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
    (fun z hz => SourcePairedInclusion.shell_inner q hq n r z hz.le)
    (fun z hz => SourcePairedInclusion.shell_outer q hq n r z hz) y x hx i j
  have hrk (a : Fin 3) : (fun x' => ShellReactionIdentification.reactionKernel
        (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X x' y a j) =
      fun x' => SourcePairedTensor.kernel q hq n r a j (x', y) := by
    funext x'
    exact SourcePairedReduction.reactionKernel_eq_pairedKernel q hq n r x' y hy a j
  rw [hrk, hrk, slice_fderiv _ x y hd1, slice_fderiv _ x y hd2] at hcurl
  exact hcurl.symm


end S3

section S4
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SphereReactionKernel OQ14.HalfTurnReactionBridge
open OQ14.SourceRadialSystem OQ14.SourcePairedGeometry
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

/-! ### Uniform convergence of the magnetic reaction kernels on compact sets -/

/-- The explicit sup bound of the limiting magnetic kernel. -/
def limF (q : ℝ) (n : ℕ) : ℝ :=
  (‖((q ^ (2 * n) : ℝ) : ℂ) - 1‖ + ‖(((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1‖) * entryBound 1

theorem norm_centralMag_le (e : Bool) (x y : Space) (i j : Fin 3) :
    ‖centralMag e 1 x y i j‖ ≤ entryBound 1 := by
  unfold centralMag
  have h1 := SphereMagneticKernel.K_bound 1 (x - y) i j
  have h2 := SphereMagneticKernel.K_bound 1 (x + y) i j
  have hs : ‖(if e then 1 else -1 : ℂ)‖ = 1 := by cases e <;> norm_num
  have hc : ‖Complex.I / 2‖ = 1 / 2 := by norm_num [norm_div]
  rw [norm_mul, hc]
  have h3 := norm_add_le (SphereMagneticKernel.K 1 (x - y) i j)
    ((if e then 1 else -1 : ℂ) * SphereMagneticKernel.K 1 (x + y) i j)
  rw [norm_mul, hs, one_mul] at h3
  nlinarith

theorem norm_limitMagKernel_le (q : ℝ) (n : ℕ) (x y : Space) (i j : Fin 3) :
    ‖limitMagKernel q n x y i j‖ ≤ limF q n := by
  unfold limitMagKernel limF
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, add_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (norm_centralMag_le true x y i j) (norm_nonneg _))
    (mul_le_mul_of_nonneg_left (norm_centralMag_le false x y i j) (norm_nonneg _))

theorem limitMagKernel_continuous_slice (q : ℝ) (n : ℕ) (x : Space) (i j : Fin 3) :
    Continuous (fun y => limitMagKernel q n x y i j) := by
  have hK1 : Continuous (fun y : Space => SphereMagneticKernel.K 1 (x - y) i j) :=
    (SphereMagneticKernel.K_continuous 1 i j).comp (continuous_const.sub continuous_id)
  have hK2 : Continuous (fun y : Space => SphereMagneticKernel.K 1 (x + y) i j) :=
    (SphereMagneticKernel.K_continuous 1 i j).comp (continuous_const.add continuous_id)
  unfold limitMagKernel centralMag
  fun_prop

/-- The shell magnetic reaction kernels converge uniformly on `{|x| <= rho0} x {|y| <= b}` to the limit
magnetic kernel: the first-order jets of the paired electric kernel converge uniformly
(`SourcePairedTensor.uniform_actual_jet_limit`) and the magnetic kernel is `-I` times their curl. -/
theorem magnetic_kernel_tendsto_uniform_compact (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ρ0 b : ℝ) (ε : ℝ)
    (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x y : Space, ‖x‖ ≤ ρ0 → ‖y‖ ≤ b → ∀ i j : Fin 3,
      ‖magneticReactionKernel (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
          (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X x y i j -
        limitMagKernel q n x y i j‖ ≤ ε := by
  obtain ⟨b', hb'def⟩ : ∃ b' : ℝ, b' = max (max ρ0 b) 1 := ⟨_, rfl⟩
  have hb' : 0 < b' := by rw [hb'def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hρb : ρ0 ≤ b' := by rw [hb'def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hbb : b ≤ b' := by rw [hb'def]; exact (le_max_right _ _).trans (le_max_left _ _)
  have hjet : ∀ᶠ r : ℕ in atTop, ∀ a j : Fin 3, ∀ p : Region b',
      ‖iteratedFDeriv ℝ 1 (SourcePairedTensor.kernel q hq n r a j) p.val -
        iteratedFDeriv ℝ 1 (VectorLimitIdentification.kernel q n a j) p.val‖ < ε / 2 :=
    Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (fun j =>
      SourcePairedTensor.uniform_actual_jet_limit q hq n 1 b' hb'.le a j (ε / 2) (half_pos hε)))
  have hdiff : ∀ᶠ r : ℕ in atTop, ∀ a j : Fin 3, ∀ p : Region b',
      DifferentiableAt ℝ (SourcePairedTensor.kernel q hq n r a j) p.val :=
    Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (fun j =>
      eventually_kernel_differentiableAt q hq n b' hb'.le a j))
  have hrad : ∀ᶠ r : ℕ in atTop, b' < (SourcePairedInclusion.data q hq n r).R :=
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop b')
  filter_upwards [hjet, hdiff, hrad] with r hj hd hR
  intro x y hx hy i j
  have hx' : ‖x‖ ≤ b' := hx.trans hρb
  have hy' : ‖y‖ ≤ b' := hy.trans hbb
  have hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R := hx'.trans_lt hR
  have hyR : ‖y‖ < (SourcePairedInclusion.data q hq n r).R := hy'.trans_lt hR
  have hmem := SourceCoreOperator.pair_mem_region b' x y hx' hy'
  have hd1 := hd (WeakCurl.previous i) j ⟨(x, y), hmem⟩
  have hd2 := hd (WeakCurl.next i) j ⟨(x, y), hmem⟩
  have h1 := magneticReactionKernel_eq_jets q hq n r x y i j hxR hyR hd1 hd2
  have hl := limit_kernel_curl q n x y i j
  rw [slice_fderiv _ x y (limit_kernel_differentiableAt q n _ j (x, y)),
    slice_fderiv _ x y (limit_kernel_differentiableAt q n _ j (x, y))] at hl
  have e1 := hj (WeakCurl.previous i) j ⟨(x, y), hmem⟩
  have e2 := hj (WeakCurl.next i) j ⟨(x, y), hmem⟩
  have b1 := jet_bound (iteratedFDeriv ℝ 1 (SourcePairedTensor.kernel q hq n r (WeakCurl.previous i) j) (x, y) -
    iteratedFDeriv ℝ 1 (VectorLimitIdentification.kernel q n (WeakCurl.previous i) j) (x, y)) (WeakCurl.next i)
  have b2 := jet_bound (iteratedFDeriv ℝ 1 (SourcePairedTensor.kernel q hq n r (WeakCurl.next i) j) (x, y) -
    iteratedFDeriv ℝ 1 (VectorLimitIdentification.kernel q n (WeakCurl.next i) j) (x, y)) (WeakCurl.previous i)
  simp only [ContinuousMultilinearMap.sub_apply, jet_one_apply] at b1 b2
  have hmain : Complex.I * (magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X x y i j - limitMagKernel q n x y i j) =
      (fderiv ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.previous i) j) (x, y) (basis (WeakCurl.next i), 0) -
        fderiv ℝ (VectorLimitIdentification.kernel q n (WeakCurl.previous i) j) (x, y)
          (basis (WeakCurl.next i), 0)) -
      (fderiv ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.next i) j) (x, y) (basis (WeakCurl.previous i), 0) -
        fderiv ℝ (VectorLimitIdentification.kernel q n (WeakCurl.next i) j) (x, y)
          (basis (WeakCurl.previous i), 0)) := by
    rw [mul_sub, h1]
    linear_combination hl
  have hlt : ‖Complex.I * (magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X x y i j - limitMagKernel q n x y i j)‖ ≤ ε := by
    rw [hmain]
    refine (norm_sub_le _ _).trans ?_
    have c1 := b1.trans e1.le
    have c2 := b2.trans e2.le
    linarith
  rwa [norm_mul, Complex.norm_I, one_mul] at hlt

end S4

section S5
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SphereReactionKernel OQ14.HalfTurnReactionBridge
open OQ14.SourceRadialSystem OQ14.SourcePairedGeometry
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

/-! ### Uniform convergence of the magnetic reaction fields on compact sets -/

/-- Support-restricted splitting of the difference of two kernel integrals. -/
theorem split_bound_supp (A L s1 s2 : Space → ℂ) (S : Set Space) (δ F : ℝ)
    (hA : AEStronglyMeasurable A volume) (hL : AEStronglyMeasurable L volume)
    (h1 : Integrable s1) (h2 : Integrable s2)
    (hs1 : ∀ y, s1 y ≠ 0 → y ∈ S) (hs2 : ∀ y, s2 y ≠ 0 → y ∈ S)
    (hδ : ∀ y ∈ S, ‖A y - L y‖ ≤ δ) (hF : ∀ y ∈ S, ‖L y‖ ≤ F) :
    ‖(∫ y, A y * s1 y) - ∫ y, L y * s2 y‖ ≤ δ * (∫ y, ‖s1 y‖) + F * ∫ y, ‖s1 y - s2 y‖ := by
  have hd : Integrable (fun y => s1 y - s2 y) := h1.sub h2
  have hsd (y : Space) (hy : s1 y - s2 y ≠ 0) : y ∈ S := by
    by_contra hn
    apply hy
    have a1 : s1 y = 0 := by_contra (fun h => hn (hs1 y h))
    have a2 : s2 y = 0 := by_contra (fun h => hn (hs2 y h))
    simp [a1, a2]
  have bA (y : Space) : ‖A y * s1 y‖ ≤ (δ + F) * ‖s1 y‖ := by
    by_cases h : s1 y = 0
    · simp [h]
    · have hyS := hs1 y h
      rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      calc ‖A y‖ = ‖(A y - L y) + L y‖ := by rw [sub_add_cancel]
        _ ≤ ‖A y - L y‖ + ‖L y‖ := norm_add_le _ _
        _ ≤ δ + F := add_le_add (hδ y hyS) (hF y hyS)
  have bL (y : Space) : ‖L y * s2 y‖ ≤ F * ‖s2 y‖ := by
    by_cases h : s2 y = 0
    · simp [h]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hF y (hs2 y h)) (norm_nonneg _)
  have bD (y : Space) : ‖(A y - L y) * s1 y‖ ≤ δ * ‖s1 y‖ := by
    by_cases h : s1 y = 0
    · simp [h]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hδ y (hs1 y h)) (norm_nonneg _)
  have bE (y : Space) : ‖L y * (s1 y - s2 y)‖ ≤ F * ‖s1 y - s2 y‖ := by
    by_cases h : s1 y - s2 y = 0
    · simp [h]
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hF y (hsd y h)) (norm_nonneg _)
  have iA : Integrable (fun y => A y * s1 y) :=
    (h1.norm.const_mul (δ + F)).mono' (hA.mul h1.aestronglyMeasurable) (Eventually.of_forall bA)
  have iL : Integrable (fun y => L y * s2 y) :=
    (h2.norm.const_mul F).mono' (hL.mul h2.aestronglyMeasurable) (Eventually.of_forall bL)
  have iD : Integrable (fun y => (A y - L y) * s1 y) :=
    (h1.norm.const_mul δ).mono' ((hA.sub hL).mul h1.aestronglyMeasurable) (Eventually.of_forall bD)
  have iE : Integrable (fun y => L y * (s1 y - s2 y)) :=
    (hd.norm.const_mul F).mono' (hL.mul hd.aestronglyMeasurable) (Eventually.of_forall bE)
  have hsplit : (∫ y, A y * s1 y) - (∫ y, L y * s2 y) =
      (∫ y, (A y - L y) * s1 y) + ∫ y, L y * (s1 y - s2 y) := by
    rw [← integral_add iD iE, ← integral_sub iA iL]
    congr 1
    funext y
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · calc ‖∫ y, (A y - L y) * s1 y‖ ≤ ∫ y, ‖(A y - L y) * s1 y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, δ * ‖s1 y‖ := integral_mono iD.norm (h1.norm.const_mul δ) bD
      _ = δ * ∫ y, ‖s1 y‖ := integral_const_mul _ _
  · calc ‖∫ y, L y * (s1 y - s2 y)‖ ≤ ∫ y, ‖L y * (s1 y - s2 y)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, F * ‖s1 y - s2 y‖ := integral_mono iE.norm (hd.norm.const_mul F) bE
      _ = F * ∫ y, ‖s1 y - s2 y‖ := integral_const_mul _ _

theorem mass_diff (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci) (u v : VectorL2) (j : Fin 3) :
    (∫ y : Space, ‖DynamicVolume.source ci u j y - DynamicVolume.source ci v j y‖) ≤
      (Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier)) * ‖u - v‖ := by
  have he : (∫ y : Space, ‖DynamicVolume.source ci u j y - DynamicVolume.source ci v j y‖) =
      ∫ y : Space, ‖DynamicVolume.source ci (u - v) j y‖ := by
    apply integral_congr_ae
    filter_upwards [SourcePairedReactionField.source_sub_ae ci u v j] with y hy
    rw [hy]
  rw [he]
  exact SourcePairedReactionField.source_mass' ci d (u - v) j

theorem arith_bound (M1 M2 δ t ε : ℝ) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hε : 0 < ε)
    (hδ : δ = ε / (6 * (M1 + 1))) (ht : t ≤ ε / (6 * (M2 + 1))) :
    3 * (δ * M1 + M2 * t) ≤ ε := by
  have h1 : δ * M1 ≤ ε / 6 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : M2 * t ≤ ε / 6 := by
    calc M2 * t ≤ M2 * (ε / (6 * (M2 + 1))) := mul_le_mul_of_nonneg_left ht hM2
      _ ≤ ε / 6 := by
        rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  linarith

/-- The shell magnetic reaction fields of a convergent sequence of weighted vectors converge uniformly
on balls to the limit magnetic field: the magnetic analogue of
`SourcePairedReactionField.reactionField_tendsto_uniform_compact`. -/
theorem magneticReactionField_tendsto_uniform_compact (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient)
    (d : BoundedMaterialKernel.SupportData ci) (b : ℝ) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) (ρ0 : ℝ)
    (u : ℕ → VectorL2) (u0 : VectorL2) (hu : Tendsto u atTop (𝓝 u0)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖magneticReactionField (SourcePairedInclusion.shell q hq n r) ci (SourcePairedInclusion.data q hq n r).X
          (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X (u r) x i -
        limitMagField q n ci u0 x i‖ ≤ ε := by
  have hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0 :=
    SourcePairedReduction.inclusion_vanish ci d b hcar
  obtain ⟨b', hb'def⟩ : ∃ b' : ℝ, b' = max (max ρ0 b) 1 := ⟨_, rfl⟩
  have hb' : 0 < b' := by rw [hb'def]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hρb : ρ0 ≤ b' := by rw [hb'def]; exact (le_max_left _ _).trans (le_max_left _ _)
  have hbb : b ≤ b' := by rw [hb'def]; exact (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨A0, hA0def⟩ : ∃ A0 : ℝ, A0 = Real.sqrt ci.bound * Real.sqrt (volume.real d.carrier) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A0 := by rw [hA0def]; positivity
  have hs (v : VectorL2) (j : Fin 3) : Integrable (DynamicVolume.source ci v j) :=
    DynamicVolume.source_integrable ci v b hci j
  have hsupp (v : VectorL2) (j : Fin 3) (y : Space) (hy : DynamicVolume.source ci v j y ≠ 0) :
      y ∈ closedBall (0 : Space) b := by
    by_contra hn
    exact hy (DynamicVolume.source_zero ci v b hci j y hn)
  obtain ⟨F, hFdef⟩ : ∃ F : ℝ, F = limF q n := ⟨_, rfl⟩
  have hF0 : 0 ≤ F := by
    rw [hFdef]
    unfold limF
    have := entryBound_nonnegative (1 : ℝ)
    positivity
  obtain ⟨M1, hM1def⟩ : ∃ M1 : ℝ, M1 = A0 * (‖u0‖ + 1) := ⟨_, rfl⟩
  obtain ⟨M2, hM2def⟩ : ∃ M2 : ℝ, M2 = F * A0 := ⟨_, rfl⟩
  have hM1 : 0 ≤ M1 := by rw [hM1def]; positivity
  have hM2 : 0 ≤ M2 := by rw [hM2def]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (6 * (M1 + 1)) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hkernel := magnetic_kernel_tendsto_uniform_compact q hq n ρ0 b δ hδpos
  have hdist := (Metric.tendsto_nhds.mp hu) (ε / (6 * (M2 + 1))) (by positivity)
  have hnorm : ∀ᶠ r : ℕ in atTop, ‖u r‖ < ‖u0‖ + 1 := hu.norm.eventually (gt_mem_nhds (lt_add_one _))
  have hdiff : ∀ᶠ r : ℕ in atTop, ∀ a j : Fin 3, ∀ p : Region b',
      DifferentiableAt ℝ (SourcePairedTensor.kernel q hq n r a j) p.val :=
    Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr (fun j =>
      eventually_kernel_differentiableAt q hq n b' hb'.le a j))
  have hrad : ∀ᶠ r : ℕ in atTop, b' < (SourcePairedInclusion.data q hq n r).R :=
    RadialPhaseLimit.radius_tendsto.eventually (eventually_gt_atTop b')
  filter_upwards [hkernel, hdist, hnorm, hdiff, hrad] with r hk hdr hn hd hR
  intro x hx i
  have hx' : ‖x‖ ≤ b' := hx.trans hρb
  have hxR : ‖x‖ < (SourcePairedInclusion.data q hq n r).R := hx'.trans_lt hR
  -- the jet expression of the kernel, a globally defined measurable function of the second variable
  obtain ⟨Aj, hAj⟩ : ∃ Aj : Fin 3 → Space → ℂ, Aj = fun j y => (-Complex.I) *
      (fderiv ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.previous i) j) (x, y)
          (basis (WeakCurl.next i), 0) -
        fderiv ℝ (SourcePairedTensor.kernel q hq n r (WeakCurl.next i) j) (x, y)
          (basis (WeakCurl.previous i), 0)) := ⟨_, rfl⟩
  have hAeq (j : Fin 3) (y : Space) (hy : ‖y‖ ≤ b) :
      magneticReactionKernel (SourcePairedInclusion.shell q hq n r) (SourcePairedInclusion.data q hq n r).X
        (SourcePairedInclusion.data q hq n r).R (SourcePairedInclusion.data q hq n r).X x y i j = Aj j y := by
    have hy' : ‖y‖ ≤ b' := hy.trans hbb
    have hyR : ‖y‖ < (SourcePairedInclusion.data q hq n r).R := hy'.trans_lt hR
    have hmem := SourceCoreOperator.pair_mem_region b' x y hx' hy'
    have h := magneticReactionKernel_eq_jets q hq n r x y i j hxR hyR
      (hd (WeakCurl.previous i) j ⟨(x, y), hmem⟩) (hd (WeakCurl.next i) j ⟨(x, y), hmem⟩)
    rw [hAj]
    simp only
    linear_combination (-Complex.I) * h + (magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X x y i j) * Complex.I_sq
  have hAm (j : Fin 3) : Measurable (Aj j) := by
    rw [hAj]
    exact (((measurable_partial _ x _).sub (measurable_partial _ x _))).const_mul _
  have hj (j : Fin 3) :
      ‖(∫ y : Space, magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X x y i j * DynamicVolume.source ci (u r) j y) -
        ∫ y : Space, limitMagKernel q n x y i j * DynamicVolume.source ci u0 j y‖ ≤
        δ * (A0 * ‖u r‖) + F * (A0 * ‖u r - u0‖) := by
    have hcongr : (∫ y : Space, magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X x y i j * DynamicVolume.source ci (u r) j y) =
        ∫ y : Space, Aj j y * DynamicVolume.source ci (u r) j y := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : DynamicVolume.source ci (u r) j y = 0
      · simp [hy]
      · have hyb : ‖y‖ ≤ b := by simpa only [mem_closedBall, dist_zero_right] using hsupp (u r) j y hy
        rw [hAeq j y hyb]
    rw [hcongr]
    refine (split_bound_supp (Aj j) (fun y => limitMagKernel q n x y i j) _ _ (closedBall (0 : Space) b) δ F
      (hAm j).aestronglyMeasurable (limitMagKernel_continuous_slice q n x i j).aestronglyMeasurable
      (hs (u r) j) (hs u0 j) (hsupp (u r) j) (hsupp u0 j) ?_ ?_).trans ?_
    · intro y hy
      have hyb : ‖y‖ ≤ b := by simpa only [mem_closedBall, dist_zero_right] using hy
      rw [← hAeq j y hyb]
      exact hk x y hx hyb i j
    · intro y _
      rw [hFdef]
      exact norm_limitMagKernel_le q n x y i j
    · have m1 := SourcePairedReactionField.source_mass' ci d (u r) j
      have m2 := mass_diff ci d (u r) u0 j
      rw [← hA0def] at m1 m2
      exact add_le_add (mul_le_mul_of_nonneg_left m1 hδpos.le) (mul_le_mul_of_nonneg_left m2 hF0)
  unfold magneticReactionField limitMagField
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖(∫ y : Space, magneticReactionKernel (SourcePairedInclusion.shell q hq n r)
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X x y i j * DynamicVolume.source ci (u r) j y) -
        ∫ y : Space, limitMagKernel q n x y i j * DynamicVolume.source ci u0 j y‖
      ≤ ∑ _j : Fin 3, (δ * (A0 * ‖u r‖) + F * (A0 * ‖u r - u0‖)) := Finset.sum_le_sum (fun j _ => hj j)
    _ = 3 * (δ * (A0 * ‖u r‖) + M2 * ‖u r - u0‖) := by
      rw [hM2def]
      simp
      ring
    _ ≤ 3 * (δ * M1 + M2 * ‖u r - u0‖) := by
      have : δ * (A0 * ‖u r‖) ≤ δ * M1 := by
        apply mul_le_mul_of_nonneg_left _ hδpos.le
        rw [hM1def]
        exact mul_le_mul_of_nonneg_left hn.le hA0
      linarith
    _ ≤ ε := by
      apply arith_bound M1 M2 δ _ ε hM1 hM2 hε hδdef
      have := hdr
      rw [dist_eq_norm] at this
      exact this.le

end S5

section S6
open MeasureTheory Set Metric Filter OQ14.Maxwell OQ14.SphereReactionKernel OQ14.HalfTurnReactionBridge
open OQ14.SourceRadialSystem OQ14.SourcePairedGeometry
open PhysicalReactionLimit (Region region_norm)
open scoped Topology

/-! ### The assembled magnetic plane field on compact sets -/

/-- Physical form of the shell magnetic reaction kernel: the magnetic field `MagneticResponse.magnetic`
of the shell polarization of the shell solution driven by the free field of the column `(y,j)`. -/
theorem magneticReactionKernel_eq_magnetic (cs : Coefficient) (R Rin X : ℝ) (x y : Space) (i j : Fin 3) :
    magneticReactionKernel cs R Rin X x y i j = MagneticResponse.magnetic 1 (DynamicVolume.source cs
      (Ring.inverse (DynamicVolume.volumeBlock cs 1 R)
        (ShellReactionIdentification.freeDatum cs Rin X y j))) x i :=
  (magnetic_eq_sum 1 _ x i).symm

/-- The magnetic plane field assembled from the actual finite paired-shell data: incident field, free
magnetic potential of the inclusion source, and the literal shell magnetic reaction field. -/
def pairedPlaneMagnetic (q : ℝ) (hq : 1 ≤ q) (n r : ℕ) (ci : Coefficient) (u : VectorL2)
    (inc : Maxwell.Field) : Maxwell.Field :=
  fun x i => inc x i + MagneticResponse.magnetic 1 (DynamicVolume.source ci u) x i +
    magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X u x i

variable (q : ℝ) (hq : 1 ≤ q) (n : ℕ) (ci : Coefficient) (d : BoundedMaterialKernel.SupportData ci)
  (b : ℝ) (hb : 0 < b) (hcar : ∀ x ∈ d.carrier, ‖x‖ ≤ b) (hsym : HalfTurnVectorAction.Symmetric ci)
include hb hcar hsym

/-- The shell magnetic reaction field of the effective inclusion solutions of half-turn-fixed data
converges uniformly on balls to the parity combination of the plane magnetic reaction fields. -/
theorem magneticReactionField_tendsto_parity
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
    (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n))) (f : VectorL2) (hf : HalfTurnVectorAction.U f = f)
    (ρ0 : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X
          (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) f) x i -
        ((((q ^ (2 * n) : ℝ) : ℂ) - 1) * ParityPlaneFields.magnetic true 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i +
          ((((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1) * ParityPlaneFields.magnetic false 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i)‖ ≤ ε := by
  have hlim := SourcePairedParityClosure.paired_shell_solutions_tendsto_parity q hq n ci d b hb hcar hsym
    hL hu f hf
  filter_upwards [magneticReactionField_tendsto_uniform_compact q hq n ci d b hcar ρ0 _ _ hlim ε hε]
    with r hr x hx i
  have hl := limitMagField_eq_parity q n ci (ParityMaterialField.solution d 1 (q ^ n) f) d.radius d.ballZero
    (SourcePairedParityClosure.source_invariantAE_of_fixed ci hsym d (q ^ n) hu f hf) x i
  rw [← hl]
  exact hr x hx i

/-- Uniform convergence on compacts at positive distance from the carrier of the assembled plane
magnetic field of the effective inclusion solutions to the parity-device total magnetic field with gain
parameter `q ^ n`: the magnetic analogue of `pairedPlaneElectric_tendsto_uniform`. -/
theorem pairedPlaneMagnetic_tendsto_uniform
    (hL : IsUnit (SourcePairedReduction.limitEffective q hq n ci d b hb))
    (hu : IsUnit (ParityMaterialField.block d 1 (q ^ n))) (f : VectorL2) (hf : HalfTurnVectorAction.U f = f)
    (inc : Maxwell.Field) (ρ0 η : ℝ) (hη : 0 < η) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → (∀ y ∈ d.carrier, η ≤ ‖x - y‖) → ∀ i : Fin 3,
      ‖pairedPlaneMagnetic q hq n r ci (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) f)
          inc x i -
        ParityPlaneFields.totalMagnetic 1 (q ^ n)
          (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) inc x i‖ ≤ ε := by
  have hlim := SourcePairedParityClosure.paired_shell_solutions_tendsto_parity q hq n ci d b hb hcar hsym
    hL hu f hf
  have e1 : ((q ^ n) ^ 2 : ℝ) = q ^ (2 * n) := by rw [← pow_mul, mul_comm]
  have e2 : ((q ^ n)⁻¹ ^ 2 : ℝ) = (q ^ (2 * n))⁻¹ := by rw [inv_pow, e1]
  have c1 : (((q ^ n) ^ 2 - 1 : ℝ) : ℂ) = ((q ^ (2 * n) : ℝ) : ℂ) - 1 := by
    rw [e1, Complex.ofReal_sub, Complex.ofReal_one]
  have c2 : (((q ^ n)⁻¹ ^ 2 - 1 : ℝ) : ℂ) = (((q ^ (2 * n))⁻¹ : ℝ) : ℂ) - 1 := by
    rw [e2, Complex.ofReal_sub, Complex.ofReal_one]
  have hM : ∀ ε' : ℝ, 0 < ε' → ∀ᶠ r : ℕ in atTop, ∀ x : Space, ‖x‖ ≤ ρ0 → ∀ i : Fin 3,
      ‖(fun r (x : Space) (i : Fin 3) => magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
          (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
          (SourcePairedInclusion.data q hq n r).X
          (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) f) x i) r x i -
        ((((q ^ n) ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic true 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i +
          (((q ^ n)⁻¹ ^ 2 - 1 : ℝ) : ℂ) * ParityPlaneFields.magnetic false 1
            (DynamicVolume.source ci (ParityMaterialField.solution d 1 (q ^ n) f)) x i)‖ ≤ ε' := by
    intro ε' hε'
    filter_upwards [magneticReactionField_tendsto_parity q hq n ci d b hb hcar hsym hL hu f hf ρ0 ε' hε']
      with r hr x hx i
    rw [c1, c2]
    exact hr x hx i
  exact SourcePairedPlaneCompact.pairedPlaneMagnetic_tendsto_of_reaction ci d inc (q ^ n)
    (fun r => Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) f)
    (ParityMaterialField.solution d 1 (q ^ n) f) hlim
    (fun r x i => magneticReactionField (SourcePairedInclusion.shell q hq n r) ci
      (SourcePairedInclusion.data q hq n r).X (SourcePairedInclusion.data q hq n r).R
      (SourcePairedInclusion.data q hq n r).X
      (Ring.inverse (SourcePairedPlaneCompact.effectiveBlock q hq n r ci b) f) x i)
    ρ0 η hη hM ε hε

end S6

end OQ14.SourcePairedPlaneMagnetic
#print axioms OQ14.SourcePairedPlaneMagnetic.K_neg
#print axioms OQ14.SourcePairedPlaneMagnetic.K_rotation
#print axioms OQ14.SourcePairedPlaneMagnetic.integrable_K
#print axioms OQ14.SourcePairedPlaneMagnetic.integrable_K_add
#print axioms OQ14.SourcePairedPlaneMagnetic.magPotential_invariant_ae
#print axioms OQ14.SourcePairedPlaneMagnetic.magPotential_neg
#print axioms OQ14.SourcePairedPlaneMagnetic.integrable_centralMag
#print axioms OQ14.SourcePairedPlaneMagnetic.centralMag_integral
#print axioms OQ14.SourcePairedPlaneMagnetic.wallMag_integral
#print axioms OQ14.SourcePairedPlaneMagnetic.centralMag_eq_wall_ae
#print axioms OQ14.SourcePairedPlaneMagnetic.limitMagField_eq_parity
#print axioms OQ14.SourcePairedPlaneMagnetic.J_differentiableAt
#print axioms OQ14.SourcePairedPlaneMagnetic.dcoord_sub_const
#print axioms OQ14.SourcePairedPlaneMagnetic.dcoord_add_const
#print axioms OQ14.SourcePairedPlaneMagnetic.curl_eq
#print axioms OQ14.SourcePairedPlaneMagnetic.central_differentiableAt
#print axioms OQ14.SourcePairedPlaneMagnetic.dcoord_central
#print axioms OQ14.SourcePairedPlaneMagnetic.central_curl
#print axioms OQ14.SourcePairedPlaneMagnetic.limit_kernel_curl
#print axioms OQ14.SourcePairedPlaneMagnetic.hollow_bound
#print axioms OQ14.SourcePairedPlaneMagnetic.response_hasFDerivAt_hollow
#print axioms OQ14.SourcePairedPlaneMagnetic.response_dcoord_hollow
#print axioms OQ14.SourcePairedPlaneMagnetic.dcoord_dyadic
#print axioms OQ14.SourcePairedPlaneMagnetic.hessian_partial_symm
#print axioms OQ14.SourcePairedPlaneMagnetic.dyadic_curl
#print axioms OQ14.SourcePairedPlaneMagnetic.magnetic_eq_sum
#print axioms OQ14.SourcePairedPlaneMagnetic.dcoord_sum
#print axioms OQ14.SourcePairedPlaneMagnetic.shell_source_support
#print axioms OQ14.SourcePairedPlaneMagnetic.reactionKernel_curl
#print axioms OQ14.SourcePairedPlaneMagnetic.series_differentiableAt
#print axioms OQ14.SourcePairedPlaneMagnetic.eventually_kernel_differentiableAt
#print axioms OQ14.SourcePairedPlaneMagnetic.jet_one_apply
#print axioms OQ14.SourcePairedPlaneMagnetic.slice_fderiv
#print axioms OQ14.SourcePairedPlaneMagnetic.norm_basis_zero
#print axioms OQ14.SourcePairedPlaneMagnetic.norm_basis'
#print axioms OQ14.SourcePairedPlaneMagnetic.jet_bound
#print axioms OQ14.SourcePairedPlaneMagnetic.limit_kernel_differentiableAt
#print axioms OQ14.SourcePairedPlaneMagnetic.measurable_partial
#print axioms OQ14.SourcePairedPlaneMagnetic.magneticReactionKernel_eq_jets
#print axioms OQ14.SourcePairedPlaneMagnetic.norm_centralMag_le
#print axioms OQ14.SourcePairedPlaneMagnetic.norm_limitMagKernel_le
#print axioms OQ14.SourcePairedPlaneMagnetic.limitMagKernel_continuous_slice
#print axioms OQ14.SourcePairedPlaneMagnetic.magnetic_kernel_tendsto_uniform_compact
#print axioms OQ14.SourcePairedPlaneMagnetic.split_bound_supp
#print axioms OQ14.SourcePairedPlaneMagnetic.mass_diff
#print axioms OQ14.SourcePairedPlaneMagnetic.arith_bound
#print axioms OQ14.SourcePairedPlaneMagnetic.magneticReactionField_tendsto_uniform_compact
#print axioms OQ14.SourcePairedPlaneMagnetic.magneticReactionKernel_eq_magnetic
#print axioms OQ14.SourcePairedPlaneMagnetic.magneticReactionField_tendsto_parity
#print axioms OQ14.SourcePairedPlaneMagnetic.pairedPlaneMagnetic_tendsto_uniform
