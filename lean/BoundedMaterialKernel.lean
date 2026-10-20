import DynamicSupportVolume

/-! # Actual bounded two-point kernels on compact material supports

Both material multipliers are literal. Cauchy--Schwarz on the finite material
support supplies a volume bound for the resulting integral operator.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.BoundedMaterialKernel

open MeasureTheory Metric DynamicConvolution DynamicSupportVolume
open scoped BigOperators

structure SupportData (c : StaticCoefficient.Coefficient) where
  radius : ℝ
  carrier : Set Space
  measurable : MeasurableSet carrier
  finite : volume carrier ≠ ⊤
  ballZero : ∀ x : Space, x ∉ closedBall 0 radius → c.value (VectorFourier.coordinateMap x) = 0
  carrierZero : ∀ x : Space, x ∉ carrier → c.value (VectorFourier.coordinateMap x) = 0

structure Kernel where
  value : Space → Space → ℂ
  continuous : Continuous (Function.uncurry value)
  bound : ℝ
  nonnegative : 0 ≤ bound
  bounded : ∀ x y, ‖value x y‖ ≤ bound

/-- Actual finite balls supply all support-set and enclosing-ball obligations. -/
def ofFiniteBalls {ι : Type*} [Fintype ι] (c : StaticCoefficient.Coefficient)
    (R : ℝ) (p : ι → Space) (r : ι → ℝ) (hinside : ∀ i, ‖p i‖ + r i ≤ R)
    (hcs : ∀ x : Space, x ∉ ⋃ i, ball (p i) (r i) →
      c.value (VectorFourier.coordinateMap x) = 0) : SupportData c := by
  have hsub : (⋃ i, ball (p i) (r i)) ⊆ closedBall (0 : Space) R := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hd : ‖x-p i‖ < r i := by simpa only [mem_ball, dist_eq_norm] using hi
    have hn := norm_add_le (x-p i) (p i)
    rw [sub_add_cancel] at hn
    simp only [mem_closedBall, dist_zero_right]
    linarith [hinside i]
  exact ⟨R, ⋃ i, ball (p i) (r i),
    (isOpen_iUnion (fun _ => isOpen_ball)).measurableSet,
    measure_ne_top_of_subset hsub (isCompact_closedBall (0 : Space) R).measure_lt_top.ne,
    fun x hx => hcs x (fun hs => hx (hsub hs)), hcs⟩

variable {c : StaticCoefficient.Coefficient}

theorem source_supported (d : SupportData c) (u : VectorL2) (j : Fin 3) :
    WeakCompactness.SupportedIn (component j (StaticCoefficient.sqrtMultiplier c u)) d.carrier := by
  filter_upwards [StaticNewton.material_source_ae c u j] with x hx hn
  rw [component_apply, hx, d.carrierZero x hn]
  simp

theorem source_mass (d : SupportData c) (u : VectorL2) (j : Fin 3) :
    (∫ x, ‖component j (StaticCoefficient.sqrtMultiplier c u) x‖) ≤
      (Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier) := by
  let v := component j (StaticCoefficient.sqrtMultiplier c u)
  let w := supportIndicator d.carrier d.measurable d.finite
  have he : (∫ x, ‖v x‖) = ∫ x, ‖v x‖ * ‖w x‖ := by
    apply integral_congr_ae
    filter_upwards [source_supported d u j,
      indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := d.measurable)
        (hμs := d.finite) (c := (1 : ℂ))] with x hx hw
    by_cases hs : x ∈ d.carrier
    · have hw' : w x = 1 := hw.trans (Set.indicator_of_mem hs _)
      rw [hw', norm_one, mul_one]
    · have hv : v x = 0 := hx hs
      rw [hv, norm_zero, zero_mul]
  rw [he]
  apply (OQ14.WeakPoynting.integral_norm_mul_le v w).trans
  rw [supportIndicator_norm]
  exact mul_le_mul_of_nonneg_right
    ((component_norm j _).trans (StaticCoefficient.applySqrt_norm c u)) (Real.sqrt_nonneg _)

set_option linter.unusedVariables false in
def sourceValue (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3)
    (x : Space) : ℂ :=
  ∫ y, A.value x y * component j (StaticCoefficient.sqrtMultiplier c u) y

theorem source_integrand_integrable (d : SupportData c) (A : Kernel)
    (u : VectorL2) (j : Fin 3) (x : Space) :
    Integrable (fun y => A.value x y * component j (StaticCoefficient.sqrtMultiplier c u) y) := by
  exact (StaticNewton.material_source_integrable c u (closedBall 0 d.radius)
    (isCompact_closedBall 0 d.radius) d.ballZero j).bdd_mul'
    ((A.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (A.bounded x))

theorem sourceValue_bound (d : SupportData c) (A : Kernel) (u : VectorL2)
    (j : Fin 3) (x : Space) :
    ‖sourceValue d A u j x‖ ≤
      A.bound * (Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier) := by
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ y, A.bound * ‖component j (StaticCoefficient.sqrtMultiplier c u) y‖ := by
      apply integral_mono_ae (source_integrand_integrable d A u j x).norm
        ((StaticNewton.material_source_integrable c u (closedBall 0 d.radius)
          (isCompact_closedBall 0 d.radius) d.ballZero j).norm.const_mul A.bound)
      filter_upwards with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (A.bounded x y) (norm_nonneg _)
    _ ≤ _ := by
      rw [integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (source_mass d u j) A.nonnegative).trans_eq (by ring)

theorem sourceValue_continuous (d : SupportData c) (A : Kernel) (u : VectorL2)
    (j : Fin 3) : Continuous (sourceValue d A u j) := by
  apply continuous_of_dominated (fun x => (source_integrand_integrable d A u j x).aestronglyMeasurable)
    (fun x => Filter.Eventually.of_forall (fun y => ?_))
    ((StaticNewton.material_source_integrable c u (closedBall 0 d.radius)
      (isCompact_closedBall 0 d.radius) d.ballZero j).norm.const_mul A.bound)
  · filter_upwards with y
    exact (A.continuous.comp (continuous_id.prodMk continuous_const)).mul continuous_const
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (A.bounded x y) (norm_nonneg _)

def value (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3) (x : Space) : ℂ :=
  (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * sourceValue d A u j x

def pointBound (d : SupportData c) (A : Kernel) (u : VectorL2) : ℝ :=
  Real.sqrt c.bound * (A.bound * (Real.sqrt c.bound * ‖u‖) * Real.sqrt (volume.real d.carrier))

theorem value_ae_bound (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3) :
    ∀ᵐ x, ‖value d A u j x‖ ≤ pointBound d A u *
      ‖supportIndicator d.carrier d.measurable d.finite x‖ := by
  filter_upwards [indicatorConstLp_coeFn (p := (2 : ENNReal)) (hs := d.measurable)
    (hμs := d.finite) (c := (1 : ℂ))] with x hx
  by_cases hs : x ∈ d.carrier
  · have hi : supportIndicator d.carrier d.measurable d.finite x = 1 :=
      hx.trans (Set.indicator_of_mem hs _)
    rw [hi, norm_one, mul_one]
    exact (norm_mul _ _).le.trans (mul_le_mul (StaticCoefficient.sqrt_value_bound c _)
      (sourceValue_bound d A u j x) (norm_nonneg _) (Real.sqrt_nonneg _))
  · have hv : value d A u j x = 0 := by simp [value, d.carrierZero x hs]
    rw [hv, norm_zero]
    have hp : 0 ≤ pointBound d A u := by
      unfold pointBound
      exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg
        (mul_nonneg A.nonnegative (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
          (Real.sqrt_nonneg _))
    positivity

theorem value_memLp (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3) :
    MemLp (value d A u j) 2 volume := by
  apply (Lp.memLp (supportIndicator d.carrier d.measurable d.finite)).of_le_mul
  · apply AEStronglyMeasurable.mul _ (sourceValue_continuous d A u j).aestronglyMeasurable
    exact (Complex.continuous_ofReal.measurable.comp
      (Real.continuous_sqrt.measurable.comp (c.measurable.comp
        VectorFourier.coordinateMap.measurable))).aestronglyMeasurable
  · exact value_ae_bound d A u j

def entry (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3) : ScalarL2 :=
  (value_memLp d A u j).toLp (value d A u j)

theorem entry_ae (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3) :
    entry d A u j =ᵐ[volume] value d A u j := (value_memLp d A u j).coeFn_toLp

theorem entry_norm (d : SupportData c) (A : Kernel) (u : VectorL2) (j : Fin 3) :
    ‖entry d A u j‖ ≤ (c.bound * A.bound * volume.real d.carrier) * ‖u‖ := by
  have hn : ‖entry d A u j‖ ≤ pointBound d A u *
      ‖supportIndicator d.carrier d.measurable d.finite‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [entry_ae d A u j, value_ae_bound d A u j] with x hx hy
    rw [hx]
    exact hy
  apply hn.trans_eq
  rw [supportIndicator_norm]
  unfold pointBound
  have hc := Real.mul_self_sqrt (StaticCoefficient.bound_nonnegative c)
  have hv := Real.mul_self_sqrt (measureReal_nonneg : 0 ≤ volume.real d.carrier)
  calc
    _ = (Real.sqrt c.bound * Real.sqrt c.bound) * A.bound *
      (Real.sqrt (volume.real d.carrier) * Real.sqrt (volume.real d.carrier)) * ‖u‖ := by ring
    _ = _ := by rw [hc, hv]

theorem sourceValue_add (d : SupportData c) (A : Kernel) (u v : VectorL2)
    (j : Fin 3) (x : Space) :
    sourceValue d A (u+v) j x = sourceValue d A u j x + sourceValue d A v j x := by
  unfold sourceValue
  rw [map_add, map_add, ← integral_add (source_integrand_integrable d A u j x)
    (source_integrand_integrable d A v j x)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add (component j (StaticCoefficient.sqrtMultiplier c u))
    (component j (StaticCoefficient.sqrtMultiplier c v))] with y hy
  rw [hy]
  simp only [Pi.add_apply, mul_add]

theorem sourceValue_smul (d : SupportData c) (A : Kernel) (z : ℂ) (u : VectorL2)
    (j : Fin 3) (x : Space) :
    sourceValue d A (z • u) j x = z * sourceValue d A u j x := by
  unfold sourceValue
  rw [map_smul, map_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul z (component j (StaticCoefficient.sqrtMultiplier c u))]
    with y hy
  rw [hy]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def entryLinear (d : SupportData c) (A : Kernel) (j : Fin 3) : VectorL2 →ₗ[ℂ] ScalarL2 where
  toFun u := entry d A u j
  map_add' u v := by
    apply Lp.ext
    filter_upwards [entry_ae d A (u+v) j, entry_ae d A u j, entry_ae d A v j,
      Lp.coeFn_add (entry d A u j) (entry d A v j)] with x huv hu hv ha
    rw [huv, ha]
    simp only [Pi.add_apply, hu, hv, value, sourceValue_add, mul_add]
  map_smul' z u := by
    apply Lp.ext
    filter_upwards [entry_ae d A (z • u) j, entry_ae d A u j,
      Lp.coeFn_smul z (entry d A u j)] with x hzu hu hs
    change entry d A (z • u) j x = (z • entry d A u j) x
    rw [hzu, hs]
    simp only [Pi.smul_apply, hu, value, sourceValue_smul, smul_eq_mul,
      RingHom.id_apply]
    ring

def entryOperator (d : SupportData c) (A : Kernel) (j : Fin 3) : VectorL2 →L[ℂ] ScalarL2 :=
  (entryLinear d A j).mkContinuous (c.bound * A.bound * volume.real d.carrier)
    (fun u => entry_norm d A u j)

theorem entryOperator_norm (d : SupportData c) (A : Kernel) (j : Fin 3) :
    ‖entryOperator d A j‖ ≤ c.bound * A.bound * volume.real d.carrier :=
  ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg
    (mul_nonneg (StaticCoefficient.bound_nonnegative c) A.nonnegative) measureReal_nonneg)
    (fun u => entry_norm d A u j)

def operator (d : SupportData c) (A : Fin 3 → Fin 3 → Kernel) : VectorL2 →L[ℂ] VectorL2 :=
  ∑ i : Fin 3, ∑ j : Fin 3, (insert i).comp (entryOperator d (A i j) j)

def bound (d : SupportData c) (A : Fin 3 → Fin 3 → Kernel) : ℝ :=
  c.bound * volume.real d.carrier * ∑ i : Fin 3, ∑ j : Fin 3, (A i j).bound

theorem bound_nonnegative (d : SupportData c) (A : Fin 3 → Fin 3 → Kernel) :
    0 ≤ bound d A := by
  apply mul_nonneg (mul_nonneg (StaticCoefficient.bound_nonnegative c) measureReal_nonneg)
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (A i j).nonnegative))

theorem operator_apply_norm (d : SupportData c) (A : Fin 3 → Fin 3 → Kernel) (u : VectorL2) :
    ‖operator d A u‖ ≤ bound d A * ‖u‖ := by
  change ‖∑ i : Fin 3, ∑ j : Fin 3, insert i (entry d (A i j) u j)‖ ≤ _
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3,
        (c.bound * (A i j).bound * volume.real d.carrier) * ‖u‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum
        (fun j _ => (insert_norm i _).trans (entry_norm d (A i j) u j)))
    _ = _ := by
      unfold bound
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem operator_norm (d : SupportData c) (A : Fin 3 → Fin 3 → Kernel) :
    ‖operator d A‖ ≤ bound d A :=
  ContinuousLinearMap.opNorm_le_bound _ (bound_nonnegative d A) (operator_apply_norm d A)

theorem operator_norm_finiteBalls {ι : Type*} [Fintype ι]
    (R : ℝ) (p : ι → Space) (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hinside : ∀ i, ‖p i‖ + r i ≤ R)
    (hcs : ∀ x : Space, x ∉ ⋃ i, ball (p i) (r i) →
      c.value (VectorFourier.coordinateMap x) = 0)
    (A : Fin 3 → Fin 3 → Kernel) :
    ‖operator (ofFiniteBalls c R p r hinside hcs) A‖ ≤
      c.bound * (∑ i, (r i)^3 * (Real.pi*4/3)) *
        ∑ i : Fin 3, ∑ j : Fin 3, (A i j).bound := by
  apply (operator_norm _ A).trans
  apply mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finite_ball_volume p r hr) (StaticCoefficient.bound_nonnegative c))
  exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (A i j).nonnegative))

theorem component_operator_ae (d : SupportData c) (A : Fin 3 → Fin 3 → Kernel)
    (u : VectorL2) (i : Fin 3) :
    component i (operator d A u) =ᵐ[volume] fun x => ∑ j : Fin 3,
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∫ y, (A i j).value x y * component j (StaticCoefficient.sqrtMultiplier c u) y := by
  have he : component i (operator d A u) = ∑ j : Fin 3, entry d (A i j) u j := by
    simp [operator, map_sum, component_insert, ContinuousLinearMap.sum_apply,
      entryOperator, entryLinear]
  rw [he]
  filter_upwards [scalar_sum_ae (fun j => entry d (A i j) u j),
    ae_all_iff.mpr (fun j => entry_ae d (A i j) u j)] with x hx hy
  rw [hx]
  simp only [hy]
  rfl

end OQ14.BoundedMaterialKernel

#print axioms OQ14.BoundedMaterialKernel.source_supported
#print axioms OQ14.BoundedMaterialKernel.source_mass
#print axioms OQ14.BoundedMaterialKernel.source_integrand_integrable
#print axioms OQ14.BoundedMaterialKernel.sourceValue_bound
#print axioms OQ14.BoundedMaterialKernel.sourceValue_continuous
#print axioms OQ14.BoundedMaterialKernel.value_ae_bound
#print axioms OQ14.BoundedMaterialKernel.value_memLp
#print axioms OQ14.BoundedMaterialKernel.entry_ae
#print axioms OQ14.BoundedMaterialKernel.entry_norm
#print axioms OQ14.BoundedMaterialKernel.sourceValue_add
#print axioms OQ14.BoundedMaterialKernel.sourceValue_smul
#print axioms OQ14.BoundedMaterialKernel.entryOperator_norm
#print axioms OQ14.BoundedMaterialKernel.bound_nonnegative
#print axioms OQ14.BoundedMaterialKernel.operator_apply_norm
#print axioms OQ14.BoundedMaterialKernel.operator_norm
#print axioms OQ14.BoundedMaterialKernel.operator_norm_finiteBalls
#print axioms OQ14.BoundedMaterialKernel.component_operator_ae
