import DynamicVolumeCompact
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Actual dynamic Maxwell remainder controlled by material volume

The enclosing radius is fixed. The bound uses the actual L2 norms of the
truncated physical kernels and the square root of the material volume.
It is not the sharper support-volume two-thirds estimate.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace OQ14.DynamicSupportVolume

open MeasureTheory Metric DynamicConvolution
open scoped BigOperators

abbrev Coefficient := StaticCoefficient.Coefficient

def supportIndicator (K : Set Space) (hK : MeasurableSet K)
    (hKF : volume K ≠ ⊤) : ScalarL2 :=
  indicatorConstLp 2 hK hKF (1 : ℂ)

theorem supportIndicator_norm (K : Set Space) (hK : MeasurableSet K)
    (hKF : volume K ≠ ⊤) :
    ‖supportIndicator K hK hKF‖ = Real.sqrt (volume.real K) := by
  rw [supportIndicator, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat]
  exact (Real.sqrt_eq_rpow _).symm

theorem vector_norm_le_sum_components (u : VectorL2) :
    ‖u‖ ≤ ∑ i : Fin 3, ‖component i u‖ := by
  have he : u = ∑ i : Fin 3, VectorFourier.insertion i (VectorFourier.coordinate i u) := by
    apply VectorFourier.components.injective
    apply PiLp.ext
    intro j
    change VectorFourier.coordinate j u = VectorFourier.coordinate j _
    simp only [map_sum, VectorFourier.coordinate_insertion]
    simp
  calc
    ‖u‖ = ‖∑ i : Fin 3, insert i (component i u)‖ := by
      congr 1
      simpa only [DynamicConvolution.insert, component, ContinuousLinearMap.comp_apply,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.symm_apply_apply] using he
    _ ≤ ∑ i : Fin 3, ‖insert i (component i u)‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun i _ => insert_norm i _)

def kernelSize (k R : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, ‖DynamicVolumeCompact.kernelL2 k (2*R) i j‖

theorem kernelSize_nonnegative (k R : ℝ) : 0 ≤ kernelSize k R := by
  unfold kernelSize
  positivity

theorem row_ae_value (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorL2) (i : Fin 3) :
    row k (2*R) i (StaticCoefficient.sqrtMultiplier c u) =ᵐ[volume]
      fun x => ∑ j : Fin 3, L2KernelCompact.value
        (DynamicVolumeCompact.kernelL2 k (2*R) i j)
        (component j (StaticCoefficient.sqrtMultiplier c u)) x := by
  have he (j : Fin 3) :
      L1Convolution.operator (kernel k (2*R) i j) (kernel_integrable k (2*R) i j)
        (component j (StaticCoefficient.sqrtMultiplier c u)) =ᵐ[volume]
      L2KernelCompact.value (DynamicVolumeCompact.kernelL2 k (2*R) i j)
        (component j (StaticCoefficient.sqrtMultiplier c u)) := by
    let q := DynamicVolumeCompact.kernelL2 k (2*R) i j
    have hq : Integrable (q : Space → ℂ) :=
      (kernel_integrable k (2*R) i j).congr
        (DynamicVolumeCompact.kernelL2_ae k (2*R) i j).symm
    rw [← DynamicVolumeCompact.operator_congr _ _ hq
      (kernel_integrable k (2*R) i j) (DynamicVolumeCompact.kernelL2_ae k (2*R) i j)]
    exact L2KernelCompact.operator_ae_value q _ hq
      (StaticNewton.material_source_integrable c u (closedBall 0 R)
        (isCompact_closedBall 0 R) hc j)
  have hs := scalar_sum_ae (fun j => L1Convolution.operator
    (kernel k (2*R) i j) (kernel_integrable k (2*R) i j)
    (component j (StaticCoefficient.sqrtMultiplier c u)))
  filter_upwards [hs, ae_all_iff.mpr he] with x hx hy
  change (∑ j : Fin 3, L1Convolution.operator (kernel k (2*R) i j)
    (kernel_integrable k (2*R) i j) (component j (StaticCoefficient.sqrtMultiplier c u))) x = _
  rw [hx]
  simp only [hy]

theorem component_sqrt_ae (c : Coefficient) (f : VectorL2) (i : Fin 3) :
    component i (StaticCoefficient.sqrtMultiplier c f) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) * component i f x := by
  filter_upwards [StaticNewton.material_source_ae c f i,
    NewtonL2.physicalCoordinate_ae f i] with x hx hy
  change NewtonL2.physicalCoordinate (StaticCoefficient.sqrtMultiplier c f) i x =
    (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
      NewtonL2.physicalCoordinate f i x
  rw [hx]
  simp only [DynamicVolume.source, ← hy]

theorem weighted_component_bound (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (K : Set Space) (hK : MeasurableSet K) (hKF : volume K ≠ ⊤)
    (hcs : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorL2) (i : Fin 3) :
    ‖component i (DynamicVolume.weightedRemainder c k R u)‖ ≤
      (Real.sqrt c.bound * (Real.sqrt c.bound * ‖u‖) *
        (∑ j : Fin 3, ‖DynamicVolumeCompact.kernelL2 k (2*R) i j‖)) *
          Real.sqrt (volume.real K) := by
  rw [← supportIndicator_norm K hK hKF]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have hr := row_ae_value c k R hc u i
  have hs := component_sqrt_ae c
    (operator k (2*R) (StaticCoefficient.sqrtMultiplier c u)) i
  rw [component_operator] at hs
  filter_upwards [hs, hr, indicatorConstLp_coeFn (p := (2 : ENNReal))
    (hs := hK) (hμs := hKF) (c := (1 : ℂ))] with x hx hy hi
  change ‖component i (StaticCoefficient.sqrtMultiplier c
    (operator k (2*R) (StaticCoefficient.sqrtMultiplier c u))) x‖ ≤ _
  rw [hx]
  by_cases h : x ∈ K
  · have hi' : supportIndicator K hK hKF x = 1 := hi.trans (Set.indicator_of_mem h _)
    rw [hi', norm_one, mul_one, norm_mul, hy]
    calc
      _ ≤ Real.sqrt c.bound *
          (∑ j : Fin 3, ‖L2KernelCompact.value
            (DynamicVolumeCompact.kernelL2 k (2*R) i j)
            (component j (StaticCoefficient.sqrtMultiplier c u)) x‖) :=
        mul_le_mul (StaticCoefficient.sqrt_value_bound c _)
          (norm_sum_le _ _) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt c.bound * (∑ j : Fin 3,
          (Real.sqrt c.bound * ‖u‖) * ‖DynamicVolumeCompact.kernelL2 k (2*R) i j‖) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply Finset.sum_le_sum
        intro j _
        exact (L2KernelCompact.value_norm_le _ _ x).trans
          (mul_le_mul_of_nonneg_right ((component_norm j _).trans
            (StaticCoefficient.applySqrt_norm c u)) (norm_nonneg _))
      _ = _ := by rw [← Finset.mul_sum]; ring
  · rw [hcs x h]
    simp only [Real.sqrt_zero, Complex.ofReal_zero, zero_mul, norm_zero]
    positivity

def volumeBound (c : Coefficient) (k R : ℝ) (K : Set Space) : ℝ :=
  c.bound * Real.sqrt (volume.real K) * kernelSize k R

theorem volumeBound_nonnegative (c : Coefficient) (k R : ℝ) (K : Set Space) :
    0 ≤ volumeBound c k R K := by
  exact mul_nonneg (mul_nonneg (StaticCoefficient.bound_nonnegative c)
    (Real.sqrt_nonneg _)) (kernelSize_nonnegative k R)

/-- Actual operator estimate at fixed enclosing radius. For material volume
of order a cubed, this gives order a to the three-halves, not order a squared. -/
theorem weightedRemainder_norm (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (K : Set Space) (hK : MeasurableSet K) (hKF : volume K ≠ ⊤)
    (hcs : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0)
    (u : VectorL2) :
    ‖DynamicVolume.weightedRemainder c k R u‖ ≤ volumeBound c k R K * ‖u‖ := by
  apply (vector_norm_le_sum_components _).trans
  calc
    _ ≤ ∑ i : Fin 3, (Real.sqrt c.bound * (Real.sqrt c.bound * ‖u‖) *
        (∑ j : Fin 3, ‖DynamicVolumeCompact.kernelL2 k (2*R) i j‖)) *
          Real.sqrt (volume.real K) :=
      Finset.sum_le_sum (fun i _ => weighted_component_bound c k R hc K hK hKF hcs u i)
    _ = volumeBound c k R K * ‖u‖ := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      unfold volumeBound kernelSize
      have he := Real.mul_self_sqrt (StaticCoefficient.bound_nonnegative c)
      calc
        _ = (Real.sqrt c.bound * Real.sqrt c.bound) *
            (‖u‖ * (∑ i : Fin 3, ∑ j : Fin 3,
              ‖DynamicVolumeCompact.kernelL2 k (2*R) i j‖) * Real.sqrt (volume.real K)) := by ring
        _ = _ := by rw [he]; ring

theorem weightedRemainder_norm_le (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (K : Set Space) (hK : MeasurableSet K) (hKF : volume K ≠ ⊤)
    (hcs : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0) :
    ‖DynamicVolume.weightedRemainder c k R‖ ≤ volumeBound c k R K :=
  ContinuousLinearMap.opNorm_le_bound _ (volumeBound_nonnegative c k R K)
    (weightedRemainder_norm c k R hc K hK hKF hcs)

theorem weightedBlock_sub_isUnit (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (K : Set Space) (hK : MeasurableSet K) (hKF : volume K ≠ ⊤)
    (hcs : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0)
    (hsmall : volumeBound c k R K < 1) :
    IsUnit (StaticCoefficient.weightedBlock c - DynamicVolume.weightedRemainder c k R) :=
  StaticCoefficient.weightedBlock_perturbation_isUnit c _
    ((weightedRemainder_norm_le c k R hc K hK hKF hcs).trans_lt hsmall)

theorem weightedBlock_sub_inverse_le_two (c : Coefficient) (k R : ℝ)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0)
    (K : Set Space) (hK : MeasurableSet K) (hKF : volume K ≠ ⊤)
    (hcs : ∀ x : Space, x ∉ K → c.value (VectorFourier.coordinateMap x) = 0)
    (hsmall : volumeBound c k R K ≤ 1/2) :
    ‖Ring.inverse (StaticCoefficient.weightedBlock c -
      DynamicVolume.weightedRemainder c k R)‖ ≤ 2 := by
  have hn := (weightedRemainder_norm_le c k R hc K hK hKF hcs).trans hsmall
  have hlt : ‖DynamicVolume.weightedRemainder c k R‖ < 1 := by linarith
  apply (StaticCoefficient.weightedBlock_perturbation_inverse c _ hlt).trans
  exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)

/-- No separation is needed for the volume upper bound. -/
theorem finite_ball_volume {ι : Type*} [Fintype ι] (p : ι → Space)
    (r : ι → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume.real (⋃ i, ball (p i) (r i)) ≤
      ∑ i, (r i)^3 * (Real.pi*4/3) := by
  apply (measureReal_iUnion_fintype_le (μ := volume) (fun i => ball (p i) (r i))).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  simp only [measureReal_def, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (hr i),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi*4/3)]

theorem finite_ball_norm_le {ι : Type*} [Fintype ι]
    (c : Coefficient) (k R : ℝ) (p : ι → Space) (r : ι → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hinside : ∀ i, ‖p i‖ + r i ≤ R)
    (hcs : ∀ x : Space, x ∉ ⋃ i, ball (p i) (r i) →
      c.value (VectorFourier.coordinateMap x) = 0) :
    ‖DynamicVolume.weightedRemainder c k R‖ ≤
      c.bound * Real.sqrt (∑ i, (r i)^3 * (Real.pi*4/3)) * kernelSize k R := by
  have hsub : (⋃ i, ball (p i) (r i)) ⊆ closedBall (0 : Space) R := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    have hdist : ‖x-p i‖ < r i := by simpa only [mem_ball, dist_eq_norm] using hi
    have hnorm := norm_add_le (x-p i) (p i)
    rw [sub_add_cancel] at hnorm
    simp only [mem_closedBall, dist_zero_right]
    linarith [hinside i]
  have hc : ∀ x : Space, x ∉ closedBall 0 R →
      c.value (VectorFourier.coordinateMap x) = 0 :=
    fun x hx => hcs x (fun hs => hx (hsub hs))
  have hK : MeasurableSet (⋃ i, ball (p i) (r i)) :=
    (isOpen_iUnion (fun _ => isOpen_ball)).measurableSet
  have hKF : volume (⋃ i, ball (p i) (r i)) ≠ ⊤ :=
    measure_ne_top_of_subset hsub (isCompact_closedBall (0 : Space) R).measure_lt_top.ne
  apply (weightedRemainder_norm_le c k R hc _ hK hKF hcs).trans
  unfold volumeBound
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (finite_ball_volume p r hr))
      (StaticCoefficient.bound_nonnegative c)) (kernelSize_nonnegative k R)

end OQ14.DynamicSupportVolume

#print axioms OQ14.DynamicSupportVolume.supportIndicator_norm
#print axioms OQ14.DynamicSupportVolume.vector_norm_le_sum_components
#print axioms OQ14.DynamicSupportVolume.kernelSize_nonnegative
#print axioms OQ14.DynamicSupportVolume.row_ae_value
#print axioms OQ14.DynamicSupportVolume.component_sqrt_ae
#print axioms OQ14.DynamicSupportVolume.weighted_component_bound
#print axioms OQ14.DynamicSupportVolume.volumeBound_nonnegative
#print axioms OQ14.DynamicSupportVolume.weightedRemainder_norm
#print axioms OQ14.DynamicSupportVolume.weightedRemainder_norm_le
#print axioms OQ14.DynamicSupportVolume.weightedBlock_sub_isUnit
#print axioms OQ14.DynamicSupportVolume.weightedBlock_sub_inverse_le_two
#print axioms OQ14.DynamicSupportVolume.finite_ball_volume
#print axioms OQ14.DynamicSupportVolume.finite_ball_norm_le
