import DynamicVolume
import BoundedMaterialKernel
import RestrictedTEDatumLinear

/-! Carrier-sensitive bound of the dynamic remainder sandwich.

The sandwich `S * T * S` with `S = sqrtMultiplier c` and `T` the truncated dyadic remainder convolution only
sees the remainder kernel on the difference set `K - K` of the carrier `K`.  Replacing the kernel by its
restriction to any measurable set `E ⊇ K - K` gives an L1 kernel whose Young bound controls the operator, so
`‖weightedRemainder c k R‖ ≤ 9 * c.bound * M` where `M` bounds the L1 mass of the remainder on `E`.  (For a
carrier consisting of balls, `E` is a finite union of balls, whose masses are `O(radius²)`.) -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.WeightedRemainderSchur
open MeasureTheory Metric
abbrev Space := FourierL2.Space
abbrev VectorL2 := VectorFourier.VectorL2
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev Coefficient := StaticCoefficient.Coefficient

/-- Row `i` of the convolution operator with an arbitrary integrable kernel matrix. -/
def rowG (κ : Fin 3 → Fin 3 → Space → ℂ) (hκ : ∀ i j, Integrable (κ i j)) (i : Fin 3) :
    VectorL2 →L[ℂ] ScalarL2 :=
  ∑ j : Fin 3, L1Convolution.operator (κ i j) (hκ i j) ∘L DynamicConvolution.component j

/-- The convolution operator with an arbitrary integrable kernel matrix. -/
def opG (κ : Fin 3 → Fin 3 → Space → ℂ) (hκ : ∀ i j, Integrable (κ i j)) : VectorL2 →L[ℂ] VectorL2 :=
  ∑ i : Fin 3, DynamicConvolution.insert i ∘L rowG κ hκ i

theorem opG_norm (κ : Fin 3 → Fin 3 → Space → ℂ) (hκ : ∀ i j, Integrable (κ i j)) (M : ℝ)
    (hM : ∀ i j, L1Convolution.mass (κ i j)≤M) (F : VectorL2) :
    ‖opG κ hκ F‖≤(9*M)*‖F‖ := by
  have hM0 : 0≤M := (L1Convolution.mass_nonnegative _).trans (hM 0 0)
  have hrow (i : Fin 3) : ‖rowG κ hκ i F‖≤3*M*‖F‖ := by
    change ‖∑ j : Fin 3, L1Convolution.operator (κ i j) (hκ i j) (DynamicConvolution.component j F)‖≤_
    refine (norm_sum_le _ _).trans ?_
    have h (j : Fin 3) : ‖L1Convolution.operator (κ i j) (hκ i j) (DynamicConvolution.component j F)‖≤M*‖F‖ :=
      (L1Convolution.operator_norm _ _ _).trans
        (mul_le_mul (hM i j) (DynamicConvolution.component_norm j F) (norm_nonneg _) hM0)
    calc _≤∑ _j : Fin 3, M*‖F‖ := Finset.sum_le_sum (fun j _ => h j)
      _ = _ := by simp; ring
  change ‖∑ i : Fin 3, DynamicConvolution.insert i (rowG κ hκ i F)‖≤_
  refine (norm_sum_le _ _).trans ?_
  calc _≤∑ _i : Fin 3, 3*M*‖F‖ :=
        Finset.sum_le_sum (fun i _ => (DynamicConvolution.insert_norm i _).trans (hrow i))
    _ = _ := by simp; ring

theorem component_opG (κ : Fin 3 → Fin 3 → Space → ℂ) (hκ : ∀ i j, Integrable (κ i j)) (F : VectorL2)
    (i : Fin 3) : DynamicConvolution.component i (opG κ hκ F)=rowG κ hκ i F := by
  change DynamicConvolution.component i (∑ j : Fin 3, DynamicConvolution.insert j (rowG κ hκ j F))=_
  simp only [map_sum, DynamicConvolution.component_insert]
  simp

theorem opG_ae_convolution (κ : Fin 3 → Fin 3 → Space → ℂ) (hκ : ∀ i j, Integrable (κ i j)) (F : VectorL2)
    (hF : ∀ j, Integrable (DynamicConvolution.component j F : Space → ℂ)) (i : Fin 3) :
    (fun x => opG κ hκ F (VectorFourier.coordinateMap x) i)=ᵐ[volume]
      fun x => ∑ j : Fin 3, HeatFourier.convolution (κ i j) (DynamicConvolution.component j F) x := by
  have hcoord := (NewtonL2.physicalCoordinate_ae (opG κ hκ F) i).symm
  change (fun x => opG κ hκ F (VectorFourier.coordinateMap x) i)=ᵐ[volume]
    (DynamicConvolution.component i (opG κ hκ F) : Space → ℂ) at hcoord
  rw [component_opG] at hcoord
  apply hcoord.trans
  have hs := DynamicConvolution.scalar_sum_ae (fun j => L1Convolution.operator (κ i j) (hκ i j)
    (DynamicConvolution.component j F))
  have hc := ae_all_iff.mpr (fun j => L1Convolution.operator_ae_convolution
    (κ i j) (hκ i j) (DynamicConvolution.component j F) (hF j))
  filter_upwards [hs, hc] with x hx hy
  change (∑ j : Fin 3, L1Convolution.operator (κ i j) (hκ i j) (DynamicConvolution.component j F)) x=_
  rw [hx]
  simp only [hy]

theorem convolution_source (c : Coefficient) (u : VectorL2) (κ : Space → ℂ) (j : Fin 3) (x : Space) :
    HeatFourier.convolution κ (DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u)) x=
      ∫ y, κ (x-y)*DynamicVolume.source c u j y := by
  change MeasureTheory.convolution κ (DynamicConvolution.component j (StaticCoefficient.sqrtMultiplier c u))
    (ContinuousLinearMap.mul ℂ ℂ) volume x=_
  rw [MeasureTheory.convolution_mul_swap]
  apply integral_congr_ae
  filter_upwards [StaticNewton.material_source_ae c u j] with y hy
  rw [DynamicConvolution.component_apply, hy]
  rfl

theorem sqrt_apply_ae (c : Coefficient) (F : VectorL2) (i : Fin 3) :
    ∀ᵐ x : Space, StaticCoefficient.sqrtMultiplier c F (VectorFourier.coordinateMap x) i=
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*F (VectorFourier.coordinateMap x) i := by
  have h := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (StaticCoefficient.sqrtMultiplier_ae c F)
  filter_upwards [h] with x hx
  rw [hx]
  rfl

/-- The restricted remainder kernel matrix. -/
def kappa (k : ℝ) (E : Set Space) (i j : Fin 3) : Space → ℂ :=
  E.indicator (fun z => DyadicKernel.remainder k z i j)

theorem kappa_integrable (k : ℝ) (E : Set Space) (hE : MeasurableSet E)
    (hint : ∀ i j, IntegrableOn (fun z => DyadicKernel.remainder k z i j) E) (i j : Fin 3) :
    Integrable (kappa k E i j) :=
  (integrable_indicator_iff hE).mpr (hint i j)

theorem kappa_mass (k : ℝ) (E : Set Space) (hE : MeasurableSet E) (i j : Fin 3) :
    L1Convolution.mass (kappa k E i j)=∫ z in E, ‖DyadicKernel.remainder k z i j‖ := by
  unfold L1Convolution.mass kappa
  have : (fun z => ‖E.indicator (fun z => DyadicKernel.remainder k z i j) z‖)=
      E.indicator (fun z => ‖DyadicKernel.remainder k z i j‖) := by
    funext z
    exact norm_indicator_eq_indicator_norm _ _
  rw [this, integral_indicator hE]

/-- The weighted remainder sandwich equals the sandwich of the convolution with any integrable kernel matrix that
agrees with the remainder kernel on differences of carrier points. -/
theorem weightedRemainder_eq (c : Coefficient) (d : BoundedMaterialKernel.SupportData c) (k R : ℝ)
    (hc : ∀ x : Space, x∉closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (κ : Fin 3 → Fin 3 → Space → ℂ) (hκ : ∀ i j, Integrable (κ i j))
    (hagree : ∀ x∈d.carrier, ∀ y∈d.carrier, ∀ i j, κ i j (x-y)=DyadicKernel.remainder k (x-y) i j) :
    DynamicVolume.weightedRemainder c k R=
      (StaticCoefficient.sqrtMultiplier c).comp ((opG κ hκ).comp (StaticCoefficient.sqrtMultiplier c)) := by
  refine ContinuousLinearMap.ext (fun u => ?_)
  refine RestrictedTEDatumLinear.physical_ext _ _ (fun i => ?_)
  have hF := StaticNewton.material_source_integrable c u (closedBall 0 R) (isCompact_closedBall 0 R) hc
  have hW := DynamicVolume.weightedRemainder_actual c u k R hc i
  have hO := opG_ae_convolution κ hκ (StaticCoefficient.sqrtMultiplier c u) hF i
  have hS := sqrt_apply_ae c (opG κ hκ (StaticCoefficient.sqrtMultiplier c u)) i
  filter_upwards [hW, hO, hS] with x h1 h2 h3
  change DynamicVolume.weightedRemainder c k R u (VectorFourier.coordinateMap x) i=
    StaticCoefficient.sqrtMultiplier c (opG κ hκ (StaticCoefficient.sqrtMultiplier c u))
      (VectorFourier.coordinateMap x) i
  rw [h1, h3, h2]
  simp only [convolution_source]
  by_cases hx : c.value (VectorFourier.coordinateMap x)=0
  · simp [hx]
  · have hxK : x∈d.carrier := by
      by_contra hn
      exact hx (d.carrierZero x hn)
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y∈d.carrier
    · rw [hagree x hxK y hy i j]
    · have hz : c.value (VectorFourier.coordinateMap y)=0 := d.carrierZero y hy
      simp [DynamicVolume.source, hz]

/-- Carrier-sensitive norm bound of the weighted dynamic remainder: if `E` is measurable and contains every
difference of two carrier points and the remainder kernel has L1 mass at most `M` on `E`, then the sandwich norm
is at most `9 * c.bound * M`. -/
theorem weightedRemainder_norm_le_of_mass (c : Coefficient) (d : BoundedMaterialKernel.SupportData c)
    (k R : ℝ) (hc : ∀ x : Space, x∉closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (E : Set Space) (hE : MeasurableSet E) (hdiff : ∀ x∈d.carrier, ∀ y∈d.carrier, x-y∈E)
    (hint : ∀ i j, IntegrableOn (fun z => DyadicKernel.remainder k z i j) E) (M : ℝ)
    (hM : ∀ i j, ∫ z in E, ‖DyadicKernel.remainder k z i j‖≤M) :
    ‖DynamicVolume.weightedRemainder c k R‖≤9*c.bound*M := by
  have hM0 : 0≤M := (integral_nonneg (fun z => norm_nonneg _)).trans (hM 0 0)
  have hmass : ∀ i j, L1Convolution.mass (kappa k E i j)≤M := fun i j => by
    rw [kappa_mass k E hE]
    exact hM i j
  have hagree : ∀ x∈d.carrier, ∀ y∈d.carrier, ∀ i j, kappa k E i j (x-y)=DyadicKernel.remainder k (x-y) i j := by
    intro x hx y hy i j
    simp only [kappa, Set.indicator_of_mem (hdiff x hx y hy)]
  rw [weightedRemainder_eq c d k R hc (kappa k E) (kappa_integrable k E hE hint) hagree]
  have hb := StaticCoefficient.bound_nonnegative c
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg (by norm_num) hb) hM0) (fun u => ?_)
  change ‖StaticCoefficient.sqrtMultiplier c (opG (kappa k E) (kappa_integrable k E hE hint)
    (StaticCoefficient.sqrtMultiplier c u))‖≤_
  calc _≤Real.sqrt c.bound*‖opG (kappa k E) (kappa_integrable k E hE hint)
        (StaticCoefficient.sqrtMultiplier c u)‖ := StaticCoefficient.applySqrt_norm c _
    _ ≤Real.sqrt c.bound*((9*M)*‖StaticCoefficient.sqrtMultiplier c u‖) :=
      mul_le_mul_of_nonneg_left (opG_norm _ _ M hmass _) (Real.sqrt_nonneg _)
    _ ≤Real.sqrt c.bound*((9*M)*(Real.sqrt c.bound*‖u‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (StaticCoefficient.applySqrt_norm c u)
        (mul_nonneg (by norm_num) hM0)) (Real.sqrt_nonneg _)
    _ = 9*c.bound*M*‖u‖ := by
      have hs := Real.sq_sqrt hb
      calc _=(Real.sqrt c.bound)^2*((9*M)*‖u‖) := by ring
        _ = _ := by rw [hs]; ring

end OQ14.WeightedRemainderSchur
#print axioms OQ14.WeightedRemainderSchur.opG_norm
#print axioms OQ14.WeightedRemainderSchur.component_opG
#print axioms OQ14.WeightedRemainderSchur.opG_ae_convolution
#print axioms OQ14.WeightedRemainderSchur.convolution_source
#print axioms OQ14.WeightedRemainderSchur.sqrt_apply_ae
#print axioms OQ14.WeightedRemainderSchur.kappa_integrable
#print axioms OQ14.WeightedRemainderSchur.kappa_mass
#print axioms OQ14.WeightedRemainderSchur.weightedRemainder_eq
#print axioms OQ14.WeightedRemainderSchur.weightedRemainder_norm_le_of_mass
