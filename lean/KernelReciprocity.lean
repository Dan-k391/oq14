import DynamicConvolution

/-!
Actual even and transpose-symmetric real-frequency remainder kernels give
absolute L2 pairing integrability and a justified Fubini exchange. The bounded
literal convolution operator is bilinearly reciprocal on all vector L2.
Reciprocal resonance normalization is outside this module.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000

namespace OQ14.KernelReciprocity
open MeasureTheory Metric
open scoped ComplexConjugate InnerProductSpace SchwartzMap
abbrev Space := FourierL2.Space
abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2

theorem remainder_symmetric (k : ℝ) (x : Space) (i j : Fin 3) :
    DyadicKernel.remainder k x i j = DyadicKernel.remainder k x j i := by
  simp only [DyadicKernel.remainder, DyadicKernel.dyadic, GreenKernel.phiHessian]
  simp only [eq_comm (a := i) (b := j)]
  ring

theorem remainder_even (k : ℝ) (x : Space) (i j : Fin 3) :
    DyadicKernel.remainder k (-x) i j = DyadicKernel.remainder k x i j := by
  simp only [DyadicKernel.remainder, DyadicKernel.dyadic, GreenKernel.phi,
    GreenKernel.phiHessian, norm_neg, PiLp.neg_apply, Complex.ofReal_neg]
  ring

theorem kernel_symmetric (k R : ℝ) (i j : Fin 3) :
    DynamicConvolution.kernel k R i j = DynamicConvolution.kernel k R j i := by
  funext x
  simp only [DynamicConvolution.kernel]
  congr 1
  funext y
  exact remainder_symmetric k y i j

theorem kernel_even (k R : ℝ) (i j : Fin 3) (x : Space) :
    DynamicConvolution.kernel k R i j (-x) = DynamicConvolution.kernel k R i j x := by
  have hm : -x ∈ closedBall (0 : Space) R ↔ x ∈ closedBall (0 : Space) R := by
    simp only [mem_closedBall, dist_zero_right, norm_neg]
  by_cases hx : x ∈ closedBall (0 : Space) R
  · simp only [DynamicConvolution.kernel, Set.indicator_of_mem hx,
      Set.indicator_of_mem (hm.mpr hx), remainder_even]
  · simp only [DynamicConvolution.kernel, Set.indicator_of_not_mem hx,
      Set.indicator_of_not_mem (mt hm.mp hx)]

def scalarConjugate : ScalarL2 →L[ℝ] ScalarL2 :=
  Complex.conjCLE.toContinuousLinearMap.compLpL 2 volume

theorem scalarConjugate_ae (F : ScalarL2) :
    scalarConjugate F =ᵐ[volume] fun x => conj (F x) :=
  Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL F

def scalarPair (F G : ScalarL2) : ℂ := ∫ x, F x * G x

theorem scalarPair_inner (F G : ScalarL2) :
    scalarPair F G = ⟪scalarConjugate F, G⟫_ℂ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarConjugate_ae F] with x hx
  simp [hx, mul_comm]

theorem scalarPair_continuous : Continuous (fun p : ScalarL2 × ScalarL2 => scalarPair p.1 p.2) := by
  simp_rw [scalarPair_inner]
  exact (scalarConjugate.continuous.comp continuous_fst).inner continuous_snd

theorem scalar_product_integrable (F G : ScalarL2) :
    Integrable (fun x => F x * G x) :=
  (Lp.memLp F).integrable_mul (Lp.memLp G)

theorem product_integrable (q : Space → ℂ) (hq : Integrable q)
    (he : ∀ x, q (-x) = q x) (F G : ScalarL2) :
    Integrable (fun p : Space × Space => F p.2 * q (p.1-p.2) * G p.1)
      (volume.prod volume) := by
  have hF := (Lp.memLp F).integrable_norm_pow (by decide : 2 ≠ 0)
  have hG := (Lp.memLp G).integrable_norm_pow (by decide : 2 ≠ 0)
  have h1 := hF.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hq.norm
  have h2 := (hG.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hq.norm).swap
  have hm := ((Lp.memLp F).aestronglyMeasurable.convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) hq.aestronglyMeasurable).mul
      ((Lp.memLp G).aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  apply (h1.add h2).mono' hm
  filter_upwards with p
  change ‖F p.2 * q (p.1-p.2) * G p.1‖ ≤
    ‖F p.2‖^2 * ‖q (p.1-p.2)‖ + ‖G p.1‖^2 * ‖q (p.2-p.1)‖
  have hn : ‖q (p.2-p.1)‖ = ‖q (p.1-p.2)‖ := by
    rw [← neg_sub p.1 p.2, he]
  rw [hn, norm_mul, norm_mul]
  have ha : ‖F p.2‖ * ‖G p.1‖ ≤ ‖F p.2‖^2 + ‖G p.1‖^2 := by
    nlinarith [sq_nonneg (‖F p.2‖ - ‖G p.1‖)]
  nlinarith [mul_le_mul_of_nonneg_right ha (norm_nonneg (q (p.1-p.2)))]

theorem convolution_swap (q f : Space → ℂ) (x : Space) :
    HeatFourier.convolution q f x = ∫ y, f y * q (x-y) := by
  unfold HeatFourier.convolution
  rw [← integral_sub_left_eq_self (fun y => q y * f (x-y)) volume x]
  simp only [sub_sub_self, mul_comm]

theorem convolution_pairing (q : Space → ℂ) (hq : Integrable q)
    (he : ∀ x, q (-x) = q x) (F G : ScalarL2) :
    (∫ x, HeatFourier.convolution q F x * G x) =
      ∫ y, F y * HeatFourier.convolution q G y := by
  simp_rw [convolution_swap, ← integral_mul_const, ← integral_const_mul]
  rw [integral_integral_swap (product_integrable q hq he F G)]
  apply integral_congr_ae
  filter_upwards with y
  apply integral_congr_ae
  filter_upwards with x
  have h : q (x-y) = q (y-x) := by rw [← neg_sub y x, he]
  rw [h]
  ring

theorem scalar_operator_reciprocity (q : Space → ℂ) (hq : Integrable q)
    (he : ∀ x, q (-x) = q x) (F G : ScalarL2)
    (hF : Integrable (F : Space → ℂ)) (hG : Integrable (G : Space → ℂ)) :
    scalarPair (L1Convolution.operator q hq F) G =
      scalarPair F (L1Convolution.operator q hq G) := by
  unfold scalarPair
  calc
    _ = ∫ x, HeatFourier.convolution q F x * G x := by
      apply integral_congr_ae
      filter_upwards [L1Convolution.operator_ae_convolution q hq F hF] with x hx
      rw [hx]
    _ = ∫ y, F y * HeatFourier.convolution q G y := convolution_pairing q hq he F G
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [L1Convolution.operator_ae_convolution q hq G hG] with x hx
      rw [hx]

theorem scalar_operator_reciprocity_all (q : Space → ℂ) (hq : Integrable q)
    (he : ∀ x, q (-x) = q x) (F G : ScalarL2) :
    scalarPair (L1Convolution.operator q hq F) G =
      scalarPair F (L1Convolution.operator q hq G) := by
  let U := L1Convolution.operator q hq
  refine FourierL2.embed_denseRange.induction_on F
    (isClosed_eq
      (scalarPair_continuous.comp (U.continuous.prodMk continuous_const))
      (scalarPair_continuous.comp (continuous_id.prodMk continuous_const))) ?_
  intro f
  refine FourierL2.embed_denseRange.induction_on G
    (isClosed_eq
      (scalarPair_continuous.comp (continuous_const.prodMk continuous_id))
      (scalarPair_continuous.comp (continuous_const.prodMk U.continuous))) ?_
  intro g
  exact scalar_operator_reciprocity q hq he (FourierL2.embed f) (FourierL2.embed g)
    (f.integrable.congr (FourierL2.embed_ae f).symm)
    (g.integrable.congr (FourierL2.embed_ae g).symm)

theorem scalarPair_sum_left (F : Fin 3 → ScalarL2) (G : ScalarL2) :
    scalarPair (∑ i, F i) G = ∑ i, scalarPair (F i) G := by
  unfold scalarPair
  calc
    _ = ∫ x, ∑ i, F i x * G x := by
      apply integral_congr_ae
      filter_upwards [DynamicConvolution.scalar_sum_ae F] with x hx
      rw [hx, Finset.sum_mul]
    _ = _ := integral_finset_sum _ (fun i _ => scalar_product_integrable (F i) G)

theorem scalarPair_comm (F G : ScalarL2) : scalarPair F G = scalarPair G F := by
  unfold scalarPair
  simp only [mul_comm]

theorem scalarPair_sum_right (F : ScalarL2) (G : Fin 3 → ScalarL2) :
    scalarPair F (∑ i, G i) = ∑ i, scalarPair F (G i) := by
  rw [scalarPair_comm, scalarPair_sum_left]
  simp only [scalarPair_comm]

def vectorPair (F G : VectorL2) : ℂ :=
  ∑ i : Fin 3, scalarPair (DynamicConvolution.component i F) (DynamicConvolution.component i G)

theorem vectorPair_continuous :
    Continuous (fun p : VectorL2 × VectorL2 => vectorPair p.1 p.2) := by
  unfold vectorPair
  apply continuous_finset_sum
  intro i _
  exact scalarPair_continuous.comp
    (((DynamicConvolution.component i).continuous.comp continuous_fst).prodMk
      ((DynamicConvolution.component i).continuous.comp continuous_snd))

theorem vectorPair_comm (F G : VectorL2) : vectorPair F G = vectorPair G F := by
  unfold vectorPair
  simp only [scalarPair_comm]

theorem dynamic_operator_reciprocity (k R : ℝ) (F G : VectorL2) :
    vectorPair (DynamicConvolution.operator k R F) G =
      vectorPair F (DynamicConvolution.operator k R G) := by
  unfold vectorPair
  simp only [DynamicConvolution.component_operator, DynamicConvolution.row,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    scalarPair_sum_left, scalarPair_sum_right]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [scalar_operator_reciprocity_all _ (DynamicConvolution.kernel_integrable k R j i)
    (kernel_even k R j i)]
  simp only [kernel_symmetric k R j i]

theorem vectorPair_actual (F G : VectorL2) :
    vectorPair F G = ∑ i : Fin 3, ∫ x : Space,
      F (VectorFourier.coordinateMap x) i * G (VectorFourier.coordinateMap x) i := by
  unfold vectorPair scalarPair
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [NewtonL2.physicalCoordinate_ae F i,
    NewtonL2.physicalCoordinate_ae G i] with x hx hy
  change NewtonL2.physicalCoordinate F i x * NewtonL2.physicalCoordinate G i x = _
  rw [hx, hy]

theorem scalarPair_sub_left (F G H : ScalarL2) :
    scalarPair (F-G) H = scalarPair F H - scalarPair G H := by
  simp only [scalarPair_inner, map_sub, inner_sub_left]

theorem scalarPair_sub_right (F G H : ScalarL2) :
    scalarPair F (G-H) = scalarPair F G - scalarPair F H := by
  simp only [scalarPair_inner, inner_sub_right]

theorem vectorPair_sub_left (F G H : VectorL2) :
    vectorPair (F-G) H = vectorPair F H - vectorPair G H := by
  simp only [vectorPair, map_sub, scalarPair_sub_left, Finset.sum_sub_distrib]

theorem vectorPair_sub_right (F G H : VectorL2) :
    vectorPair F (G-H) = vectorPair F G - vectorPair F H := by
  simp only [vectorPair, map_sub, scalarPair_sub_right, Finset.sum_sub_distrib]

theorem scalarPair_add_left (F G H : ScalarL2) :
    scalarPair (F+G) H = scalarPair F H + scalarPair G H := by
  simp only [scalarPair_inner, map_add, inner_add_left]

theorem scalarPair_add_right (F G H : ScalarL2) :
    scalarPair F (G+H) = scalarPair F G + scalarPair F H := by
  simp only [scalarPair_inner, inner_add_right]

theorem vectorPair_add_left (F G H : VectorL2) :
    vectorPair (F+G) H = vectorPair F H + vectorPair G H := by
  simp only [vectorPair, map_add, scalarPair_add_left, Finset.sum_add_distrib]

theorem vectorPair_add_right (F G H : VectorL2) :
    vectorPair F (G+H) = vectorPair F G + vectorPair F H := by
  simp only [vectorPair, map_add, scalarPair_add_right, Finset.sum_add_distrib]

theorem vector_operator_reciprocity_of_schwartz (U : VectorL2 →L[ℂ] VectorL2)
    (h : ∀ f g : Fin 3 → 𝓢(Space, ℂ),
      vectorPair (U (VectorFourier.schwartzVector f)) (VectorFourier.schwartzVector g) =
        vectorPair (VectorFourier.schwartzVector f) (U (VectorFourier.schwartzVector g)))
    (F G : VectorL2) : vectorPair (U F) G = vectorPair F (U G) := by
  have hc1 : Continuous (fun A : VectorL2 => vectorPair (U A) G) :=
    vectorPair_continuous.comp (f := fun A : VectorL2 => (U A, G))
      (U.continuous.prodMk continuous_const)
  have hc2 : Continuous (fun A : VectorL2 => vectorPair A (U G)) :=
    vectorPair_continuous.comp (f := fun A : VectorL2 => (A, U G))
      (continuous_id.prodMk continuous_const)
  refine NewtonL2.schwartzVector_denseRange.induction_on
    (p := fun A : VectorL2 => vectorPair (U A) G = vectorPair A (U G))
    F (isClosed_eq hc1 hc2) ?_
  intro f
  have hc3 : Continuous (fun B : VectorL2 => vectorPair (U (VectorFourier.schwartzVector f)) B) :=
    vectorPair_continuous.comp
      (f := fun B : VectorL2 => (U (VectorFourier.schwartzVector f), B))
      (continuous_const.prodMk continuous_id)
  have hc4 : Continuous (fun B : VectorL2 => vectorPair (VectorFourier.schwartzVector f) (U B)) :=
    vectorPair_continuous.comp
      (f := fun B : VectorL2 => (VectorFourier.schwartzVector f, U B))
      (continuous_const.prodMk U.continuous)
  refine NewtonL2.schwartzVector_denseRange.induction_on
    (p := fun B : VectorL2 => vectorPair (U (VectorFourier.schwartzVector f)) B =
      vectorPair (VectorFourier.schwartzVector f) (U B))
    G (isClosed_eq hc3 hc4) ?_
  intro g
  exact h f g

end OQ14.KernelReciprocity







#print axioms OQ14.KernelReciprocity.remainder_symmetric
#print axioms OQ14.KernelReciprocity.remainder_even
#print axioms OQ14.KernelReciprocity.kernel_symmetric
#print axioms OQ14.KernelReciprocity.kernel_even
#print axioms OQ14.KernelReciprocity.scalarConjugate_ae
#print axioms OQ14.KernelReciprocity.scalarPair_inner
#print axioms OQ14.KernelReciprocity.scalarPair_continuous
#print axioms OQ14.KernelReciprocity.scalar_product_integrable
#print axioms OQ14.KernelReciprocity.product_integrable
#print axioms OQ14.KernelReciprocity.convolution_swap
#print axioms OQ14.KernelReciprocity.convolution_pairing
#print axioms OQ14.KernelReciprocity.scalar_operator_reciprocity
#print axioms OQ14.KernelReciprocity.scalar_operator_reciprocity_all
#print axioms OQ14.KernelReciprocity.scalarPair_sum_left
#print axioms OQ14.KernelReciprocity.scalarPair_comm
#print axioms OQ14.KernelReciprocity.scalarPair_sum_right
#print axioms OQ14.KernelReciprocity.vectorPair_continuous
#print axioms OQ14.KernelReciprocity.vectorPair_comm
#print axioms OQ14.KernelReciprocity.dynamic_operator_reciprocity
#print axioms OQ14.KernelReciprocity.vectorPair_actual
#print axioms OQ14.KernelReciprocity.scalarPair_sub_left
#print axioms OQ14.KernelReciprocity.scalarPair_sub_right
#print axioms OQ14.KernelReciprocity.vectorPair_sub_left
#print axioms OQ14.KernelReciprocity.vectorPair_sub_right
#print axioms OQ14.KernelReciprocity.scalarPair_add_left
#print axioms OQ14.KernelReciprocity.scalarPair_add_right
#print axioms OQ14.KernelReciprocity.vectorPair_add_left
#print axioms OQ14.KernelReciprocity.vectorPair_add_right

#print axioms OQ14.KernelReciprocity.vector_operator_reciprocity_of_schwartz
