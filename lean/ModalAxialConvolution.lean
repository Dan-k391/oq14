import ModalAxialIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.ModalAxialConvolution
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalAxialRotation
  OQ14.ModalWeightedMode OQ14.ModalAxialKernel OQ14.ModalAxialIntegrability
open scoped Topology

def potential (n : ℝ) (hn : 1 < n) (k : ℝ) (u : VectorFourier.VectorL2) (x : Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source (coefficient n hn) u j y

theorem potential_cov_at (n : ℝ) (hn : 1 < n) (θ k : ℝ) (u : VectorFourier.VectorL2) (x : Space)
    (i : Fin 3)
    (hI : ∀ p l, Integrable (fun y => DyadicKernel.remainder k (x-y) i p * source n hn θ u l y))
    (hJ : ∀ i j, Integrable (fun y => DyadicKernel.remainder k (rotation (-θ) x-y) i j * DynamicVolume.source (coefficient n hn) u j y))
    :
    potential n hn k (action θ u) x i =
      ∑ j : Fin 3, matrix θ i j * potential n hn k u (rotation (-θ) x) j := by
  let Q := rotation θ
  let P := rotation (-θ)
  have hQP (y : Space) : P (Q y) = y := spatial_inverse θ y
  have hPQ (y : Space) : Q (P y) = y := by
    simpa only [neg_neg] using spatial_inverse (-θ) y
  have hK (y : Space) (l : Fin 3) :
      (∑ p : Fin 3, DyadicKernel.remainder k (x-Q y) i p * matrix θ p l) =
        ∑ j : Fin 3, matrix θ i j * DyadicKernel.remainder k (P x-y) j l := by
    have h := remainder_cov θ k (P x-y) i l
    have he : Q (P x-y) = x-Q y := by rw [map_sub, hPQ]
    rw [he] at h
    exact h.symm
  have hS (p : Fin 3) : (∫ y, DyadicKernel.remainder k (x-y) i p *
        DynamicVolume.source (coefficient n hn) (action θ u) p y) =
      ∑ l : Fin 3, matrix θ p l * ∫ y, DyadicKernel.remainder k (x-y) i p * source n hn θ u l y := by
    calc
      _ = ∫ y, ∑ l : Fin 3, matrix θ p l *
          (DyadicKernel.remainder k (x-y) i p * source n hn θ u l y) := by
        apply integral_congr_ae
        filter_upwards [ModalAxialDynamic.source_action n hn θ u p] with y hy
        rw [hy, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _; unfold source; ring
      _ = ∑ l : Fin 3, ∫ y, matrix θ p l *
          (DyadicKernel.remainder k (x-y) i p * source n hn θ u l y) := by
        exact integral_finset_sum _ (fun l _ => (hI p l).const_mul _)
      _ = _ := by simp only [integral_const_mul]
  unfold potential
  simp_rw [hS, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have hInt (p : Fin 3) : Integrable (fun y => DyadicKernel.remainder k (x-Q y) i p *
      DynamicVolume.source (coefficient n hn) u l y) := by
    have hh := hI p l
    have hcomp := ((rotation θ).measurePreserving.integrable_comp hh.aestronglyMeasurable).mpr hh
    apply hcomp.congr
    filter_upwards with y
    change DyadicKernel.remainder k (x-Q y) i p * source n hn θ u l (Q y) = _
    simp [source, P, Q, hQP]
  have htransform (p : Fin 3) : (∫ y, DyadicKernel.remainder k (x-y) i p * source n hn θ u l y) =
      ∫ y, DyadicKernel.remainder k (x-Q y) i p * DynamicVolume.source (coefficient n hn) u l y := by
    have h := (rotation θ).measurePreserving.integral_comp (rotation θ).toHomeomorph.measurableEmbedding
      (fun y => DyadicKernel.remainder k (x-y) i p * source n hn θ u l y)
    simpa [source, P, Q, hQP] using h.symm
  simp_rw [htransform]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ (fun p _ => (hInt p).const_mul _)]
  have he : (∫ y, ∑ p : Fin 3, matrix θ p l *
      (DyadicKernel.remainder k (x-Q y) i p * DynamicVolume.source (coefficient n hn) u l y)) =
      ∫ y, ∑ j : Fin 3, matrix θ i j *
        (DyadicKernel.remainder k (P x-y) j l * DynamicVolume.source (coefficient n hn) u l y) := by
    apply integral_congr_ae
    filter_upwards with y
    calc
      _ = (∑ p : Fin 3, DyadicKernel.remainder k (x-Q y) i p * matrix θ p l) *
          DynamicVolume.source (coefficient n hn) u l y := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro p _; ring
      _ = (∑ j : Fin 3, matrix θ i j * DyadicKernel.remainder k (P x-y) j l) *
          DynamicVolume.source (coefficient n hn) u l y := by rw [hK]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
  rw [he, integral_finset_sum _ (fun j _ => (hJ j l).const_mul _)]

theorem cross_integrable_ae (n : ℝ) (hn : 1 < n) (θ k : ℝ) (u : VectorFourier.VectorL2)
    (i p l : Fin 3) : ∀ᵐ x ∂(volume : Measure Space), x ∈ closedBall 0 1 →
      Integrable (fun y => DyadicKernel.remainder k (x-y) i p * source n hn θ u l y) := by
  have h := (source_integrable n hn θ u l).ae_convolution_exists
    (ContinuousLinearMap.mul ℂ ℂ) (DynamicConvolution.kernel_integrable k 2 i p)
  filter_upwards [h] with x hx hxb
  apply hx.congr
  filter_upwards with y
  change source n hn θ u l y * DynamicConvolution.kernel k 2 i p (x-y) = _
  rw [mul_comm]
  by_cases hy : y ∈ closedBall (0 : Space) 1
  · have hxy : x-y ∈ closedBall (0 : Space) 2 := by
      have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hxb
      have hy' : ‖y‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hy
      have h := norm_sub_le x y
      simp only [mem_closedBall, dist_zero_right]
      linarith
    simp [DynamicConvolution.kernel, hxy]
  · rw [source_zero n hn θ u l y hy]; simp

theorem weightedRemainder_comm (n : ℝ) (hn : 1 < n) (θ k : ℝ) (u : VectorFourier.VectorL2) :
    action θ (DynamicVolume.weightedRemainder (coefficient n hn) k 1 u) =
      DynamicVolume.weightedRemainder (coefficient n hn) k 1 (action θ u) := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hI : ∀ᵐ x : Space ∂volume, ∀ p l : Fin 3, x ∈ closedBall 0 1 →
      Integrable (fun y => DyadicKernel.remainder k (x-y) i p * source n hn θ u l y) :=
    ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun l => cross_integrable_ae n hn θ k u i p l))
  have hJ : ∀ᵐ x : Space ∂volume, ∀ j l : Fin 3, (rotation (-θ) x) ∈ closedBall 0 1 →
      Integrable (fun y => DyadicKernel.remainder k (rotation (-θ) x-y) j l *
        DynamicVolume.source (coefficient n hn) u l y) :=
    (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun l =>
        DynamicVolume.remainder_source_integrable_ae (coefficient n hn) u k 1 (coefficient_support n hn) j l)))
  have hT : ∀ᵐ x : Space ∂volume, ∀ j : Fin 3,
      DynamicVolume.weightedRemainder (coefficient n hn) k 1 u (VectorFourier.coordinateMap (rotation (-θ) x)) j =
        (Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap (rotation (-θ) x))) : ℂ) *
          potential n hn k u (rotation (-θ) x) j :=
    (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j => DynamicVolume.weightedRemainder_actual (coefficient n hn) u k 1 (coefficient_support n hn) j))
  filter_upwards [action_ae θ (DynamicVolume.weightedRemainder (coefficient n hn) k 1 u) i,
    DynamicVolume.weightedRemainder_actual (coefficient n hn) (action θ u) k 1 (coefficient_support n hn) i,
    hI, hJ, hT] with x h1 h2 hI' hJ' hT'
  rw [h1, h2]
  change (∑ j : Fin 3, matrix θ i j *
    DynamicVolume.weightedRemainder (coefficient n hn) k 1 u (VectorFourier.coordinateMap (rotation (-θ) x)) j) =
    (Real.sqrt ((coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) * potential n hn k (action θ u) x i
  simp_rw [hT']
  have hm : (coefficient n hn).value (VectorFourier.coordinateMap (rotation (-θ) x)) =
      (coefficient n hn).value (VectorFourier.coordinateMap x) := material_invariant n hn (-θ) x
  simp_rw [hm]
  by_cases hx : x ∈ closedBall (0 : Space) 1
  · have hPx : rotation (-θ) x ∈ closedBall (0 : Space) 1 := by
      simpa [mem_closedBall, dist_zero_right, (rotation (-θ)).norm_map] using hx
    have hc := potential_cov_at n hn θ k u x i (fun p l => hI' p l hx) (fun j l => hJ' j l hPx)
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  · rw [coefficient_support n hn x hx]
    simp

#print axioms OQ14.ModalAxialConvolution.weightedRemainder_comm
#print axioms OQ14.ModalAxialConvolution.potential_cov_at
end OQ14.ModalAxialConvolution




