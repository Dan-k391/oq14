import Packet06AxialConvolution
import Packet06AxialMaterialTransport

/-! Dynamic volume transport for arbitrary material under axial rotation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace OQ14.Packet06AxialDynamicTransport
open Complex MeasureTheory Metric Set Filter Maxwell ModalAxialRotation ModalAxialKernel
  StaticCoefficient Packet06AxialMaterialTransport Packet06AxialSource
open scoped Topology
def potential (c : Coefficient) (k : ℝ) (u : VectorFourier.VectorL2) (x : Maxwell.Space) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, ∫ y, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j y

theorem potential_cov_at (c : Coefficient) (R : ℝ) (_hR : 0 ≤ R)
    (_hsupp : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (θ k : ℝ) (u : VectorFourier.VectorL2) (x : Maxwell.Space)
    (i : Fin 3)
    (hI : ∀ p l, Integrable (fun y => DyadicKernel.remainder k (x-y) i p * source c θ u l y))
    (hJ : ∀ i j, Integrable (fun y => DyadicKernel.remainder k (rotation (-θ) x-y) i j * DynamicVolume.source c u j y))
    :
    potential (coefficient θ c) k (action θ u) x i =
      ∑ j : Fin 3, matrix θ i j * potential c k u (rotation (-θ) x) j := by
  let Q := rotation θ
  let P := rotation (-θ)
  have hQP (y : Maxwell.Space) : P (Q y) = y := spatial_inverse θ y
  have hPQ (y : Maxwell.Space) : Q (P y) = y := by
    simpa only [neg_neg] using spatial_inverse (-θ) y
  have hK (y : Maxwell.Space) (l : Fin 3) :
      (∑ p : Fin 3, DyadicKernel.remainder k (x-Q y) i p * matrix θ p l) =
        ∑ j : Fin 3, matrix θ i j * DyadicKernel.remainder k (P x-y) j l := by
    have h := remainder_cov θ k (P x-y) i l
    have he : Q (P x-y) = x-Q y := by rw [map_sub, hPQ]
    rw [he] at h
    exact h.symm
  have hS (p : Fin 3) : (∫ y, DyadicKernel.remainder k (x-y) i p *
        DynamicVolume.source (coefficient θ c) (action θ u) p y) =
      ∑ l : Fin 3, matrix θ p l * ∫ y, DyadicKernel.remainder k (x-y) i p * source c θ u l y := by
    calc
      _ = ∫ y, ∑ l : Fin 3, matrix θ p l *
          (DyadicKernel.remainder k (x-y) i p * source c θ u l y) := by
        apply integral_congr_ae
        filter_upwards [Packet06AxialMaterialTransport.source_transport θ c u p] with y hy
        rw [hy, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro l _; unfold source; ring
      _ = ∑ l : Fin 3, ∫ y, matrix θ p l *
          (DyadicKernel.remainder k (x-y) i p * source c θ u l y) := by
        exact integral_finset_sum _ (fun l _ => (hI p l).const_mul _)
      _ = _ := by simp only [integral_const_mul]
  unfold potential
  simp_rw [hS, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  have hInt (p : Fin 3) : Integrable (fun y => DyadicKernel.remainder k (x-Q y) i p *
      DynamicVolume.source c u l y) := by
    have hh := hI p l
    have hcomp := ((rotation θ).measurePreserving.integrable_comp hh.aestronglyMeasurable).mpr hh
    apply hcomp.congr
    filter_upwards with y
    change DyadicKernel.remainder k (x-Q y) i p * source c θ u l (Q y) = _
    simp [source, P, Q, hQP]
  have htransform (p : Fin 3) : (∫ y, DyadicKernel.remainder k (x-y) i p * source c θ u l y) =
      ∫ y, DyadicKernel.remainder k (x-Q y) i p * DynamicVolume.source c u l y := by
    have h := (rotation θ).measurePreserving.integral_comp (rotation θ).toHomeomorph.measurableEmbedding
      (fun y => DyadicKernel.remainder k (x-y) i p * source c θ u l y)
    simpa [source, P, Q, hQP] using h.symm
  simp_rw [htransform]
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ (fun p _ => (hInt p).const_mul _)]
  have he : (∫ y, ∑ p : Fin 3, matrix θ p l *
      (DyadicKernel.remainder k (x-Q y) i p * DynamicVolume.source c u l y)) =
      ∫ y, ∑ j : Fin 3, matrix θ i j *
        (DyadicKernel.remainder k (P x-y) j l * DynamicVolume.source c u l y) := by
    apply integral_congr_ae
    filter_upwards with y
    calc
      _ = (∑ p : Fin 3, DyadicKernel.remainder k (x-Q y) i p * matrix θ p l) *
          DynamicVolume.source c u l y := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro p _; ring
      _ = (∑ j : Fin 3, matrix θ i j * DyadicKernel.remainder k (P x-y) j l) *
          DynamicVolume.source c u l y := by rw [hK]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
  rw [he, integral_finset_sum _ (fun j _ => (hJ j l).const_mul _)]

theorem cross_integrable_ae (c : Coefficient) (R : ℝ) (_hR : 0 ≤ R)
    (hsupp : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (θ k : ℝ) (u : VectorFourier.VectorL2)
    (i p l : Fin 3) : ∀ᵐ x ∂(volume : Measure Maxwell.Space), x ∈ closedBall 0 R →
      Integrable (fun y => DyadicKernel.remainder k (x-y) i p * source c θ u l y) := by
  have h := (source_integrable c R hsupp θ u l).ae_convolution_exists
    (ContinuousLinearMap.mul ℂ ℂ) (DynamicConvolution.kernel_integrable k (2*R) i p)
  filter_upwards [h] with x hx hxb
  apply hx.congr
  filter_upwards with y
  change source c θ u l y * DynamicConvolution.kernel k (2*R) i p (x-y) = _
  rw [mul_comm]
  by_cases hy : y ∈ closedBall (0 : Maxwell.Space) R
  · have hxy : x-y ∈ closedBall (0 : Maxwell.Space) (2*R) := by
      have hx' : ‖x‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hxb
      have hy' : ‖y‖ ≤ R := by simpa only [mem_closedBall, dist_zero_right] using hy
      have h := norm_sub_le x y
      simp only [mem_closedBall, dist_zero_right]
      linarith
    simp [DynamicConvolution.kernel, hxy]
  · rw [source_zero c R hsupp θ u l y hy]; simp

theorem weightedRemainder_transport (c : Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hsupp : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x) = 0) (θ k : ℝ) (u : VectorFourier.VectorL2) :
    action θ (DynamicVolume.weightedRemainder c k R u) =
      DynamicVolume.weightedRemainder (coefficient θ c) k R (action θ u) := by
  have hsuppRot : ∀ x : Maxwell.Space, x ∉ closedBall 0 R →
      (coefficient θ c).value (VectorFourier.coordinateMap x)=0 := by
    intro x hx
    rw [coefficient_value]
    apply hsupp
    simpa [mem_closedBall, dist_zero_right, (rotation (-θ)).norm_map] using hx
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have hI : ∀ᵐ x : Maxwell.Space ∂volume, ∀ p l : Fin 3, x ∈ closedBall 0 R →
      Integrable (fun y => DyadicKernel.remainder k (x-y) i p * source c θ u l y) :=
    ae_all_iff.mpr (fun p => ae_all_iff.mpr (fun l => cross_integrable_ae c R hR hsupp θ k u i p l))
  have hJ : ∀ᵐ x : Maxwell.Space ∂volume, ∀ j l : Fin 3, (rotation (-θ) x) ∈ closedBall 0 R →
      Integrable (fun y => DyadicKernel.remainder k (rotation (-θ) x-y) j l *
        DynamicVolume.source c u l y) :=
    (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun l =>
        DynamicVolume.remainder_source_integrable_ae c u k R (hsupp) j l)))
  have hT : ∀ᵐ x : Maxwell.Space ∂volume, ∀ j : Fin 3,
      DynamicVolume.weightedRemainder c k R u (VectorFourier.coordinateMap (rotation (-θ) x)) j =
        (Real.sqrt (c.value (VectorFourier.coordinateMap (rotation (-θ) x))) : ℂ) *
          potential c k u (rotation (-θ) x) j :=
    (rotation (-θ)).measurePreserving.quasiMeasurePreserving.ae
      (ae_all_iff.mpr (fun j => DynamicVolume.weightedRemainder_actual c u k R (hsupp) j))
  filter_upwards [action_ae θ (DynamicVolume.weightedRemainder c k R u) i,
    DynamicVolume.weightedRemainder_actual (coefficient θ c) (action θ u) k R (hsuppRot) i,
    hI, hJ, hT] with x h1 h2 hI' hJ' hT'
  rw [h1, h2]
  change (∑ j : Fin 3, matrix θ i j *
    DynamicVolume.weightedRemainder c k R u (VectorFourier.coordinateMap (rotation (-θ) x)) j) =
    (Real.sqrt ((coefficient θ c).value (VectorFourier.coordinateMap x)) : ℂ) * potential (coefficient θ c) k (action θ u) x i
  simp_rw [hT']
  have hm : c.value (VectorFourier.coordinateMap (rotation (-θ) x)) =
      (coefficient θ c).value (VectorFourier.coordinateMap x) := (coefficient_value θ c x).symm
  simp_rw [hm]
  by_cases hx : x ∈ closedBall (0 : Maxwell.Space) R
  · have hPx : rotation (-θ) x ∈ closedBall (0 : Maxwell.Space) R := by
      simpa [mem_closedBall, dist_zero_right, (rotation (-θ)).norm_map] using hx
    have hc := potential_cov_at c R hR hsupp θ k u x i (fun p l => hI' p l hx) (fun j l => hJ' j l hPx)
    rw [hc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _; ring
  · rw [hsuppRot x hx]
    simp


end OQ14.Packet06AxialDynamicTransport
#print axioms OQ14.Packet06AxialDynamicTransport.potential_cov_at
#print axioms OQ14.Packet06AxialDynamicTransport.cross_integrable_ae
#print axioms OQ14.Packet06AxialDynamicTransport.weightedRemainder_transport
