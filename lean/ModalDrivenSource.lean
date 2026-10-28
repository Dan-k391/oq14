import ModalDrivenRadiation
import ModalVolumeData
import ModalDipoleOrigin

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalDrivenSource
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.ModalDriven
  OQ14.ModalDrivenScattering OQ14.ModalWeightedMode OQ14.ModalVolumeData
open scoped Topology

theorem weighted_actual (n : ℝ) (hn : 1 < n) (k : ℂ) (hk : k ≠ 0) (i : Fin 3) :
    (fun x => ModalVolumeData.numerator n hn k (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt ((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        ModalDriven.electric (n : ℂ) k x i := by
  filter_upwards [ModalVolumeData.numerator_actual n hn k i] with x hx
  rw [hx, ModalWeightedMode.coefficient_value]
  by_cases hi : ‖x‖ < 1
  · rw [if_pos hi, (ModalDriven.interior (n : ℂ) k hk x hi.le).1]
    simp
  · rw [if_neg hi]
    simp

theorem source_actual (n : ℝ) (hn : 1 < n) (k : ℂ) (hk : k ≠ 0) (i : Fin 3) :
    DynamicVolume.source (ModalWeightedMode.coefficient n hn) (ModalVolumeData.numerator n hn k) i =ᵐ[volume]
      fun x => (((ModalWeightedMode.coefficient n hn).value (VectorFourier.coordinateMap x)) : ℂ) *
        ModalDriven.electric (n : ℂ) k x i :=
  MaterialVolumeConverse.source_from_weighted _ _ _ (weighted_actual n hn k hk) i

theorem vacuum_num_second (k : ℂ) : (ModalDriven.numerator 1 k).2 = 0 := by
  simp [ModalDriven.numerator, ModalMatching.adjugate, ModalDriven.incidentState]
  ring

theorem vacuum_fields (k : ℂ) (hk : k ≠ 0) (x : Space) :
    ModalDriven.electric 1 k x = I • ModalOrigin.centerE k x ∧
    ModalDriven.magnetic 1 k x = I • ModalOrigin.centerH k k x := by
  have hfirst := ModalDriven.numerator_first 1 k hk
  have hsecond := vacuum_num_second k
  have hdet := ModalDipoleOrigin.tmDet_one k hk
  by_cases hx : ‖x‖ ≤ 1
  · simp [ModalDriven.electric, ModalDriven.magnetic, hx, hfirst]
  · simp [ModalDriven.electric, ModalDriven.magnetic, hx, hdet, ModalDriven.determinant, hsecond]

theorem weakCurl_const_mul (c : ℂ) (F : Field) (φ : Space → ℂ) :
    weakCurlPairing (fun x => c • F x) φ = fun i => c * weakCurlPairing F φ i := by
  have hp (i j : Fin 3) : (∫ x, (c * F x i) * dcoord φ x j) =
      c * ∫ x, F x i * dcoord φ x j := by
    simp_rw [mul_assoc]
    exact integral_const_mul _ _
  ext i
  fin_cases i <;> simp [weakCurlPairing, hp] <;> ring

theorem incident_weak (n k : ℂ) (hk : k ≠ 0) (φ : Space → ℂ)
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) :
    weakCurlPairing (fun x => ModalDriven.determinant n k • ModalOrigin.centerE k x) φ =
      (fun j => ∫ x, (I*k*(ModalDriven.determinant n k * ModalOrigin.centerH k k x j))*φ x) ∧
    weakCurlPairing (fun x => ModalDriven.determinant n k • ModalOrigin.centerH k k x) φ =
      (fun j => ∫ x, (-I*k*(ModalDriven.determinant n k * ModalOrigin.centerE k x j))*φ x) := by
  let c := ModalDriven.determinant n k / I
  have hci : c * I = ModalDriven.determinant n k := by dsimp [c]; field_simp; ring_nf; simp [I_sq]
  have he : (fun x => ModalDriven.determinant n k • ModalOrigin.centerE k x) =
      fun x => c • ModalDriven.electric 1 k x := by
    funext x; rw [(vacuum_fields k hk x).1]
    rw [smul_smul, hci]
  have hh : (fun x => ModalDriven.determinant n k • ModalOrigin.centerH k k x) =
      fun x => c • ModalDriven.magnetic 1 k x := by
    funext x; rw [(vacuum_fields k hk x).2]
    rw [smul_smul, hci]
  have h := ModalDrivenClassical.weak_maxwell 1 k one_ne_zero hk φ hφ hc
  have hcoeff (x : Space) : ModalProfiles.coefficient 1 x = 1 := by simp [ModalProfiles.coefficient]
  constructor
  · rw [he, weakCurl_const_mul, h.1]
    ext j
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [(vacuum_fields k hk x).2]
    simp [c, I_ne_zero]
    ring_nf
    simp [I_sq]
  · rw [hh, weakCurl_const_mul, h.2]
    ext j
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [hcoeff x, (vacuum_fields k hk x).1]
    simp [c, I_ne_zero]
    ring_nf
    simp [I_sq]

theorem weak_pair (F : Field) (i : Fin 3) (f : DynamicSource.Test) :
    weakCurlPairing F f.val i = MagneticResponse.curlPair (MaterialMaxwell.fieldPair F) i f := by
  fin_cases i <;> simp [weakCurlPairing, MagneticResponse.curlPair, MaterialMaxwell.fieldPair,
    WeakCurl.next, WeakCurl.previous, DynamicSource.testPartial, GradientProjection.pderivative_apply]

theorem forced (n : ℝ) (hn : 1 < n) (k : ℝ) (hk : k ≠ 0) :
    ForcedMaxwellResponse.TestForced k
      (DynamicVolume.source (ModalWeightedMode.coefficient n hn) (ModalVolumeData.numerator n hn k))
      (scatteredE (n : ℂ) k) (scatteredH (n : ℂ) k) := by
  let E := ModalDriven.electric (n : ℂ) k
  let H := ModalDriven.magnetic (n : ℂ) k
  let EI : Field := fun x => ModalDriven.determinant (n : ℂ) k • ModalOrigin.centerE k x
  let HI : Field := fun x => ModalDriven.determinant (n : ℂ) k • ModalOrigin.centerH k k x
  let ρ := DynamicVolume.source (ModalWeightedMode.coefficient n hn) (ModalVolumeData.numerator n hn k)
  have hk' : (k : ℂ) ≠ 0 := ofReal_ne_zero.mpr hk
  have hn' : (n : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hE (i : Fin 3) : LocallyIntegrable (fun x => E x i) :=
    HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _
      (fun T => (ModalDrivenLocal.local_L2 (n : ℂ) k hk' T i).1)
  have hH (i : Fin 3) : LocallyIntegrable (fun x => H x i) :=
    HomogeneousVolumeUniqueness.locallyIntegrable_of_memLp_closedBalls _
      (fun T => (ModalDrivenLocal.local_L2 (n : ℂ) k hk' T i).2)
  have hEI (i : Fin 3) : LocallyIntegrable (fun x => EI x i) :=
    (continuous_const.mul (ModalOrigin.centerE_continuous k i)).locallyIntegrable
  have hHI (i : Fin 3) : LocallyIntegrable (fun x => HI x i) :=
    (continuous_const.mul (ModalOrigin.centerH_continuous k k i)).locallyIntegrable
  have hρ (i : Fin 3) : Integrable (ρ i) :=
    DynamicVolume.source_integrable _ _ 1 (ModalWeightedMode.coefficient_support n hn) i
  have ep : MaterialMaxwell.fieldPair (scatteredE (n : ℂ) k) =
      fun i f => MaterialMaxwell.fieldPair E i f - MaterialMaxwell.fieldPair EI i f := by
    funext i f; exact ForcedMaxwellResponse.fieldPair_sub E EI hE hEI i f
  have hp : MaterialMaxwell.fieldPair (scatteredH (n : ℂ) k) =
      fun i f => MaterialMaxwell.fieldPair H i f - MaterialMaxwell.fieldPair HI i f := by
    funext i f; exact ForcedMaxwellResponse.fieldPair_sub H HI hH hHI i f
  intro i f
  have ht := ModalDrivenClassical.weak_maxwell (n : ℂ) k hn' hk' f.val (f.val.smooth 2) f.property
  have hi := incident_weak (n : ℂ) k hk' f.val (f.val.smooth 2) f.property
  have hEt : Integrable (fun x => E x i * f.val x) :=
    PointSingularity.test_product_integrable _ _ (hE i) f.val.continuous f.property
  have hρt : Integrable (fun x => ρ i x * f.val x) :=
    PointSingularity.test_product_integrable _ _ (hρ i).locallyIntegrable f.val.continuous f.property
  have hsum : (∫ x, ModalProfiles.coefficient (n : ℂ) x * E x i * f.val x) =
      MaterialMaxwell.fieldPair E i f + ∫ x, ρ i x * f.val x := by
    have ha : (fun x => ModalProfiles.coefficient (n : ℂ) x * E x i * f.val x) =ᵐ[volume]
        fun x => E x i * f.val x + ρ i x * f.val x := by
      filter_upwards [ModalWeightedMode.coefficient_agrees_ae n hn, source_actual n hn (k : ℂ) hk' i] with x hx hs
      change ModalProfiles.coefficient (n : ℂ) x * E x i * f.val x = E x i * f.val x + DynamicVolume.source _ _ i x * f.val x
      rw [← hx, hs]
      ring
    rw [integral_congr_ae ha, integral_add hEt hρt]
    rfl
  have h1 := congrFun ht.1 i
  have h2 := congrFun ht.2 i
  have h3 := congrFun hi.1 i
  have h4 := congrFun hi.2 i
  rw [weak_pair] at h1 h2 h3 h4
  have h1' : MagneticResponse.curlPair (MaterialMaxwell.fieldPair E) i f = I*(k : ℂ)*MaterialMaxwell.fieldPair H i f := by
    rw [h1]; simp only [MaterialMaxwell.fieldPair, ← integral_const_mul]; congr 1; funext x; dsimp [E, H, EI, HI]; ring
  have h2' : MagneticResponse.curlPair (MaterialMaxwell.fieldPair H) i f = -(I*(k : ℂ))*(MaterialMaxwell.fieldPair E i f + ∫ x, ρ i x*f.val x) := by
    rw [h2, ← hsum, ← integral_const_mul]; congr 1; funext x; dsimp [E, H, EI, HI]; ring
  have h3' : MagneticResponse.curlPair (MaterialMaxwell.fieldPair EI) i f = I*(k : ℂ)*MaterialMaxwell.fieldPair HI i f := by
    rw [h3]; simp only [MaterialMaxwell.fieldPair, ← integral_const_mul]; congr 1; funext x; dsimp [E, H, EI, HI]; ring
  have h4' : MagneticResponse.curlPair (MaterialMaxwell.fieldPair HI) i f = -(I*(k : ℂ))*MaterialMaxwell.fieldPair EI i f := by
    rw [h4]; simp only [MaterialMaxwell.fieldPair, ← integral_const_mul]; congr 1; funext x; dsimp [E, H, EI, HI]; ring
  constructor
  · rw [ep, hp, ForcedMaxwellResponse.curlPair_sub, h1', h3']; ring
  · rw [hp, ep, ForcedMaxwellResponse.curlPair_sub, h2', h4']; ring

#print axioms OQ14.ModalDrivenSource.forced
#print axioms OQ14.ModalDrivenSource.incident_weak
#print axioms OQ14.ModalDrivenSource.weighted_actual
#print axioms OQ14.ModalDrivenSource.source_actual
end OQ14.ModalDrivenSource








