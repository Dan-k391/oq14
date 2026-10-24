import ShellInclusionVolume
import ExteriorMaterial
import LocalVolumeResponse

/-! Off the support of a compactly supported material source, the literal scattered field and the
kernel operator are given by the pointwise dyadic integral of the source. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.SeparatedScatteredRepresentation
open MeasureTheory Set Metric OQ14.Maxwell
abbrev Coefficient := StaticCoefficient.Coefficient
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

/-- The continuous exterior representative of the scattered field is, at every exterior point, the
pointwise dyadic integral (dyadic factor first). -/
theorem representative_exterior (ci : Coefficient) (k b : ℝ) (u : VectorL2) (z : Space)
    (hz : b < ‖z‖) (i : Fin 3) :
    ExteriorMaterial.scattered ci k b u z i =
      ∑ j, ∫ y, DyadicKernel.dyadic k (z-y) i j * DynamicVolume.source ci u j y := by
  rw [ExteriorMaterial.scattered_exterior ci k b u z hz i]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  ring

theorem representative_continuousAt (ci : Coefficient) (k b : ℝ) (u : VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (z : Space) (hz : b < ‖z‖) : ContinuousAt (ExteriorMaterial.scattered ci k b u) z :=
  ExteriorMaterial.scattered_continuousAt ci k b u hci z hz

/-- The literal scattered field (built from the Newton operator class) equals the pointwise dyadic
integral almost everywhere off the support. Only almost-everywhere is possible because the
Newton class has no canonical pointwise value; the continuous representative above is exact. -/
theorem scattered_exterior_ae (ci : Coefficient) (k b : ℝ) (u : VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0) :
    ∀ᵐ z : Space, b < ‖z‖ → ∀ i : Fin 3, MaterialField.scattered ci k u z i =
      ∑ j, ∫ y, DyadicKernel.dyadic k (z-y) i j * DynamicVolume.source ci u j y := by
  filter_upwards [ExteriorMaterial.scattered_ae ci k b u hci] with z hz hb i
  rw [← congrFun hz i]
  exact representative_exterior ci k b u z hb i

theorem scattered_exterior_ae_restrict (ci : Coefficient) (k b : ℝ) (u : VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (i : Fin 3) :
    ∀ᵐ z : Space ∂volume.restrict {z : Space | b < ‖z‖}, MaterialField.scattered ci k u z i =
      ∑ j, ∫ y, DyadicKernel.dyadic k (z-y) i j * DynamicVolume.source ci u j y := by
  have h := scattered_exterior_ae ci k b u hci
  rw [ae_restrict_iff' (isOpen_lt continuous_const continuous_norm).measurableSet]
  filter_upwards [h] with z hz hm
  exact hz hm i

theorem kernel_eq_localRepresentative (k R : ℝ) (v : VectorL2) :
    ShellInclusionVolume.kernel k R v = LocalVolumeResponse.localRepresentative k R R v := by
  simp only [ShellInclusionVolume.kernel,LocalVolumeResponse.localRepresentative,NewtonL2.newtonOperator,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.neg_apply,two_mul]
  abel

/-- Operator form: for any vector class whose physical coordinates are integrable with support in
`closedBall 0 b`, the kernel operator `kernel k R` (with `b ≤ R`) is the pointwise dyadic integral
of that source at almost every point with `b < ‖z‖ ≤ R`. -/
theorem kernel_exterior_ae (k b R : ℝ) (hbR : b ≤ R) (v : VectorL2) (ρ : Fin 3 → Space → ℂ)
    (hρ : ∀ j, Integrable (ρ j))
    (hc : ∀ j y, y ∉ closedBall (0 : Space) b → ρ j y = 0)
    (hF : ∀ j, (NewtonL2.physicalCoordinate v j : Space → ℂ) =ᵐ[volume] ρ j) (i : Fin 3) :
    ∀ᵐ z : Space, b < ‖z‖ → ‖z‖ ≤ R →
      (NewtonL2.physicalCoordinate (ShellInclusionVolume.kernel k R v) i : Space → ℂ) z =
        ∑ j, ∫ y, DyadicKernel.dyadic k (z-y) i j * ρ j y := by
  have hcR : ∀ j y, y ∉ closedBall (0 : Space) R → ρ j y = 0 :=
    fun j y hy => hc j y (fun h => hy (closedBall_subset_closedBall hbR h))
  have h1 := (ae_restrict_iff' measurableSet_closedBall).mp
    (LocalVolumeResponse.electric_ae_on_ball k R R v ρ hρ hcR hF i)
  filter_upwards [h1,ExteriorContinuity.electric_ae_exterior k v ρ hρ hF b hc] with z hz1 hz2 hb hR
  rw [kernel_eq_localRepresentative]
  have hmem : z ∈ closedBall (0 : Space) R := by simpa only [mem_closedBall,dist_zero_right] using hR
  rw [hz1 hmem]
  have := congrFun (hz2 hb) i
  rw [this]
  unfold ExteriorContinuity.electric KernelConvolution.response
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- The same, for the weighted source `S ci u` of a coefficient supported in `closedBall 0 b`. -/
theorem kernel_weighted_exterior_ae (ci : Coefficient) (k b R : ℝ) (hbR : b ≤ R) (u : VectorL2)
    (hci : ∀ y : Space, y ∉ closedBall (0 : Space) b → ci.value (VectorFourier.coordinateMap y) = 0)
    (i : Fin 3) :
    ∀ᵐ z : Space, b < ‖z‖ → ‖z‖ ≤ R →
      (NewtonL2.physicalCoordinate
        (ShellInclusionVolume.kernel k R (StaticCoefficient.sqrtMultiplier ci u)) i : Space → ℂ) z =
        ∑ j, ∫ y, DyadicKernel.dyadic k (z-y) i j * DynamicVolume.source ci u j y :=
  kernel_exterior_ae k b R hbR _ (DynamicVolume.source ci u)
    (DynamicVolume.source_integrable ci u b hci) (DynamicVolume.source_zero ci u b hci)
    (StaticNewton.material_source_ae ci u) i

end OQ14.SeparatedScatteredRepresentation
#print axioms OQ14.SeparatedScatteredRepresentation.representative_exterior
#print axioms OQ14.SeparatedScatteredRepresentation.representative_continuousAt
#print axioms OQ14.SeparatedScatteredRepresentation.scattered_exterior_ae
#print axioms OQ14.SeparatedScatteredRepresentation.scattered_exterior_ae_restrict
#print axioms OQ14.SeparatedScatteredRepresentation.kernel_eq_localRepresentative
#print axioms OQ14.SeparatedScatteredRepresentation.kernel_exterior_ae
#print axioms OQ14.SeparatedScatteredRepresentation.kernel_weighted_exterior_ae
