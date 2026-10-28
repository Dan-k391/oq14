import ModalAngularReconstruction
import ModalRadialAE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace OQ14.ModalAngularLinearity
open Complex MeasureTheory Metric Set Filter OQ14.Maxwell OQ14.AngularPower OQ14.PolarMomentTesting
  OQ14.ModalVolumeAngularCoefficients OQ14.ModalAngularReconstruction
open scoped Topology
abbrev VectorL2 := VectorFourier.VectorL2

theorem coefficient_add (u v : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    coefficient (u+v) m =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => coefficient u m r + coefficient v m r := by
  have h : ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)), ∀ i : Fin 3,
      moment (DynamicConvolution.component i (u+v)) (weight m i) r =
        moment (DynamicConvolution.component i u) (weight m i) r +
        moment (DynamicConvolution.component i v) (weight m i) r :=
    ae_all_iff.mpr (fun i => by
      rw [map_add]
      exact (PolarMomentAE.moment_congr (Lp.coeFn_add (DynamicConvolution.component i u)
        (DynamicConvolution.component i v)) (weight m i)).trans
        (PolarMomentAE.moment_add (DynamicConvolution.component i u)
          (DynamicConvolution.component i v) (weight m i) (weight_memLp m i)))
  filter_upwards [h] with r hr
  simp only [coefficient, hr, Finset.sum_add_distrib]

theorem coefficient_smul (a : ℂ) (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    coefficient (a • u) m =ᵐ[volume.restrict (Ioi (0 : ℝ))] fun r => a * coefficient u m r := by
  have h (i : Fin 3) : moment (DynamicConvolution.component i (a • u)) (weight m i) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => a * moment (DynamicConvolution.component i u) (weight m i) r := by
    have hc := PolarMomentAE.moment_congr (Lp.coeFn_smul a (DynamicConvolution.component i u)) (weight m i)
    filter_upwards [hc] with r hr
    rw [show DynamicConvolution.component i (a • u) = a • DynamicConvolution.component i u by simp, hr]
    unfold moment
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  filter_upwards [ae_all_iff.mpr h] with r hr
  simp only [coefficient, hr, Finset.mul_sum]

theorem reconstruct_add (u v : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    reconstruct (u+v) m = reconstruct u m + reconstruct v m := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have h := ModalRadialAE.radial_ae (coefficient_add u v m)
  have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_add (reconstruct u m) (reconstruct v m))
  filter_upwards [reconstruct_actual (u+v) m, reconstruct_actual u m, reconstruct_actual v m, h, hp] with x h1 h2 h3 h4 h5
  rw [h1, h5]
  simp only [Pi.add_apply, PiLp.add_apply]
  rw [h2,h3]
  simp [reconstructedField, h4, add_smul, add_mul]

theorem reconstruct_smul (a : ℂ) (u : VectorL2) (m : C(Sphere, ComplexVectorSphere.Vector)) :
    reconstruct (a • u) m = a • reconstruct u m := by
  apply HalfTurnVectorAction.vector_ext_pt
  intro i
  have h := ModalRadialAE.radial_ae (coefficient_smul a u m)
  have hp := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (Lp.coeFn_smul a (reconstruct u m))
  filter_upwards [reconstruct_actual (a • u) m, reconstruct_actual u m, h, hp] with x h1 h2 h3 h4
  rw [h1, h4]
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  rw [h2]
  simp [reconstructedField, h3, smul_smul, mul_assoc]

#print axioms OQ14.ModalAngularLinearity.reconstruct_add
#print axioms OQ14.ModalAngularLinearity.reconstruct_smul
end OQ14.ModalAngularLinearity


