import Packet04RaisingPolynomial
import Packet01MomentIntegrability
import OutgoingModeGluing

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04RaisingMoments
open Complex MeasureTheory Set OQ14.Maxwell OQ14.AngularPower
  OQ14.HarmonicPolynomial OQ14.SphericalMomentEquation OQ14.PolarMomentTesting
  OQ14.PolarMomentEnergy OQ14.HarmonicMomentCoupling OQ14.HarmonicMomentIntegrability
  OQ14.Packet04RaisingPolynomial

def raisedMoment (V : VectorFourier.VectorL2) (p : Poly) (l : ℕ) (r : ℝ) : ℂ :=
  ∑ i : Fin 3, moment (NewtonL2.physicalCoordinate V i) (angularPolynomial (raised p l i)) r

theorem raised_radial_gradient (V : VectorFourier.VectorL2) (p : Poly) (l : ℕ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      raisedMoment V p l r = radialMoment (fun i => NewtonL2.physicalCoordinate V i) p r -
        ((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ * gradientMoment (fun i => NewtonL2.physicalCoordinate V i) p r := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin 3 =>
    slice_memLp_ae (NewtonL2.physicalCoordinate V i))] with r hr
  have he (i : Fin 3) :
      moment (NewtonL2.physicalCoordinate V i) (angularPolynomial (raised p l i)) r =
        moment (NewtonL2.physicalCoordinate V i) (radialWeight p i) r -
        ((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ *
          moment (NewtonL2.physicalCoordinate V i) (gradientWeight p i) r := by
    unfold moment
    simp only [raised_angular_value]
    have ha : Integrable (fun ω : Sphere =>
        NewtonL2.physicalCoordinate V i (r • (ω : Space)) * radialWeight p i ω) angularMeasure :=
      (hr i).integrable_mul (HarmonicMomentCoupling.weight_memLp p i).1
    have hb : Integrable (fun ω : Sphere =>
        ((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ *
          (NewtonL2.physicalCoordinate V i (r • (ω : Space)) * gradientWeight p i ω)) angularMeasure :=
      ((hr i).integrable_mul (HarmonicMomentCoupling.weight_memLp p i).2).const_mul _
    have hf : (fun ω : Sphere => NewtonL2.physicalCoordinate V i (r • (ω : Space)) *
        (radialWeight p i ω - ((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ * gradientWeight p i ω)) =
      (fun ω : Sphere => NewtonL2.physicalCoordinate V i (r • (ω : Space)) * radialWeight p i ω -
        ((2*(l : ℝ)+3 : ℝ) : ℂ)⁻¹ *
          (NewtonL2.physicalCoordinate V i (r • (ω : Space)) * gradientWeight p i ω)) := by
      funext ω; ring
    rw [hf, integral_sub ha hb, integral_const_mul]
  simp only [raisedMoment, he, Finset.sum_sub_distrib, ← Finset.mul_sum,
    radialMoment, gradientMoment]

theorem raised_radial_tangential (V : VectorFourier.VectorL2) (p : Poly) (l : ℕ) :
    ∀ᵐ r : ℝ ∂volume.restrict (Ioi (0 : ℝ)),
      raisedMoment V p l r =
        (((l+2 : ℂ) * radialMoment (fun i => NewtonL2.physicalCoordinate V i) p r) -
          tangentialMoment (fun i => NewtonL2.physicalCoordinate V i) p l r) /
        (2*(l : ℂ)+3) := by
  filter_upwards [raised_radial_gradient V p l] with r hr
  rw [hr, tangentialMoment]
  have hc : (2*(l : ℂ)+3) ≠ 0 := by
    exact_mod_cast (show 2*(l : ℝ)+3 ≠ 0 by positivity)
  push_cast
  field_simp [hc]
  ring

theorem actual_raised_outgoing (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0)
    (T : ℝ) (hT : 1 < T) (u : VectorFourier.VectorL2)
    (p : Poly) (l : ℕ) (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0) :
    ∃ c : ℂ, ∀ᵐ r : ℝ ∂volume.restrict (Ioo 1 T),
      (r : ℂ) * raisedMoment (ComplexExteriorResponse.response
        (ModalWeightedMode.coefficient n hn) z 1 T u) p l r =
        c * RadialRellich.outgoing (l+2) z r := by
  have hm (i : Fin 3) := OutgoingModeGluing.actual_exterior_moment n hn z hz T hT u i
    (raised p l i) (l+2) (raised_homogeneous p l hp i) (raised_harmonic p l hp hh i)
  choose c hc using hm
  refine ⟨∑ i : Fin 3, c i, ?_⟩
  filter_upwards [ae_all_iff.mpr hc] with r hr
  simp only [raisedMoment, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun i _ => hr i)

end OQ14.Packet04RaisingMoments
#print axioms OQ14.Packet04RaisingMoments.raised_radial_gradient
#print axioms OQ14.Packet04RaisingMoments.raised_radial_tangential
#print axioms OQ14.Packet04RaisingMoments.actual_raised_outgoing
