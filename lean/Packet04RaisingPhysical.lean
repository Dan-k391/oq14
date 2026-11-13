import Packet04RaisingMoments
import Packet04RaisingSelection

/-! The actual Cartesian outgoing condition selects the physical TM degree
once its actual radial/poloidal representatives and radial ODE are available. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet04RaisingPhysical
open Complex MeasureTheory Set OQ14.HarmonicPolynomial OQ14.HarmonicMomentIntegrability
  OQ14.Packet04RaisingMoments

theorem actual_TM_outgoing
    (n : ℝ) (hn : 1 < n) (z : ℂ) (hz : z ≠ 0) (T : ℝ) (hT : 1 < T)
    (u : VectorFourier.VectorL2) (p : Poly) (l : ℕ)
    (hp : p.IsHomogeneous (l+1)) (hh : formalLaplacian p = 0)
    (f df : ℝ → ℂ)
    (hf : ∀ r ∈ Ioo 1 T, HasDerivAt f (df r) r)
    (hdf : ∀ r ∈ Ioo 1 T, HasDerivAt df (RadialRellich.radialCoefficient (l+1) z r * f r) r)
    (hactual : ∀ᵐ r : ℝ ∂volume.restrict (Ioo 1 T),
      let E := fun i => NewtonL2.physicalCoordinate
        (ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u) i
      ((r : ℂ)^2 * radialMoment E p r = ((l+1 : ℂ)*(l+2 : ℂ))*f r) ∧
      ((r : ℂ) * tangentialMoment E p l r = ((l+1 : ℂ)*(l+2 : ℂ))*df r)) :
    ∃ a : ℂ, ∀ r ∈ Ioo 1 T, f r = a * RadialRellich.outgoing (l+1) z r := by
  let V := ComplexExteriorResponse.response (ModalWeightedMode.coefficient n hn) z 1 T u
  let E := fun i => NewtonL2.physicalCoordinate V i
  let lam : ℂ := (l+1 : ℂ)*(l+2 : ℂ)
  let d : ℂ := 2*(l : ℂ)+3
  have hlam : lam ≠ 0 := mul_ne_zero (by exact_mod_cast (show l+1 ≠ 0 by omega))
    (by exact_mod_cast (show l+2 ≠ 0 by omega))
  have hd : d ≠ 0 := by dsimp [d]; exact_mod_cast (show 2*(l : ℝ)+3 ≠ 0 by positivity)
  obtain ⟨c,hc⟩ := actual_raised_outgoing n hn z hz T hT u p l hp hh
  apply Packet04RaisingSelection.ode_raised_outgoing_selection (l+1) z hz T hT f df hf hdf
    (c*d/(lam*z))
  have hm := ae_restrict_of_ae_restrict_of_subset
    (show Ioo (1 : ℝ) T ⊆ Ioi (0 : ℝ) from fun _ hr => lt_trans (by norm_num) hr.1)
    (raised_radial_tangential V p l)
  filter_upwards [hactual, hc, hm, ae_restrict_mem measurableSet_Ioo] with r ha hc hm hr
  have h1 : (r : ℂ)^2 * radialMoment E p r = lam*f r := ha.1
  have h2 : (r : ℂ) * tangentialMoment E p l r = lam*df r := ha.2
  change (r : ℂ)*raisedMoment V p l r = c*RadialRellich.outgoing (l+2) z r at hc
  rw [hm] at hc
  change (r : ℂ) * (((l+2 : ℂ)*radialMoment E p r-tangentialMoment E p l r)/d) = _ at hc
  have h3 : (r : ℂ)*((l+2 : ℂ)*radialMoment E p r-tangentialMoment E p l r) =
      c*RadialRellich.outgoing (l+2) z r*d := by
    apply (div_eq_iff hd).mp
    simpa only [mul_div_assoc] using hc
  have hid : lam * ((l+2 : ℂ)*f r-(r : ℂ)*df r) =
      c*d*(r : ℂ)*RadialRellich.outgoing (l+2) z r := by
    linear_combination (r : ℂ)*h3 - (l+2 : ℂ)*h1 + (r : ℂ)*h2
  have he : (c*d/(lam*z))*(z*r) = c*d*(r : ℂ)/lam := by field_simp [hlam,hz]; ring
  simp only [Nat.cast_add, Nat.cast_one, show l+1+1 = l+2 by omega]
  rw [he]
  apply mul_left_cancel₀ hlam
  calc
    _ = c*d*(r : ℂ)*RadialRellich.outgoing (l+2) z r := by
      convert hid using 1; ring
    _ = _ := by field_simp [hlam]

end OQ14.Packet04RaisingPhysical
#print axioms OQ14.Packet04RaisingPhysical.actual_TM_outgoing
