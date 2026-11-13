import Packet05ScalarResidualBound

/-! Separate principal and lower-order terms in the actual differentiated
scalar transmission identity. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet05ScalarEnergyIdentity
open MeasureTheory OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting
  OQ14.WeakGreen OQ14.DivCurlCompact OQ14.WeakPower
  OQ14.MaxwellWeakTranslation OQ14.MaxwellDifferenceQuotient
  OQ14.Packet05ScalarCutoffTesting OQ14.Packet05ScalarDielectricFlux
  OQ14.Packet05ScalarTransmissionCommutator OQ14.Packet05TensorCommutator
  OQ14.Packet05FlatWeight OQ14.Packet05ScalarTransmissionTest

theorem mulWeight_add (d : ℝ) (hd : 0 ≤ d) (u v : L2Scalar) :
    mulWeight d hd (u+v) = mulWeight d hd u + mulWeight d hd v := by
  apply Lp.ext
  filter_upwards [mulWeight_ae d hd (u+v), mulWeight_ae d hd u, mulWeight_ae d hd v,
    Lp.coeFn_add u v, Lp.coeFn_add (mulWeight d hd u) (mulWeight d hd v)] with x h0 h1 h2 ha hb
  rw [h0,ha,hb]
  simp only [Pi.add_apply]
  rw [h1,h2,mul_add]

theorem scalarProduct_add_left (u v w : L2Scalar) :
    scalarProduct (u+v) w = scalarProduct u w + scalarProduct v w := by
  simp only [scalarProduct_integral]
  rw [← integral_add (scalarProduct_integrable u w) (scalarProduct_integrable v w)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add u v] with x hx
  rw [hx]
  simp only [Pi.add_apply, add_mul]

theorem differentiatedFlux_split (A : Fin 3 → Fin 3 → Test) (C F : L2Vector)
    (d : ℝ) (hd : 0 ≤ d) (i j : Fin 3) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    differentiatedFlux A C F d hd i j h hh b hb =
      mulWeight d hd (matrixField A (fun l => quotient (C l) i h) j) +
        (mulWeight d hd (matrixResidual A C i j h hh b hb) - quotient (F j) i h) := by
  unfold differentiatedFlux
  rw [mulWeight_add]
  abel

theorem principal_energy_balance (A : Fin 3 → Fin 3 → Test) (u : L2Scalar)
    (C F : L2Vector) (d : ℝ) (hd : 0 ≤ d)
    (hC : ∀ j, HasWeakPartial u (C j) j)
    (hdiv : HasWeakDivergence (fun j => flux A C d hd j - F j) 0)
    (χ : Test) (i : Fin 3) (hi : i ≠ 2) (h : ℝ) (hh : h ≠ 0)
    (b : ℝ) (hb : ∀ p q l x, ‖dcoord (A p q).function x l‖ ≤ b) :
    (∑ j : Fin 3, scalarProduct
      (mulWeight d hd (matrixField A (fun l => quotient (C l) i h) j))
      (conjScalar (cutoffDerivative χ (quotient u i h) (fun l => quotient (C l) i h) j))) =
    -(∑ j : Fin 3, scalarProduct
      (mulWeight d hd (matrixResidual A C i j h hh b hb) - quotient (F j) i h)
      (conjScalar (cutoffDerivative χ (quotient u i h) (fun l => quotient (C l) i h) j))) := by
  have ht := differentiated_flux_test A u C F d hd hC hdiv χ i hi h hh b hb
  simp only [differentiatedFlux_split, scalarProduct_add_left] at ht
  simp only [Fin.sum_univ_three]
  linear_combination ht

end OQ14.Packet05ScalarEnergyIdentity
#print axioms OQ14.Packet05ScalarEnergyIdentity.mulWeight_add
#print axioms OQ14.Packet05ScalarEnergyIdentity.scalarProduct_add_left
#print axioms OQ14.Packet05ScalarEnergyIdentity.differentiatedFlux_split
#print axioms OQ14.Packet05ScalarEnergyIdentity.principal_energy_balance
