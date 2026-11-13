import Packet05AssembleTangentialArrays
import Packet05PlateauGraphFlux

/-! A single uniform L² ceiling for all explicit plateau-cutoff arrays. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05AssembledArrayCeiling
open Maxwell WeakCurl WeakPoynting WeakGreen WeakConservation DivCurlCompact
  Packet05QuantitativeLocalArrays Packet05PlateauGraphFlux MaxwellCutoffCommutator

def ceiling (a b c L0 L1 L2 : ℝ) : ℝ :=
  max (a*L0) (max (a*L1+b*L0) (a*L2+2*b*L1+c*L0))

theorem assembled_ceiling (θ : Test) (hθ2 : ContDiff ℝ 2 θ.function)
    (C : L2Vector) (D : Fin 3 → L2Vector) (H : Fin 3 → Fin 3 → L2Vector)
    (a b c L0 L1 L2 : ℝ) (ha : ∀ x, ‖θ.function x‖ ≤ a)
    (hb : ∀ i x, ‖dcoord θ.function x i‖ ≤ b)
    (hc : ∀ i j x, ‖dcoord (derivativeCutoff θ hθ2 i).function x j‖ ≤ c)
    (hC : ∀ j, ‖C j‖ ≤ L0) (hD : ∀ i j, ‖D i j‖ ≤ L1)
    (hH : ∀ i t j, ‖H i t j‖ ≤ L2) :
    (∀ j, ‖cutVector θ C j‖ ≤ ceiling a b c L0 L1 L2) ∧
    (∀ i j, ‖first θ C D i j‖ ≤ ceiling a b c L0 L1 L2) ∧
    (∀ i t j, ‖second θ hθ2 C D H i t j‖ ≤ ceiling a b c L0 L1 L2) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 0)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0 0)
  constructor
  · intro j
    have h := InteriorTestDensity.scaleL2_norm_le θ.function θ.regular.continuous θ.compact (C j) ha
    exact (h.trans (mul_le_mul_of_nonneg_left (hC j) ha0)).trans (le_max_left _ _)
  constructor
  · intro i j
    have h := first_norm θ C D i j a b ha hb
    have hm := add_le_add (mul_le_mul_of_nonneg_left (hD i j) ha0) (mul_le_mul_of_nonneg_left (hC j) hb0)
    exact (h.trans hm).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro i t j
    have h := second_norm θ hθ2 C D H i t j a b c ha hb hc
    have h1 := mul_le_mul_of_nonneg_left (hH i t j) ha0
    have h2 := mul_le_mul_of_nonneg_left (hD i j) hb0
    have h3 := mul_le_mul_of_nonneg_left (hD t j) hb0
    have h4 := mul_le_mul_of_nonneg_left (hC j) hc0
    have hm : a*‖H i t j‖+b*‖D i j‖+b*‖D t j‖+c*‖C j‖ ≤
        a*L2+2*b*L1+c*L0 := by nlinarith only [h1,h2,h3,h4]
    exact (h.trans hm).trans ((le_max_right _ _).trans (le_max_right _ _))

end OQ14.Packet05AssembledArrayCeiling
#print axioms OQ14.Packet05AssembledArrayCeiling.assembled_ceiling
