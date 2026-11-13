import Packet06TranslationMaterial
import Packet06AxialConvolution

/-! Actual compact material source and dyadic potential under rigid translation. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.Packet06TranslationPotential
open MeasureTheory Maxwell Packet06TranslationL2 Packet06TranslationMaterial

theorem source_action (a : Space) (c : StaticCoefficient.Coefficient) (u : VectorFourier.VectorL2) (i : Fin 3) :
    DynamicVolume.source (coefficient a c) (action a u) i =ᵐ[volume]
      fun x => DynamicVolume.source c u i (x-a) := by
  filter_upwards [action_ae a u i] with x hx
  simp only [DynamicVolume.source, coefficient_value]
  rw [hx]

theorem potential_translate (a : Space) (c : StaticCoefficient.Coefficient) (k : ℝ)
    (u : VectorFourier.VectorL2) (x : Space) (i : Fin 3) :
    Packet06AxialConvolution.potential (coefficient a c) k (action a u) x i =
      Packet06AxialConvolution.potential c k u (x-a) i := by
  unfold Packet06AxialConvolution.potential
  apply Finset.sum_congr rfl
  intro j hj
  have hs : (∫ y : Space, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source (coefficient a c) (action a u) j y) =
      ∫ y : Space, DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j (y-a) := by
    apply integral_congr_ae
    filter_upwards [source_action a c u j] with y hy
    rw [hy]
  rw [hs]
  have h := integral_add_right_eq_self (μ := (volume : Measure Space))
    (fun y : Space => DyadicKernel.remainder k (x-y) i j * DynamicVolume.source c u j (y-a)) a
  rw [← h]
  apply integral_congr_ae
  filter_upwards with y
  have h1 : y+a-a = y := by abel
  have h2 : x-(y+a) = x-a-y := by abel
  rw [h1,h2]

end OQ14.Packet06TranslationPotential
#print axioms OQ14.Packet06TranslationPotential.source_action
#print axioms OQ14.Packet06TranslationPotential.potential_translate
