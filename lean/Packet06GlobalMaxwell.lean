import Packet06GlobalField

/-! The glued electric field and actual magnetic convolution form one globally
defined, locally L², outgoing electric Maxwell mode for every volume kernel. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06GlobalMaxwell
open MeasureTheory Metric DynamicSource Packet06GlobalField
open StaticCoefficient (Coefficient)
open WeakCurl (next previous)

theorem magnetic_memLp_ball (c : Coefficient) (z : ℂ) (S T : ℝ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : MemLp (fun x => ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i)
      2 (volume.restrict (closedBall 0 T)) :=
  ComplexMagneticLocal.magnetic_memLp_ball z T S (StaticCoefficient.sqrtMultiplier c u)
    (DynamicVolume.source c u) (DynamicVolume.source_integrable c u S hc)
    (DynamicVolume.source_zero c u S hc) (StaticNewton.material_source_ae c u) i

theorem global_first_order (c : Coefficient) (z : ℂ) (S : ℝ) (hS : 0 ≤ S) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z S u = 0) (i : Fin 3) (f : Test) :
    ((∫ x : Maxwell.Space, electric c z S u x (next i) * (testPartial (previous i) f).val x) -
      (∫ x : Maxwell.Space, electric c z S u x (previous i) * (testPartial (next i) f).val x) =
        Complex.I*z * (∫ x : Maxwell.Space, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x i * f.val x)) ∧
    ((∫ x : Maxwell.Space, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x (next i) * (testPartial (previous i) f).val x) -
      (∫ x : Maxwell.Space, ComplexMagneticLocal.magnetic z (DynamicVolume.source c u) x (previous i) * (testPartial (next i) f).val x) =
        -(Complex.I*z) * (∫ x : Maxwell.Space, (1+(c.value (VectorFourier.coordinateMap x) : ℂ))*
          electric c z S u x i*f.val x)) := by
  obtain ⟨T₀,hT₀⟩ := f.property.isBounded.subset_closedBall (0 : Maxwell.Space)
  let T := max T₀ (S+1)
  have hT : S+1 ≤ T := le_max_right _ _
  have hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T :=
    hT₀.trans (closedBall_subset_closedBall (le_max_left _ _))
  have hp (j : Fin 3) : tsupport ((testPartial j f).val : Maxwell.Space → ℂ) ⊆ closedBall 0 T :=
    (ComplexResponseRealWeak.partial_support j f).trans hf
  have he (a b : Fin 3) :
      (∫ x : Maxwell.Space, electric c z S u x a * (testPartial b f).val x) =
        ∫ x : Maxwell.Space, ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) a * (testPartial b f).val x := by
    simpa only [one_mul] using electric_test_integral c z S T hT u hc a (testPartial b f) (hp b) (fun _ => 1)
  rw [he,he,electric_test_integral c z S T hT u hc i f hf]
  exact Packet06KernelMaxwell.actual_first_order c z S T (by linarith) (by linarith) u hc hu i f hf

end OQ14.Packet06GlobalMaxwell
#print axioms OQ14.Packet06GlobalMaxwell.magnetic_memLp_ball
#print axioms OQ14.Packet06GlobalMaxwell.global_first_order
