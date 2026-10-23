import AngularFinitePairing

/-! Continuous actual sphere pairings of complex vector-valued continuous maps. -/
noncomputable section
set_option autoImplicit false
namespace OQ14.SphereVectorPairing
open MeasureTheory OQ14.Maxwell OQ14.SphereReactionKernel

def coordinate (i : Fin 3) : C(Sphere,Vector) →L[ℂ] C(Sphere,ℂ) :=
  (ContinuousLinearMap.proj i : Vector →L[ℂ] ℂ).compLeftContinuousCompact Sphere

theorem coordinate_apply (i : Fin 3) (F : C(Sphere,Vector)) (n : Sphere) : coordinate i F n=F n i := rfl

def pairing (F G : C(Sphere,Vector)) : ℂ :=
  AngularFinitePairing.integralMap
    (∑ i : Fin 3, coordinate i F*AngularFinitePairing.conjugateMap (coordinate i G))

theorem pairing_continuous : Continuous (fun p : C(Sphere,Vector) × C(Sphere,Vector) => pairing p.1 p.2) := by
  apply AngularFinitePairing.integralMap.continuous.comp
  apply continuous_finset_sum
  intro i _
  exact ((coordinate i).continuous.comp continuous_fst).mul
    (AngularFinitePairing.conjugateMap.continuous.comp ((coordinate i).continuous.comp continuous_snd))

theorem integrand_integrable (F G : C(Sphere,Vector)) :
    Integrable (fun n : Sphere => dot (F n) (conjugate (G n))) surface := by
  apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
  have hf (i : Fin 3) := (continuous_apply i).comp F.continuous
  have hg (i : Fin 3) := Complex.continuous_conj.comp ((continuous_apply i).comp G.continuous)
  exact (((hf 0).mul (hg 0)).add ((hf 1).mul (hg 1))).add ((hf 2).mul (hg 2))

theorem pairing_integral (F G : C(Sphere,Vector)) :
    pairing F G=∫ n : Sphere,dot (F n) (conjugate (G n)) ∂surface := by
  rw [pairing,AngularFinitePairing.integralMap_apply]
  apply integral_congr_ae
  filter_upwards with n
  simp [coordinate_apply,AngularFinitePairing.conjugateMap,Complex.conjCLE_apply,dot,conjugate,Fin.sum_univ_three]

theorem pairing_self (F : C(Sphere,Vector)) :
    (pairing F F).re=∫ n : Sphere,Maxwell.energy (F n) ∂surface := by
  rw [pairing_integral]
  simp_rw [Maxwell.dot_conjugate]
  exact congrArg Complex.re (integral_ofReal (𝕜 := ℂ) (μ := surface)
    (f := fun n : Sphere => Maxwell.energy (F n)))

end OQ14.SphereVectorPairing
#print axioms OQ14.SphereVectorPairing.coordinate_apply
#print axioms OQ14.SphereVectorPairing.pairing_continuous
#print axioms OQ14.SphereVectorPairing.integrand_integrable
#print axioms OQ14.SphereVectorPairing.pairing_integral
#print axioms OQ14.SphereVectorPairing.pairing_self
