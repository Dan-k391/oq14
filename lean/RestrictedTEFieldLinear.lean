import RestrictedTEScale

/-! Actual linear maps of finite harmonic coefficient data to the complete regular TE E/H fields. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.RestrictedTEFieldLinear
open Complex Maxwell RestrictedTEIncoming RestrictedTEPlaneLocal SymmetricHarmonicJets

def electricMap : (Index →₀ ℂ) →ₗ[ℂ] Field :=
  Finsupp.linearCombination ℂ (fun q x i => ((4*Real.pi : ℂ)*I^q.val.1)*
    DebyeMaxwell.teElectric (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) x i)

def magneticMap : (Index →₀ ℂ) →ₗ[ℂ] Field :=
  Finsupp.linearCombination ℂ (fun q x i => ((4*Real.pi : ℂ)*I^q.val.1)*
    DebyeMaxwell.teMagnetic 1 (SolidScalarHelmholtz.wave q.val.1 1 (polynomial q)) x i)

theorem electricMap_apply (A : Index →₀ ℂ) : electricMap A=electric A := by
  funext x i
  rw [show electric A x i=DebyeMaxwell.teElectric (RestrictedTEFields.potential 1 A) x i from rfl,electric_sum]
  simp only [electricMap,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  dsimp [coefficient]
  ring

theorem magneticMap_apply (A : Index →₀ ℂ) : magneticMap A=magnetic A := by
  funext x i
  rw [show magnetic A x i=DebyeMaxwell.teMagnetic 1 (RestrictedTEFields.potential 1 A) x i from rfl,magnetic_sum]
  simp only [magneticMap,Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  dsimp [coefficient]
  ring

theorem electric_add (A B : Index →₀ ℂ) : electric (A+B)=electric A+electric B := by
  rw [← electricMap_apply,map_add,electricMap_apply,electricMap_apply]

theorem magnetic_add (A B : Index →₀ ℂ) : magnetic (A+B)=magnetic A+magnetic B := by
  rw [← magneticMap_apply,map_add,magneticMap_apply,magneticMap_apply]

end OQ14.RestrictedTEFieldLinear
#print axioms OQ14.RestrictedTEFieldLinear.electricMap_apply
#print axioms OQ14.RestrictedTEFieldLinear.magneticMap_apply
#print axioms OQ14.RestrictedTEFieldLinear.electric_add
#print axioms OQ14.RestrictedTEFieldLinear.magnetic_add
