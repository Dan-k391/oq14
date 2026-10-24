import HalfTurnVectorAction

/-! Equivariance of the Fourier transform, the longitudinal multiplier and the physical longitudinal
projection under the half-turn action, and commutation of the actual parity material block with it. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.HalfTurnParityEquivariance
open MeasureTheory OQ14.Maxwell OQ14.DynamicConvolution OQ14.HalfTurnVectorAction
open scoped FourierTransform SchwartzMap

/-- Composition of a Schwartz function with the half-turn. -/
def schwartzRot : 𝓢(FourierL2.Space, ℂ) →L[ℂ] 𝓢(FourierL2.Space, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ rot.toContinuousLinearEquiv

theorem schwartzRot_apply (f : 𝓢(FourierL2.Space, ℂ)) (x : FourierL2.Space) : schwartzRot f x=f (rot x) := rfl

theorem pb_embed (f : 𝓢(FourierL2.Space, ℂ)) : pb (FourierL2.embed f)=FourierL2.embed (schwartzRot f) := by
  apply Lp.ext
  filter_upwards [pb_ae (FourierL2.embed f),ae_rot (FourierL2.embed_ae f),
    FourierL2.embed_ae (schwartzRot f)] with x h1 h2 h3
  rw [h1,h2,h3,schwartzRot_apply]

theorem fourier_schwartzRot (f : 𝓢(FourierL2.Space, ℂ)) :
    SchwartzMap.fourierTransformCLE ℂ (schwartzRot f)=schwartzRot (SchwartzMap.fourierTransformCLE ℂ f) := by
  ext x
  change 𝓕 (fun y => f (rot y)) x=𝓕 (fun y => f y) (rot x)
  exact Real.fourierIntegral_comp_linearIsometry rot (fun y => f y) x

/-- The scalar Fourier equivalence commutes with the half-turn pullback. -/
theorem fourierEquiv_pb (g : FourierL2.ScalarL2) :
    FourierL2.fourierEquiv (pb g)=pb (FourierL2.fourierEquiv g) := by
  have hA : Continuous (fun g : FourierL2.ScalarL2 => FourierL2.fourierEquiv (pb g)) :=
    FourierL2.fourierEquiv.continuous.comp pb.continuous
  have hB : Continuous (fun g : FourierL2.ScalarL2 => pb (FourierL2.fourierEquiv g)) :=
    pb.continuous.comp FourierL2.fourierEquiv.continuous
  refine FourierL2.embed_denseRange.induction_on g (isClosed_eq hA hB) ?_
  intro f
  rw [pb_embed,FourierL2.fourierEquiv_embed,FourierL2.fourierEquiv_embed,pb_embed,fourier_schwartzRot]

theorem component_fourier (F : VectorFourier.VectorL2) (i : Fin 3) :
    component i (VectorFourier.fourier F)=FourierL2.fourierEquiv (component i F) := by
  change VectorFourier.scalarCoordinates (VectorFourier.coordinate i (VectorFourier.fourier F))=
    FourierL2.fourierEquiv (VectorFourier.scalarCoordinates (VectorFourier.coordinate i F))
  rw [VectorFourier.fourier_coordinate]
  simp [VectorFourier.scalarFourier]

/-- The vector Fourier transform commutes with the half-turn action. -/
theorem U_fourier (F : VectorFourier.VectorL2) :
    U (VectorFourier.fourier F)=VectorFourier.fourier (U F) := by
  apply vector_eq_of_component
  intro j
  calc component j (U (VectorFourier.fourier F))
      =(o j : ℂ) • pb (component j (VectorFourier.fourier F)) := component_U _ _
    _ =(o j : ℂ) • pb (FourierL2.fourierEquiv (component j F)) := by rw [component_fourier]
    _ =(o j : ℂ) • FourierL2.fourierEquiv (pb (component j F)) := by rw [fourierEquiv_pb]
    _ =FourierL2.fourierEquiv ((o j : ℂ) • pb (component j F)) :=
      (map_smul FourierL2.fourierEquiv _ _).symm
    _ =FourierL2.fourierEquiv (component j (U F)) := by rw [component_U]
    _ =component j (VectorFourier.fourier (U F)) := (component_fourier _ _).symm

theorem U_fourier_symm (G : VectorFourier.VectorL2) :
    U (VectorFourier.fourier.symm G)=VectorFourier.fourier.symm (U G) := by
  apply VectorFourier.fourier.injective
  rw [LinearIsometryEquiv.apply_symm_apply,←U_fourier,LinearIsometryEquiv.apply_symm_apply]


theorem symbol_cov (ξ ξ' : LongitudinalProjection.Frequency) (hξ : ∀ l,ξ' l=o l * ξ l)
    (z : LongitudinalProjection.Vector) (i : Fin 3) :
    (o i : ℂ) * LongitudinalProjection.symbol ξ' z i=
      LongitudinalProjection.symbol ξ ((WithLp.equiv 2 (Fin 3 → ℂ)).symm (fun l => (o l : ℂ) * z l)) i := by
  rw [LongitudinalProjection.symbol_coordinate,LongitudinalProjection.symbol_coordinate]
  have hden : ∑ j : Fin 3,(ξ' j : ℂ)^2=∑ j : Fin 3,(ξ j : ℂ)^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hξ j]
    push_cast
    have h := o_sq_c j
    calc ((o j : ℂ)*(ξ j : ℂ))^2=((o j : ℂ)*(o j : ℂ))*(ξ j : ℂ)^2 := by ring
      _=_ := by rw [h,one_mul]
  have hnum : ∑ j : Fin 3,(ξ' j : ℂ)*z j=∑ j : Fin 3,(ξ j : ℂ)*((o j : ℂ)*z j) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hξ j]
    push_cast
    ring
  simp only [WithLp.equiv_symm_pi_apply]
  rw [hden,hnum,hξ i]
  push_cast
  linear_combination ((∑ j : Fin 3,(ξ j : ℂ)*((o j : ℂ)*z j))/(∑ j : Fin 3,(ξ j : ℂ)^2)*(ξ i : ℂ))*o_sq_c i

/-- The longitudinal Fourier multiplier commutes with the half-turn action. -/
theorem U_multiplier (G : VectorFourier.VectorL2) :
    U (LongitudinalProjection.multiplier G)=LongitudinalProjection.multiplier (U G) := by
  apply vector_ext_pt
  intro i
  have hM := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae G)
  have hM' := VectorFourier.coordinateMap_preserving.quasiMeasurePreserving.ae
    (LongitudinalProjection.multiplier_ae (U G))
  have hUl : ∀ᵐ x ∂(volume : Measure FourierL2.Space),∀ l : Fin 3,
      U G (VectorFourier.coordinateMap x) l=(o l : ℂ)*G (VectorFourier.coordinateMap (rot x)) l :=
    ae_all_iff.mpr (fun l => U_ae G l)
  filter_upwards [U_ae (LongitudinalProjection.multiplier G) i,ae_rot hM,hM',hUl] with x h1 h2 h3 h4
  rw [h1,h2,h3]
  have hv : U G (VectorFourier.coordinateMap x)=
      (WithLp.equiv 2 (Fin 3 → ℂ)).symm (fun l => (o l : ℂ)*G (VectorFourier.coordinateMap (rot x)) l) := by
    ext l
    rw [h4 l]
    simp
  rw [hv]
  exact symbol_cov (VectorFourier.coordinateMap x) (VectorFourier.coordinateMap (rot x))
    (fun l => rot_coordinate x l) _ i

/-- The physical longitudinal projection commutes with the half-turn action. -/
theorem U_physicalProjection (F : VectorFourier.VectorL2) :
    U (VectorFourier.physicalProjection F)=VectorFourier.physicalProjection (U F) := by
  unfold VectorFourier.physicalProjection
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [U_fourier_symm,U_multiplier,U_fourier]

/-- The actual parity material block of a half-turn symmetric coefficient commutes with the
half-turn action. No hypothesis on the physical projection is needed. -/
theorem block_comm (c : StaticCoefficient.Coefficient) (hsym : Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) (k B : ℝ) (u : VectorFourier.VectorL2) :
    U (ParityMaterialField.block d k B u)=ParityMaterialField.block d k B (U u) := by
  unfold ParityMaterialField.block ParityReactionVolume.perturbation StaticCoefficient.weightedBlock
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,map_sub,map_add,map_smul]
  rw [sqrtMultiplier_comm c hsym,U_physicalProjection,sqrtMultiplier_comm c hsym,
    weightedRemainder_comm c hsym k d.radius d.ballZero,parity_operator_comm c hsym d true k,
    parity_operator_comm c hsym d false k]

/-- Inverse of an invertible block that commutes with the half-turn action preserves fixed vectors. -/
theorem inverse_fixed (A : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2)
    (hA : ∀ u,U (A u)=A (U u)) (hu : IsUnit A) (f : VectorFourier.VectorL2) (hf : U f=f) :
    U (Ring.inverse A f)=Ring.inverse A f := by
  have h1 : A (Ring.inverse A f)=f :=
    congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L f)
      (Ring.mul_inverse_cancel A hu)
  have h2 : A (U (Ring.inverse A f))=A (Ring.inverse A f) := by
    rw [←hA,h1,hf]
  have h3 := congrArg (fun v => Ring.inverse A v) h2
  have hl : ∀ v,Ring.inverse A (A v)=v := fun v =>
    congrArg (fun L : VectorFourier.VectorL2 →L[ℂ] VectorFourier.VectorL2 => L v)
      (Ring.inverse_mul_cancel A hu)
  simp only [hl] at h3
  exact h3

/-- The parity solution of half-turn-fixed data is half-turn fixed, given a unit block. -/
theorem solution_fixed (c : StaticCoefficient.Coefficient) (hsym : Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) (k B : ℝ)
    (hu : IsUnit (ParityMaterialField.block d k B)) (f : VectorFourier.VectorL2) (hf : U f=f) :
    U (ParityMaterialField.solution d k B f)=ParityMaterialField.solution d k B f :=
  inverse_fixed _ (block_comm c hsym d k B) hu f hf

/-- Under the explicit smallness hypothesis already used for the parity solution. -/
theorem solution_fixed_of_small (c : StaticCoefficient.Coefficient) (hsym : Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) (k B : ℝ)
    (hsmall : ParityReactionVolume.perturbationBound d k B<1) (f : VectorFourier.VectorL2)
    (hf : U f=f) :
    U (ParityMaterialField.solution d k B f)=ParityMaterialField.solution d k B f :=
  solution_fixed c hsym d k B (ParityReactionVolume.explicitBlock_isUnit d k B hsmall) f hf

/-- The weighted source of the parity solution of fixed data is almost everywhere half-turn invariant
in the sense `source (O y) j = O_j * source y j`, i.e. `HalfTurnMaxwellParity.Invariant` almost everywhere. -/
theorem solution_source_invariant_ae (c : StaticCoefficient.Coefficient) (hsym : Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) (k B : ℝ)
    (hu : IsUnit (ParityMaterialField.block d k B)) (f : VectorFourier.VectorL2) (hf : U f=f) (j : Fin 3) :
    ∀ᵐ y ∂(volume : Measure FourierL2.Space),
      DynamicVolume.source c (ParityMaterialField.solution d k B f) j (rot y)=
        (o j : ℂ)*DynamicVolume.source c (ParityMaterialField.solution d k B f) j y :=
  source_invariant_ae c hsym _ (solution_fixed c hsym d k B hu f hf) j

end OQ14.HalfTurnParityEquivariance
#print axioms OQ14.HalfTurnParityEquivariance.schwartzRot_apply
#print axioms OQ14.HalfTurnParityEquivariance.pb_embed
#print axioms OQ14.HalfTurnParityEquivariance.fourier_schwartzRot
#print axioms OQ14.HalfTurnParityEquivariance.fourierEquiv_pb
#print axioms OQ14.HalfTurnParityEquivariance.component_fourier
#print axioms OQ14.HalfTurnParityEquivariance.U_fourier
#print axioms OQ14.HalfTurnParityEquivariance.U_fourier_symm
#print axioms OQ14.HalfTurnParityEquivariance.symbol_cov
#print axioms OQ14.HalfTurnParityEquivariance.U_multiplier
#print axioms OQ14.HalfTurnParityEquivariance.U_physicalProjection
#print axioms OQ14.HalfTurnParityEquivariance.block_comm
#print axioms OQ14.HalfTurnParityEquivariance.inverse_fixed
#print axioms OQ14.HalfTurnParityEquivariance.solution_fixed
#print axioms OQ14.HalfTurnParityEquivariance.solution_fixed_of_small
#print axioms OQ14.HalfTurnParityEquivariance.solution_source_invariant_ae
