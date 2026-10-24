import HalfTurnReactionKernel
import ParityMaterialField
import MaterialVolumeConverse

/-! The natural action of the proper half-turn `O = diag(-sign)` on vector L2:
`(U F)(x) = O (F (O x))`, its basic properties, and equivariance of the square-root multiplier,
the parity reaction operators and the dynamic remainder sandwich for half-turn symmetric
coefficients. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace OQ14.HalfTurnVectorAction
open MeasureTheory OQ14.Maxwell OQ14.DynamicConvolution
open OQ14.SphereReactionKernel (sign)

abbrev ScalarL2 := FourierL2.ScalarL2
abbrev VectorL2 := VectorFourier.VectorL2
abbrev Space := Maxwell.Space

/-- The half-turn as a linear isometry equivalence. -/
abbrev rot : Space ≃ₗᵢ[ℝ] Space := HarmonicHalfTurn.rotation

theorem rot_mp : MeasurePreserving rot (volume : Measure Space) volume := rot.measurePreserving

theorem rot_rot (x : Space) : rot (rot x)=x := HarmonicHalfTurn.rotation_involutive x

/-- Entries of the diagonal orthogonal involution `O`. -/
def o (i : Fin 3) : ℝ := -sign i

theorem o_sq (i : Fin 3) : o i * o i=1 := by
  unfold o sign
  split_ifs <;> norm_num

theorem o_sq_c (i : Fin 3) : (o i : ℂ) * (o i : ℂ)=1 := by
  have := congrArg (fun r : ℝ => (r : ℂ)) (o_sq i)
  simpa using this

/-- Scalar pullback by the half-turn. -/
def pb : ScalarL2 →L[ℂ] ScalarL2 :=
  (Lp.compMeasurePreservingₗᵢ ℂ (rot : Space → Space) rot_mp).toContinuousLinearMap

theorem pb_ae (g : ScalarL2) : pb g =ᵐ[volume] fun x => g (rot x) :=
  Lp.coeFn_compMeasurePreserving g rot_mp

theorem ae_rot {p : Space → Prop} (h : ∀ᵐ x ∂(volume : Measure Space),p x) :
    ∀ᵐ x ∂(volume : Measure Space),p (rot x) :=
  rot_mp.quasiMeasurePreserving.ae h

theorem pb_pb (g : ScalarL2) : pb (pb g)=g := by
  apply Lp.ext
  filter_upwards [pb_ae (pb g),ae_rot (pb_ae g)] with x h1 h2
  rw [h1,h2,rot_rot]

/-- The half-turn action on vector L2. -/
def U : VectorL2 →L[ℂ] VectorL2 :=
  ∑ i : Fin 3,(insert i) ∘L ((o i : ℂ) • pb) ∘L (component i)

theorem component_U (j : Fin 3) (F : VectorL2) :
    component j (U F)=(o j : ℂ) • pb (component j F) := by
  simp only [U,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum,component_insert,
    ContinuousLinearMap.smul_apply]
  simp

theorem vector_eq_of_component (F G : VectorL2) (h : ∀ i,component i F=component i G) : F=G :=
  MaterialVolumeConverse.vector_ext F G (fun i => by
    rw [←component_apply,←component_apply,h i])

theorem U_U (F : VectorL2) : U (U F)=F := by
  apply vector_eq_of_component
  intro j
  rw [component_U,component_U,map_smul,smul_smul,pb_pb,o_sq_c,one_smul]

theorem component_ae (F : VectorL2) (j : Fin 3) :
    component j F =ᵐ[volume] fun x => F (VectorFourier.coordinateMap x) j :=
  NewtonL2.physicalCoordinate_ae F j

/-- Pointwise form of the half-turn action. -/
theorem U_ae (F : VectorL2) (j : Fin 3) :
    (fun x => U F (VectorFourier.coordinateMap x) j) =ᵐ[volume]
      fun x => (o j : ℂ) * F (VectorFourier.coordinateMap (rot x)) j := by
  filter_upwards [component_ae (U F) j,ae_rot (component_ae F j),pb_ae (component j F),
    Lp.coeFn_smul (o j : ℂ) (pb (component j F))] with x h1 h2 h3 h4
  rw [←h1,component_U,h4]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [h3,h2]


theorem rot_coordinate (x : Space) (i : Fin 3) : rot x i=o i * x i := by
  rw [HalfTurnReactionKernel.rotation_coordinate]
  simp [o]

theorem o_cases (i : Fin 3) : (o i : ℂ)=1 ∨ (o i : ℂ)=-1 := by
  unfold o sign
  split_ifs <;> simp

theorem rot_reflect (x : Space) : rot (SphereReactionKernel.reflect x)=-x := by
  ext l
  rw [rot_coordinate]
  simp [SphereReactionKernel.reflect,o,SphereReactionKernel.sign]
  split_ifs <;> simp

theorem reflect_rot (x : Space) : SphereReactionKernel.reflect (rot x)=-x := by
  ext l
  simp only [SphereReactionKernel.reflect,rot_coordinate,o,PiLp.neg_apply,WithLp.equiv_symm_pi_apply]
  have : sign l * sign l=1 := by unfold sign; split_ifs <;> norm_num
  linear_combination (-(x l))*this

/-- Symmetric coefficient: the susceptibility is invariant under the half-turn. -/
def Symmetric (c : StaticCoefficient.Coefficient) : Prop :=
  ∀ x : Space,c.value (VectorFourier.coordinateMap (rot x))=c.value (VectorFourier.coordinateMap x)

theorem vector_ext_pt (F G : VectorL2)
    (h : ∀ i,(fun x => F (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => G (VectorFourier.coordinateMap x) i) : F=G := by
  apply MaterialVolumeConverse.vector_ext
  intro i
  filter_upwards [NewtonL2.physicalCoordinate_ae F i,NewtonL2.physicalCoordinate_ae G i,h i] with x h1 h2 h3
  rw [h1,h2]
  exact h3

theorem source_U (c : StaticCoefficient.Coefficient) (hsym : Symmetric c) (u : VectorL2) (j : Fin 3) :
    (fun y => DynamicVolume.source c (U u) j y) =ᵐ[volume]
      fun y => (o j : ℂ) * DynamicVolume.source c u j (rot y) := by
  filter_upwards [U_ae u j] with y hy
  unfold DynamicVolume.source
  rw [hy,←hsym y]
  ring

theorem sqrt_pt (c : StaticCoefficient.Coefficient) (u : VectorL2) (i : Fin 3) :
    (fun x => StaticCoefficient.sqrtMultiplier c u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => DynamicVolume.source c u i x := by
  filter_upwards [NewtonL2.physicalCoordinate_ae (StaticCoefficient.sqrtMultiplier c u) i,
    StaticNewton.material_source_ae c u i] with x h1 h2
  rw [←h1,h2]
  rfl

/-- The square-root multiplier of a symmetric coefficient commutes with the half-turn action. -/
theorem sqrtMultiplier_comm (c : StaticCoefficient.Coefficient) (hsym : Symmetric c) (u : VectorL2) :
    U (StaticCoefficient.sqrtMultiplier c u)=StaticCoefficient.sqrtMultiplier c (U u) := by
  apply vector_ext_pt
  intro i
  filter_upwards [U_ae (StaticCoefficient.sqrtMultiplier c u) i,ae_rot (sqrt_pt c u i),
    sqrt_pt c (U u) i,source_U c hsym u i] with x h1 h2 h3 h4
  rw [h1,h2,h3,h4]

/-- Abstract equivariance of kernel operators of the weighted-source form. -/
theorem kernel_comm (c : StaticCoefficient.Coefficient) (hsym : Symmetric c)
    (T : VectorL2 →L[ℂ] VectorL2) (K : Space → Space → Fin 3 → Fin 3 → ℂ)
    (hK : ∀ x y i j,K (rot x) (rot y) i j=(o i : ℂ)*(o j : ℂ)*K x y i j)
    (hT : ∀ u i,(fun x => T u (VectorFourier.coordinateMap x) i) =ᵐ[volume]
      fun x => (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) *
        ∑ j : Fin 3,∫ y,K x y i j * DynamicVolume.source c u j y) (u : VectorL2) :
    U (T u)=T (U u) := by
  apply vector_ext_pt
  intro i
  have I1 (x : Space) (j : Fin 3) : (∫ y,K (rot x) y i j * DynamicVolume.source c u j y)=
      (o i : ℂ)*(o j : ℂ)*∫ y,K x (rot y) i j * DynamicVolume.source c u j y := by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    have := hK x (rot y) i j
    rw [rot_rot] at this
    rw [this]
    ring
  have I2 (x : Space) (j : Fin 3) : (∫ y,K x y i j * DynamicVolume.source c (U u) j y)=
      (o j : ℂ)*∫ y,K x (rot y) i j * DynamicVolume.source c u j y := by
    have h3 : (∫ y,K x y i j * DynamicVolume.source c (U u) j y)=
        ∫ y,(o j : ℂ)*(K x y i j * DynamicVolume.source c u j (rot y)) := by
      apply integral_congr_ae
      filter_upwards [source_U c hsym u j] with y hy
      rw [hy]
      ring
    have h4 := rot_mp.integral_comp rot.toHomeomorph.measurableEmbedding
      (fun y' => K x (rot y') i j * DynamicVolume.source c u j y')
    simp only [rot_rot] at h4
    rw [h3,integral_const_mul]
    congr 1
  filter_upwards [U_ae (T u) i,ae_rot (hT u i),hT (U u) i] with x h1 h2 h3
  rw [h1,h3,h2,hsym x]
  simp only [I1,I2]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have := o_sq_c i
  linear_combination ((Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ)*(o j : ℂ)*
    ∫ y,K x (rot y) i j * DynamicVolume.source c u j y)*this


theorem o_abs (i : Fin 3) : ‖(o i : ℂ)‖=1 := by
  have h := o_sq i
  have h2 : |o i| * |o i|=1 := by rw [←abs_mul,h,abs_one]
  have h3 : |o i|=1 := by nlinarith [abs_nonneg (o i)]
  rw [Complex.norm_real,Real.norm_eq_abs]
  exact h3

theorem norm_sq_components (F : VectorL2) : ‖F‖^2=∑ i : Fin 3,‖component i F‖^2 := by
  have h := VectorFourier.components_norm F
  have h2 := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => VectorFourier.ScalarL2) (VectorFourier.componentsLinear F)
  rw [h] at h2
  rw [h2]
  apply Finset.sum_congr rfl
  intro i _
  change ‖VectorFourier.coordinate i F‖^2=‖VectorFourier.scalarCoordinates (VectorFourier.coordinate i F)‖^2
  rw [VectorFourier.scalarCoordinates.norm_map]

theorem norm_pb (g : ScalarL2) : ‖pb g‖=‖g‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (rot : Space → Space) rot_mp).norm_map g

/-- The half-turn action is an isometry. -/
theorem norm_U (F : VectorL2) : ‖U F‖=‖F‖ := by
  have h : ‖U F‖^2=‖F‖^2 := by
    rw [norm_sq_components,norm_sq_components]
    apply Finset.sum_congr rfl
    intro i _
    rw [component_U,norm_smul,o_abs,one_mul,norm_pb]
  nlinarith [norm_nonneg (U F),norm_nonneg F]

theorem U_eq_iff (F : VectorL2) :
    U F=F ↔ ∀ j,∀ᵐ x ∂(volume : Measure Space),
      F (VectorFourier.coordinateMap (rot x)) j=(o j : ℂ)*F (VectorFourier.coordinateMap x) j := by
  constructor
  · intro h j
    filter_upwards [U_ae F j] with x hy
    rw [h] at hy
    rw [hy]
    linear_combination (-(F (VectorFourier.coordinateMap (rot x)) j))*o_sq_c j
  · intro h
    apply vector_ext_pt
    intro j
    filter_upwards [U_ae F j,h j] with x hx hy
    rw [hx,hy]
    linear_combination (F (VectorFourier.coordinateMap x) j)*o_sq_c j

/-- A half-turn-fixed vector has almost everywhere half-turn-invariant weighted source. -/
theorem source_invariant_ae (c : StaticCoefficient.Coefficient) (hsym : Symmetric c) (u : VectorL2)
    (hu : U u=u) (j : Fin 3) :
    ∀ᵐ y ∂(volume : Measure Space),
      DynamicVolume.source c u j (rot y)=(o j : ℂ)*DynamicVolume.source c u j y := by
  filter_upwards [(U_eq_iff u).mp hu j] with y hy
  unfold DynamicVolume.source
  rw [hsym y,hy]
  ring

/-- The weighted vector `sqrtMultiplier c u` is half-turn fixed whenever `u` is. -/
theorem sqrtMultiplier_fixed (c : StaticCoefficient.Coefficient) (hsym : Symmetric c) (u : VectorL2)
    (hu : U u=u) : U (StaticCoefficient.sqrtMultiplier c u)=StaticCoefficient.sqrtMultiplier c u := by
  rw [sqrtMultiplier_comm c hsym,hu]


theorem reaction_rot (e : Bool) (k : ℝ) (x y : Space) (i j : Fin 3) :
    SphereReactionKernel.reaction e k (rot x) (rot y) i j=
      (o i : ℂ)*(o j : ℂ)*SphereReactionKernel.reaction e k x y i j := by
  have h1 : SphereReactionKernel.J k (rot x-rot y) i j=
      (sign i : ℂ)*(sign j : ℂ)*SphereReactionKernel.J k (x-y) i j := by
    rw [←map_sub]
    exact HalfTurnReactionKernel.J_rotation k (x-y) i j
  have h2 : SphereReactionKernel.J k (SphereReactionKernel.reflect (rot x)-rot y) i j=
      (sign i : ℂ)*(sign j : ℂ)*SphereReactionKernel.J k (SphereReactionKernel.reflect x-y) i j := by
    have : SphereReactionKernel.reflect (rot x)-rot y=rot (SphereReactionKernel.reflect x-y) := by
      rw [map_sub,rot_reflect,reflect_rot]
    rw [this]
    exact HalfTurnReactionKernel.J_rotation k _ i j
  unfold SphereReactionKernel.reaction
  rw [h1,h2]
  have ho : ∀ l : Fin 3,(o l : ℂ)=-(sign l : ℂ) := fun l => by simp [o]
  rw [ho i,ho j]
  ring

theorem remainder_rot (k : ℝ) (z : Space) (i j : Fin 3) :
    DyadicKernel.remainder k (rot z) i j=(o i : ℂ)*(o j : ℂ)*DyadicKernel.remainder k z i j := by
  unfold DyadicKernel.remainder DyadicKernel.dyadic GreenKernel.phiHessian GreenKernel.phi
  have hn : ‖rot z‖=‖z‖ := rot.norm_map z
  have hc (l : Fin 3) : ((rot z l : ℝ) : ℂ)=(o l : ℂ)*(z l : ℂ) := by
    rw [rot_coordinate]
    push_cast
    ring
  simp only [hn,hc]
  by_cases hij : i=j
  · subst hij
    rcases o_cases i with h | h
    · simp only [h]
      ring
    · simp only [h]
      ring
  · simp only [hij,if_false]
    ring

/-- The parity reaction operators of a symmetric coefficient commute with the half-turn action. -/
theorem parity_operator_comm (c : StaticCoefficient.Coefficient) (hsym : Symmetric c)
    (d : BoundedMaterialKernel.SupportData c) (e : Bool) (k : ℝ) (u : VectorL2) :
    U (ParityReactionVolume.operator d e k u)=ParityReactionVolume.operator d e k (U u) :=
  kernel_comm c hsym (ParityReactionVolume.operator d e k)
    (fun x y i j => SphereReactionKernel.reaction e k x y i j) (reaction_rot e k)
    (fun u i => ParityReactionVolume.operator_actual d e k u i) u

/-- The dynamic remainder sandwich of a symmetric coefficient commutes with the half-turn action. -/
theorem weightedRemainder_comm (c : StaticCoefficient.Coefficient) (hsym : Symmetric c) (k R : ℝ)
    (hc : ∀ x : Space,x ∉ Metric.closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (u : VectorL2) :
    U (DynamicVolume.weightedRemainder c k R u)=DynamicVolume.weightedRemainder c k R (U u) :=
  kernel_comm c hsym (DynamicVolume.weightedRemainder c k R)
    (fun x y i j => DyadicKernel.remainder k (x-y) i j)
    (fun x y i j => by
      show DyadicKernel.remainder k (rot x-rot y) i j=
        (o i : ℂ)*(o j : ℂ)*DyadicKernel.remainder k (x-y) i j
      rw [←map_sub]
      exact remainder_rot k (x-y) i j)
    (fun u i => DynamicVolume.weightedRemainder_actual c u k R hc i) u

end OQ14.HalfTurnVectorAction
#print axioms OQ14.HalfTurnVectorAction.rot_mp
#print axioms OQ14.HalfTurnVectorAction.rot_rot
#print axioms OQ14.HalfTurnVectorAction.o_sq
#print axioms OQ14.HalfTurnVectorAction.o_sq_c
#print axioms OQ14.HalfTurnVectorAction.pb_ae
#print axioms OQ14.HalfTurnVectorAction.ae_rot
#print axioms OQ14.HalfTurnVectorAction.pb_pb
#print axioms OQ14.HalfTurnVectorAction.component_U
#print axioms OQ14.HalfTurnVectorAction.vector_eq_of_component
#print axioms OQ14.HalfTurnVectorAction.U_U
#print axioms OQ14.HalfTurnVectorAction.component_ae
#print axioms OQ14.HalfTurnVectorAction.U_ae
#print axioms OQ14.HalfTurnVectorAction.rot_coordinate
#print axioms OQ14.HalfTurnVectorAction.o_cases
#print axioms OQ14.HalfTurnVectorAction.rot_reflect
#print axioms OQ14.HalfTurnVectorAction.reflect_rot
#print axioms OQ14.HalfTurnVectorAction.vector_ext_pt
#print axioms OQ14.HalfTurnVectorAction.source_U
#print axioms OQ14.HalfTurnVectorAction.sqrt_pt
#print axioms OQ14.HalfTurnVectorAction.sqrtMultiplier_comm
#print axioms OQ14.HalfTurnVectorAction.kernel_comm
#print axioms OQ14.HalfTurnVectorAction.o_abs
#print axioms OQ14.HalfTurnVectorAction.norm_sq_components
#print axioms OQ14.HalfTurnVectorAction.norm_pb
#print axioms OQ14.HalfTurnVectorAction.norm_U
#print axioms OQ14.HalfTurnVectorAction.U_eq_iff
#print axioms OQ14.HalfTurnVectorAction.source_invariant_ae
#print axioms OQ14.HalfTurnVectorAction.sqrtMultiplier_fixed
#print axioms OQ14.HalfTurnVectorAction.reaction_rot
#print axioms OQ14.HalfTurnVectorAction.remainder_rot
#print axioms OQ14.HalfTurnVectorAction.parity_operator_comm
#print axioms OQ14.HalfTurnVectorAction.weightedRemainder_comm
