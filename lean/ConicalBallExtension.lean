import ConicalRungeBall

/-! Genuine bounded complex-linear zero extension of physical ball L2 incident data. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalBallExtension
open MeasureTheory Set Metric OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space

theorem scalar_memLp (a : ℝ) (f : ScalarBall a) :
    MemLp ((closedBall (0 : Space) a).indicator (f : Space → ℂ)) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_closedBall).mpr (Lp.memLp f)

def scalarExtension (a : ℝ) (f : ScalarBall a) : FourierL2.ScalarL2 :=
  (scalar_memLp a f).toLp ((closedBall (0 : Space) a).indicator (f : Space → ℂ))

theorem scalarExtension_ae (a : ℝ) (f : ScalarBall a) :
    scalarExtension a f =ᵐ[volume] (closedBall (0 : Space) a).indicator (f : Space → ℂ) :=
  (scalar_memLp a f).coeFn_toLp

theorem scalarExtension_add (a : ℝ) (f g : ScalarBall a) :
    scalarExtension a (f+g)=scalarExtension a f+scalarExtension a g := by
  apply Lp.ext
  have hf := (ae_restrict_iff' measurableSet_closedBall).mp (Lp.coeFn_add f g)
  filter_upwards [scalarExtension_ae a (f+g),scalarExtension_ae a f,scalarExtension_ae a g,
    Lp.coeFn_add (scalarExtension a f) (scalarExtension a g),hf] with x hfg he hf hadd hlocal
  rw [hfg,hadd]
  simp only [Pi.add_apply,he,hf]
  by_cases hx : x ∈ closedBall (0 : Space) a
  · simp only [indicator_of_mem hx]
    exact hlocal hx
  · simp only [indicator_of_not_mem hx,add_zero]

theorem scalarExtension_smul (a : ℝ) (z : ℂ) (f : ScalarBall a) :
    scalarExtension a (z • f)=z • scalarExtension a f := by
  apply Lp.ext
  have hf := (ae_restrict_iff' measurableSet_closedBall).mp (Lp.coeFn_smul z f)
  filter_upwards [scalarExtension_ae a (z • f),scalarExtension_ae a f,
    Lp.coeFn_smul z (scalarExtension a f),hf] with x hz he hs hlocal
  rw [hz,hs]
  simp only [Pi.smul_apply,smul_eq_mul,he]
  by_cases hx : x ∈ closedBall (0 : Space) a
  · simp only [indicator_of_mem hx]
    exact hlocal hx
  · simp only [indicator_of_not_mem hx,mul_zero]

theorem scalarExtension_norm (a : ℝ) (f : ScalarBall a) : ‖scalarExtension a f‖=‖f‖ := by
  simp only [Lp.norm_def]
  rw [eLpNorm_congr_ae (scalarExtension_ae a f),eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]

def scalar (a : ℝ) : ScalarBall a →L[ℂ] FourierL2.ScalarL2 :=
  ({toFun := scalarExtension a,map_add' := scalarExtension_add a,map_smul' := scalarExtension_smul a} :
    ScalarBall a →ₗ[ℂ] FourierL2.ScalarL2).mkContinuous 1 (fun f => by
      change ‖scalarExtension a f‖ ≤ 1*‖f‖
      rw [scalarExtension_norm,one_mul])

def vector (a : ℝ) : BallL2 a →L[ℂ] VectorFourier.VectorL2 :=
  ∑ j : Fin 3, (DynamicConvolution.insert j).comp
    ((scalar a).comp (PiLp.proj 2 (fun _ : Fin 3 => ScalarBall a) j))

theorem vector_coordinate (a : ℝ) (g : BallL2 a) (j : Fin 3) :
    NewtonL2.physicalCoordinate (vector a g) j=scalarExtension a (g j) := by
  change DynamicConvolution.component j (vector a g)=_
  simp only [vector,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply,map_sum,
    DynamicConvolution.component_insert]
  simp
  rfl

theorem vector_ae (a : ℝ) (g : BallL2 a) (j : Fin 3) :
    NewtonL2.physicalCoordinate (vector a g) j =ᵐ[volume]
      (closedBall (0 : Space) a).indicator (fun x => g j x) := by
  rw [vector_coordinate]
  exact scalarExtension_ae a (g j)

theorem vector_norm (a : ℝ) (g : BallL2 a) : ‖vector a g‖ ≤ 3*‖g‖ := by
  simp only [vector,ContinuousLinearMap.sum_apply,ContinuousLinearMap.comp_apply]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ j : Fin 3, ‖g j‖ := Finset.sum_le_sum (fun j _ => by
      apply (DynamicConvolution.insert_norm j _).trans_eq
      exact scalarExtension_norm a (g j))
    _ ≤ ∑ _j : Fin 3, ‖g‖ := Finset.sum_le_sum (fun j _ => PiLp.norm_apply_le g j)
    _ = _ := by simp only [Fin.sum_univ_three]; ring

def weighted (c : StaticCoefficient.Coefficient) (a : ℝ) : BallL2 a →L[ℂ] VectorFourier.VectorL2 :=
  (StaticCoefficient.sqrtMultiplier c).comp (vector a)

end OQ14.ConicalBallExtension

#print axioms OQ14.ConicalBallExtension.scalar_memLp
#print axioms OQ14.ConicalBallExtension.scalarExtension_ae
#print axioms OQ14.ConicalBallExtension.scalarExtension_add
#print axioms OQ14.ConicalBallExtension.scalarExtension_smul
#print axioms OQ14.ConicalBallExtension.scalarExtension_norm
#print axioms OQ14.ConicalBallExtension.vector_coordinate
#print axioms OQ14.ConicalBallExtension.vector_ae
#print axioms OQ14.ConicalBallExtension.vector_norm
