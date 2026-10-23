import ConicalBallExtension

/-! Genuine bounded physical restriction from global vector L2 to ball L2. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.ConicalBallRestriction
open MeasureTheory Set Metric OQ14.ConicalRungeBall
open scoped Topology
abbrev Space := Maxwell.Space

def scalarRestriction (a : ℝ) (f : FourierL2.ScalarL2) : ScalarBall a :=
  ((Lp.memLp f).mono_measure Measure.restrict_le_self).toLp (f : Space → ℂ)

theorem scalarRestriction_ae (a : ℝ) (f : FourierL2.ScalarL2) :
    scalarRestriction a f =ᵐ[volume.restrict (closedBall (0 : Space) a)] (f : Space → ℂ) :=
  ((Lp.memLp f).mono_measure Measure.restrict_le_self).coeFn_toLp

theorem scalarRestriction_add (a : ℝ) (f g : FourierL2.ScalarL2) :
    scalarRestriction a (f+g)=scalarRestriction a f+scalarRestriction a g := by
  apply Lp.ext
  filter_upwards [scalarRestriction_ae a (f+g),scalarRestriction_ae a f,scalarRestriction_ae a g,
    Lp.coeFn_add (scalarRestriction a f) (scalarRestriction a g),ae_restrict_of_ae (Lp.coeFn_add f g)]
      with x hfg hf hg hadd hglobal
  rw [hfg,hadd]
  simp only [Pi.add_apply,hf,hg]
  exact hglobal

theorem scalarRestriction_smul (a : ℝ) (z : ℂ) (f : FourierL2.ScalarL2) :
    scalarRestriction a (z • f)=z • scalarRestriction a f := by
  apply Lp.ext
  filter_upwards [scalarRestriction_ae a (z • f),scalarRestriction_ae a f,
    Lp.coeFn_smul z (scalarRestriction a f),ae_restrict_of_ae (Lp.coeFn_smul z f)] with x hz hf hs hglobal
  rw [hz,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hf]
  exact hglobal

theorem scalarRestriction_norm (a : ℝ) (f : FourierL2.ScalarL2) : ‖scalarRestriction a f‖ ≤ ‖f‖ := by
  simp only [Lp.norm_def]
  rw [eLpNorm_congr_ae (scalarRestriction_ae a f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_mono_measure f Measure.restrict_le_self)

def scalar (a : ℝ) : FourierL2.ScalarL2 →L[ℂ] ScalarBall a :=
  ({toFun := scalarRestriction a,map_add' := scalarRestriction_add a,map_smul' := scalarRestriction_smul a} :
    FourierL2.ScalarL2 →ₗ[ℂ] ScalarBall a).mkContinuous 1 (fun f => by
      change ‖scalarRestriction a f‖ ≤ 1*‖f‖
      simpa only [one_mul] using scalarRestriction_norm a f)

def vector (a : ℝ) : VectorFourier.VectorL2 →L[ℂ] BallL2 a :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ScalarBall a)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => (scalar a).comp (DynamicConvolution.component j)))

theorem vector_ae (a : ℝ) (F : VectorFourier.VectorL2) (j : Fin 3) :
    (vector a F j : Space → ℂ) =ᵐ[volume.restrict (closedBall (0 : Space) a)]
      (NewtonL2.physicalCoordinate F j : Space → ℂ) :=
  scalarRestriction_ae a _

theorem extension_leftInverse (a : ℝ) (g : BallL2 a) : vector a (ConicalBallExtension.vector a g)=g := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [vector_ae a (ConicalBallExtension.vector a g) j,
    ae_restrict_of_ae (ConicalBallExtension.vector_ae a g j),
    ae_restrict_mem measurableSet_closedBall] with x hr he hx
  rw [hr,he,indicator_of_mem hx]

end OQ14.ConicalBallRestriction

#print axioms OQ14.ConicalBallRestriction.scalarRestriction_ae
#print axioms OQ14.ConicalBallRestriction.scalarRestriction_add
#print axioms OQ14.ConicalBallRestriction.scalarRestriction_smul
#print axioms OQ14.ConicalBallRestriction.scalarRestriction_norm
#print axioms OQ14.ConicalBallRestriction.vector_ae
#print axioms OQ14.ConicalBallRestriction.extension_leftInverse
