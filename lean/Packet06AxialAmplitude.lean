import Packet06PlacedMaterialField
import Packet06SectorOperator
import Packet06MaterialSymmetry
import FiniteMixedScaledFlux

/-! The physical Euclidean amplitude of the actual modal response is axial a.e.
on the positive material region. This uses the exact kernel equation. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06AxialAmplitude
open MeasureTheory Metric Maxwell ModalAxialRotation
abbrev V := VectorFourier.VectorL2

theorem rotation_energy (θ : ℝ) (v : Maxwell.Vector) : energy (vector θ v)=energy v := by
  simp only [energy,vector,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.head_cons,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,
    Complex.add_im,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im]
  simp only [zero_mul,sub_zero,zero_add]
  simp only [Matrix.vecHead,Matrix.vecTail,Function.comp_def]
  simp only [Matrix.cons_val_succ,Matrix.cons_val_zero]
  linear_combination ((v 0).re^2+(v 0).im^2+(v 1).re^2+(v 1).im^2)*
    (Real.cos_sq_add_sin_sq θ)

theorem sector_energy_ae (u : Packet06SectorOperator.Sector) (θ : ℝ) :
    ∀ᵐ x : Space, energy (fun i => (u : V) (VectorFourier.coordinateMap (rotation θ x)) i) =
      energy (fun i => (u : V) (VectorFourier.coordinateMap x) i) := by
  have hax : action (-θ) (u : V)=(u : V) := by
    have h : (u : V) ∈ axialSector := u.property.1
    simp only [axialSector,Submodule.mem_iInf,LinearMap.mem_ker,
      ContinuousLinearMap.sub_apply,ContinuousLinearMap.one_apply,sub_eq_zero] at h
    exact h (-θ)
  have he := ae_all_iff.mpr (fun i => action_ae (-θ) (u : V) i)
  filter_upwards [he] with x hx
  have hv : (fun i => (u : V) (VectorFourier.coordinateMap x) i) =
      vector (-θ) (fun i => (u : V) (VectorFourier.coordinateMap (rotation θ x)) i) := by
    funext i
    have hh := hx i
    rw [hax] at hh
    simpa only [neg_neg, matrix_vector] using hh
  rw [hv,rotation_energy]

theorem response_energy_ae (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (z : ℂ) (R T : ℝ) (hRT : R ≤ T)
    (u : Packet06SectorOperator.Sector)
    (hc : ∀ x : Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (hu : ComplexConvolutionAnalytic.volumeBlock c z R u=0) (θ : ℝ) :
    ∀ᵐ x : Space, c.value (VectorFourier.coordinateMap x) ≠ 0 →
      energy (fun i => Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap (rotation θ x)) i) =
      energy (fun i => Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap x) i) := by
  have hrep := ae_all_iff.mpr (fun i => Packet06PlacedMaterialField.kernel_weighted_response_ae c z R T hRT u hc hu i)
  have hrot := (rotation θ).measurePreserving.quasiMeasurePreserving.ae hrep
  filter_upwards [hrep,hrot,sector_energy_ae u θ] with x hx hr he hχ
  let E : Maxwell.Vector := fun i => Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap x) i
  let Er : Maxwell.Vector := fun i => Packet06LocalPencil.response c z R T u (VectorFourier.coordinateMap (rotation θ x)) i
  have hv : (fun i => (u : V) (VectorFourier.coordinateMap x) i) =
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) • E := funext hx
  have hvr : (fun i => (u : V) (VectorFourier.coordinateMap (rotation θ x)) i) =
      (Real.sqrt (c.value (VectorFourier.coordinateMap x)) : ℂ) • Er := by
    funext i
    simpa only [ha θ x] using hr i
  rw [hv,hvr,FiniteMixedScaledFlux.energy_smul_vector,FiniteMixedScaledFlux.energy_smul_vector,
    Complex.normSq_ofReal,Real.mul_self_sqrt (c.nonnegative _)] at he
  exact mul_left_cancel₀ hχ he

end OQ14.Packet06AxialAmplitude
#print axioms OQ14.Packet06AxialAmplitude.rotation_energy
#print axioms OQ14.Packet06AxialAmplitude.sector_energy_ae
#print axioms OQ14.Packet06AxialAmplitude.response_energy_ae
