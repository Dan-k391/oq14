import Packet06PlacedSector
import Packet06SimpleCertificate

/-! Simple Schur data for the actual placed pencil in transported-sector coordinates. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06PlacedSchur
open Metric Packet06SectorOperator Packet06RankOneRepair Packet06ScalarSchur
open Packet06PlacedSector (pencil)

theorem pencil_analyticAt (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (z : ℂ) :
    AnalyticAt ℂ (pencil c R s hs a) z := by
  have he : pencil c R s hs a = fun v => Packet06MaterialSector.pencil c R (v/(s : ℂ)) :=
    funext (Packet06PlacedSector.pencil_formula c R hR hc s hs a)
  rw [he]
  apply (Packet06MaterialSector.pencil_analyticAt c R hR _).comp
  simpa only [div_eq_mul_inv] using
    (analyticAt_id.mul (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (s : ℂ)⁻¹) z))

theorem scalar_derivative (c : StaticCoefficient.Coefficient) (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (z : ℂ) (w : Sector) (ψ : Sector →L[ℂ] ℂ)
    (hu : IsUnit (repair (Packet06MaterialSector.pencil c R z) w ψ)) :
    deriv (fun v => scalar (pencil c R s hs a v) w ψ) ((s : ℂ)*z) =
      deriv (fun v => scalar (Packet06MaterialSector.pencil c R v) w ψ) z / (s : ℂ) := by
  have hs0 : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have he : (s : ℂ)*z/(s : ℂ)=z := by field_simp
  have hbase := (Packet06SchurAnalytic.scalar_analyticAt (Packet06MaterialSector.pencil c R)
    w ψ z (Packet06MaterialSector.pencil_analyticAt c R hR z) hu).differentiableAt.hasDerivAt
  have harg := (hasDerivAt_id ((s : ℂ)*z)).div_const (s : ℂ)
  have hb' : HasDerivAt (fun v => scalar (Packet06MaterialSector.pencil c R v) w ψ)
      (deriv (fun v => scalar (Packet06MaterialSector.pencil c R v) w ψ) z)
      (((s : ℂ)*z)/(s : ℂ)) := by simpa only [he] using hbase
  have hcomp := hb'.comp ((s : ℂ)*z) harg
  have hf : (fun v => scalar (pencil c R s hs a v) w ψ) =
      (fun v => scalar (Packet06MaterialSector.pencil c R (v/(s : ℂ))) w ψ) := by
    funext v
    rw [Packet06PlacedSector.pencil_formula c R hR hc s hs a v]
  rw [hf]
  simpa only [Function.comp_def,id_eq,one_div,div_eq_mul_inv,one_mul] using hcomp.deriv

theorem certified_schur (c : StaticCoefficient.Coefficient)
    (ha : Packet06MaterialSymmetry.Axial c) (hm : Packet06MaterialSymmetry.Meridional c)
    (R : ℝ) (hR : 0 ≤ R)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 R → c.value (VectorFourier.coordinateMap x)=0)
    (s : ℝ) (hs : 0 < s) (a : Maxwell.Space) (z : ℂ) (u : Sector)
    (hcert : Packet06SimpleCertificate.Certified c R z u) :
    ∃ (w : Sector) (ψ : Sector →L[ℂ] ℂ),
      IsUnit (repair (pencil c R s hs a ((s : ℂ)*z)) w ψ) ∧
      pencil c R s hs a ((s : ℂ)*z) u=0 ∧ ψ u=1 ∧
      deriv (fun v => scalar (pencil c R s hs a v) w ψ) ((s : ℂ)*z) ≠ 0 := by
  obtain ⟨w,ψ,hunit,hker,hψ,hder⟩ := hcert
  refine ⟨w,ψ,?_,?_,hψ,?_⟩
  · rwa [Packet06PlacedSector.pencil_scaled c R hR hc s hs a z]
  · rw [Packet06PlacedSector.pencil_scaled c R hR hc s hs a z]
    exact (Packet06MaterialSector.pencil_kernel_actual c ha hm R hR hc z u).mpr hker
  · rw [scalar_derivative c R hR hc s hs a z w ψ hunit]
    exact div_ne_zero hder (Complex.ofReal_ne_zero.mpr hs.ne')

end OQ14.Packet06PlacedSchur
#print axioms OQ14.Packet06PlacedSchur.pencil_analyticAt
#print axioms OQ14.Packet06PlacedSchur.scalar_derivative
#print axioms OQ14.Packet06PlacedSchur.certified_schur
