import Packet06KernelMaxwell
import ComplexDyadicOutgoing

/-! One global physical electric representative, obtained by gluing the local
L² response to the actual outgoing dyadic field outside a containing ball. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace OQ14.Packet06GlobalField
open MeasureTheory Metric Filter Set DynamicSource
open StaticCoefficient (Coefficient)
open scoped Topology
abbrev V := VectorFourier.VectorL2

def electric (c : Coefficient) (z : ℂ) (S : ℝ) (u : V) : Maxwell.Field := fun x i =>
  if ‖x‖ ≤ S+1 then
    ComplexExteriorResponse.response c z S (S+1) u (VectorFourier.coordinateMap x) i
  else ComplexExteriorIntegral.field c z u x i

theorem electric_matches_response (c : Coefficient) (z : ℂ) (S T : ℝ) (hT : S+1 ≤ T) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) :
    (fun x => electric c z S u x i) =ᵐ[volume.restrict (closedBall 0 T)]
      fun x => ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i := by
  have hov := (ae_restrict_iff' measurableSet_closedBall).mp
    (Packet06LocalPencil.response_overlap c z S (S+1) T hT u hc i)
  have hext := ComplexExteriorIntegral.response_exterior_ae c z S T (S+1/2) (by linarith) u hc i
  filter_upwards [ae_restrict_of_ae hov,hext] with x hx he
  unfold electric
  split_ifs with hn
  · exact hx (by simpa only [mem_closedBall,dist_zero_right] using hn)
  · exact (he (by linarith)).symm

theorem electric_memLp_ball (c : Coefficient) (z : ℂ) (S T : ℝ) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) : MemLp (fun x => electric c z S u x i) 2 (volume.restrict (closedBall 0 T)) := by
  let U := max T (S+1)
  have he := electric_matches_response c z S U (le_max_right _ _) u hc i
  have heT := ae_restrict_of_ae_restrict_of_subset (closedBall_subset_closedBall (le_max_left T (S+1))) he
  have hrep := NewtonL2.physicalCoordinate_ae (ComplexExteriorResponse.response c z S U u) i
  have hmatch : (fun x => NewtonL2.physicalCoordinate (ComplexExteriorResponse.response c z S U u) i x)
      =ᵐ[volume.restrict (closedBall 0 T)] fun x => electric c z S u x i := by
    filter_upwards [ae_restrict_of_ae hrep,heT] with x hx he
    exact hx.trans he.symm
  exact ((Lp.memLp (NewtonL2.physicalCoordinate (ComplexExteriorResponse.response c z S U u) i)).restrict
    (s := closedBall 0 T)).ae_eq hmatch

theorem electric_test_integral (c : Coefficient) (z : ℂ) (S T : ℝ) (hT : S+1 ≤ T) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (i : Fin 3) (f : Test) (hf : tsupport (f.val : Maxwell.Space → ℂ) ⊆ closedBall 0 T)
    (a : Maxwell.Space → ℂ) :
    (∫ x : Maxwell.Space, a x * electric c z S u x i * f.val x) =
      ∫ x : Maxwell.Space, a x * ComplexExteriorResponse.response c z S T u (VectorFourier.coordinateMap x) i * f.val x := by
  apply integral_congr_ae
  have he := (ae_restrict_iff' measurableSet_closedBall).mp (electric_matches_response c z S T hT u hc i)
  filter_upwards [he] with x hx
  by_cases hmem : x ∈ closedBall (0 : Maxwell.Space) T
  · rw [hx hmem]
  · have hz : f.val x = 0 := image_eq_zero_of_nmem_tsupport (fun h => hmem (hf h))
    simp [hz]

theorem electric_outgoing (c : Coefficient) (z : ℂ) (S : ℝ) (hS : 0 ≤ S) (u : V)
    (hc : ∀ x : Maxwell.Space, x ∉ closedBall 0 S → c.value (VectorFourier.coordinateMap x) = 0)
    (n : Maxwell.Space) (hn : ‖n‖ = 1) (i : Fin 3) :
    Tendsto (fun r : ℝ => (r : ℂ)*Complex.exp (-Complex.I*z*r)*electric c z S u (r • n) i)
      atTop (𝓝 (ComplexDyadicOutgoing.amplitude c z u n i)) := by
  apply (ComplexDyadicOutgoing.field_far_limit c z S hS u hc n hn i).congr'
  filter_upwards [eventually_gt_atTop (S+1),eventually_gt_atTop (0 : ℝ)] with r hr hr0
  have hnorm : ‖r • n‖ = r := by simp [norm_smul,hn,abs_of_pos hr0]
  simp only [electric,hnorm,if_neg (not_le.mpr hr)]

end OQ14.Packet06GlobalField
#print axioms OQ14.Packet06GlobalField.electric_matches_response
#print axioms OQ14.Packet06GlobalField.electric_memLp_ball
#print axioms OQ14.Packet06GlobalField.electric_test_integral
#print axioms OQ14.Packet06GlobalField.electric_outgoing
