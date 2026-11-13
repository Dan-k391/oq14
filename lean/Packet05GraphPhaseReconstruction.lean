import Packet05PhysicalPhaseBranches
import Packet05GraphL2Constitutive

/-! Exact graph-algebra identification of the transmission variables with
the physical electric field and its continuous correction on either phase. -/
noncomputable section
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
namespace OQ14.Packet05GraphPhaseReconstruction
open MeasureTheory Set OQ14.Maxwell OQ14.WeakCurl OQ14.WeakPoynting OQ14.WeakGreen
  OQ14.DivCurlCompact OQ14.ConicalJunctionPhysical OQ14.Packet05GraphPullback
  OQ14.Packet05GraphH1Pullback OQ14.Packet05GraphGradientValues OQ14.Packet05GraphSlopeMultiplier
  OQ14.Packet05GraphWeakDivergence OQ14.Packet05GraphL2Constitutive
  OQ14.Packet05GraphFluxExtension OQ14.Packet05ScalarDielectricFlux OQ14.Packet05FlatWeight
  OQ14.Packet05TensorCommutator OQ14.Packet05PhysicalPhaseBranches
abbrev Plane := OQ14.ConicalSmoothJunction.Plane

theorem graph_phase_reconstruction (g : Plane → ℝ) (hg : ContDiff ℝ 2 g)
    (G Q : L2Vector) (B : Fin 3 → ℝ) (hB : ∀ i x, ‖slopeC g i x‖ ≤ B i)
    (A : Fin 3 → Fin 3 → Test) (d : ℝ) (hd : 0 ≤ d)
    (T : Set Maxwell.Space) (hT : IsOpen T) (ε : ℂ) (hε : ε ≠ 0)
    (hweight : ∀ x ∈ T, weight d x = ε)
    (hmetric : ∀ x ∈ T, ∀ j k, (A j k).function x =
      (Packet05GraphChartMatrix.metric (Packet05GraphSlope.slope g 0 x)
        (Packet05GraphSlope.slope g 1 x) j k : ℂ))
    (w : Fin 3 → Maxwell.Space → ℂ) (hw : ∀ j, Continuous (w j))
    (hQ : ∀ j, (fun x => pullback g hg.continuous (Q j) x) =ᵐ[volume.restrict T] w j)
    (f0 f1 fn : Maxwell.Space → ℂ) (hf0 : Continuous f0) (hf1 : Continuous f1) (hfn : Continuous fn)
    (h0 : (fun x => pulledGradient g hg G B hB 0 x) =ᵐ[volume.restrict T] f0)
    (h1 : (fun x => pulledGradient g hg G B hB 1 x) =ᵐ[volume.restrict T] f1)
    (hn : (fun x => (flux A (pulledGradient g hg G B hB) d hd 2 -
      (-mulWeight d hd (transformedFlux g hg Q B hB 2)) : L2Scalar) x) =ᵐ[volume.restrict T] fn) :
    ∃ reps : Fin 3 → Maxwell.Space → ℂ, (∀ j, Continuous (reps j)) ∧
      ∀ j, (fun x => pullback g hg.continuous (G j) x + pullback g hg.continuous (Q j) x)
        =ᵐ[volume.restrict T] reps j := by
  let C := pulledGradient g hg G B hB
  let N : L2Scalar := flux A C d hd 2-(-mulWeight d hd (transformedFlux g hg Q B hB 2))
  let a := Packet05GraphSlope.slope g 0
  let b := Packet05GraphSlope.slope g 1
  have ha : Continuous a := (Packet05GraphSlope.slope_contDiff g hg 0).continuous
  have hb : Continuous b := (Packet05GraphSlope.slope_contDiff g hg 1).continuous
  have hC0 := ae_restrict_of_ae (s := T) (pulledGradient_ae g hg G B hB 0)
  have hC1 := ae_restrict_of_ae (s := T) (pulledGradient_ae g hg G B hB 1)
  have hC2 := ae_restrict_of_ae (s := T) (pulledGradient_ae g hg G B hB 2)
  have hflux : ∀ᵐ x ∂volume.restrict T, N x = ε *
      (-(a x : ℂ)*C 0 x-(b x : ℂ)*C 1 x + ((1+(a x)^2+(b x)^2 : ℝ) : ℂ)*C 2 x +
        w 2 x-(a x : ℂ)*w 0 x-(b x : ℂ)*w 1 x) := by
    filter_upwards [ae_restrict_of_ae (matrixField_ae A C 2),
      ae_restrict_of_ae (mulWeight_ae d hd (matrixField A C 2)),
      ae_restrict_of_ae (mulWeight_ae d hd (transformedFlux g hg Q B hB 2)),
      ae_restrict_of_ae (transformedFlux_ae g hg Q B hB 2),
      ae_restrict_of_ae (Lp.coeFn_neg (mulWeight d hd (transformedFlux g hg Q B hB 2))),
      ae_restrict_of_ae (Lp.coeFn_sub (flux A C d hd 2) (-mulWeight d hd (transformedFlux g hg Q B hB 2))),
      hQ 0,hQ 1,hQ 2,ae_restrict_mem hT.measurableSet] with x hm hw hq hp hneg hn hq0 hq1 hq2 hx
    change (flux A C d hd 2-(-mulWeight d hd (transformedFlux g hg Q B hB 2)) : L2Scalar) x = _
    rw [hn]
    simp only [Pi.sub_apply]
    change (mulWeight d hd (matrixField A C 2)) x -
      (-mulWeight d hd (transformedFlux g hg Q B hB 2) : L2Scalar) x = _
    rw [hw,hneg]
    simp only [Pi.neg_apply]
    rw [hq,hp,if_pos rfl,hweight x hx,hm]
    simp only [Fin.sum_univ_three,hmetric x hx,Packet05GraphChartMatrix.metric,
      Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,
      Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_pow]
    rw [hq0,hq1,hq2]
    simp [Packet05GraphChartMatrix.metric, slopeC,a,b]
    ring
  have he0 : ∀ᵐ x ∂volume.restrict T,
      pullback g hg.continuous (G 0) x + pullback g hg.continuous (Q 0) x =
        C 0 x-(a x : ℂ)*C 2 x+w 0 x := by
    filter_upwards [hC0,hC2,hQ 0] with x h0 h2 hw
    rw [h0,h2,normal_slope_zero g hg x,hw]
    simp only [zero_mul,add_zero,slopeC]
    ring
  have he1 : ∀ᵐ x ∂volume.restrict T,
      pullback g hg.continuous (G 1) x + pullback g hg.continuous (Q 1) x =
        C 1 x-(b x : ℂ)*C 2 x+w 1 x := by
    filter_upwards [hC1,hC2,hQ 1] with x h1 h2 hw
    rw [h1,h2,normal_slope_zero g hg x,hw]
    simp only [zero_mul,add_zero,slopeC]
    ring
  have he2 : ∀ᵐ x ∂volume.restrict T,
      pullback g hg.continuous (G 2) x + pullback g hg.continuous (Q 2) x = C 2 x+w 2 x := by
    filter_upwards [hC2,hQ 2] with x h2 hw
    rw [h2,normal_slope_zero g hg x,hw]
    simp
  exact physical_phase_branches T (fun x j => pullback g hg.continuous (G j) x+
    pullback g hg.continuous (Q j) x) ε hε a b ha hb (C 0) (C 1) (C 2) N
    (w 0) (w 1) (w 2) f0 f1 fn hf0 hf1 hfn (hw 0) (hw 1) (hw 2) h0 h1 hn hflux he0 he1 he2

end OQ14.Packet05GraphPhaseReconstruction
#print axioms OQ14.Packet05GraphPhaseReconstruction.graph_phase_reconstruction
