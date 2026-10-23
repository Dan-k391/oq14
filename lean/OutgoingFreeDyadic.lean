import OutgoingFiniteHelmholtz
import PointDyadicAngularLimit
import PointDyadicHelmholtz
import UniformHelmholtzEquation
import ScalarExteriorRellich

/-! Genuine far-exterior identification of the actual outgoing series with the translated free dyadic. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace OQ14.OutgoingFreeDyadic
open MeasureTheory Filter Set OQ14.Maxwell OQ14.SphereHarmonicBasis
open OQ14.VectorHarmonicNormalization OQ14.OutgoingSpatialSeries OQ14.OutgoingGeometricTail
open OQ14.ExteriorHelmholtz
open scoped Topology

theorem partial_sum_uniform (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    TendstoUniformlyOn (fun s : Finset PositiveIndex => fun x : Space => ∑ a∈s,term a x y i j)
      (fun x => electric y j x i) atTop {x : Space | R<‖x‖} :=
  tendstoUniformlyOn_tsum (majorant_summable b R hb)
    (fun a x hx => term_bound a b B R hb hB hscale hR hBR x y hx.le hy i j)

theorem actual_helmholtz (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    (∀ x : Space,R<‖x‖ → ContDiffAt ℝ (⊤ : ℕ∞) (fun z => electric y j z i) x) ∧
      (∀ x : Space,R<‖x‖ → laplacian (fun z => electric y j z i) x+electric y j x i=0) := by
  have hx0 (x : Space) (hx : R<‖x‖) : x≠0 := by
    intro he
    rw [he,norm_zero] at hx
    linarith
  have h := UniformHelmholtzEquation.limit_helmholtz atTop {x : Space | R<‖x‖}
    (isOpen_lt continuous_const continuous_norm) 1
    (fun s : Finset PositiveIndex => fun x => ∑ a∈s,term a x y i j) (fun x => electric y j x i)
    (fun s x hx => OutgoingFiniteHelmholtz.partial_sum_smooth s y i j x (hx0 x hx))
    (fun s x hx => by simpa only [Complex.ofReal_one,one_pow,one_mul] using
      OutgoingFiniteHelmholtz.partial_sum_helmholtz s y i j x (hx0 x hx))
    (partial_sum_uniform b B R hb hB hscale hR hBR y hy i j)
  simpa only [Complex.ofReal_one,one_pow,one_mul] using h

theorem actual_free_dyadic (b B R : ℝ) (hb : 0≤b) (hB : 0≤B)
    (hscale : HarmonicSpatialMajorant.degreeScale 2 b≤B) (hR : 2≤R)
    (hBR : 2*(B*AngularExteriorBounds.base)≤R)
    (y : Space) (hy : ‖y‖≤b) (i j : Fin 3) :
    ∀ x : Space,max R ‖y‖<‖x‖ → electric y j x i=DyadicKernel.dyadic 1 (x-y) i j := by
  have h := actual_helmholtz b B R hb hB hscale hR hBR y hy i j
  have hxy (x : Space) (hx : max R ‖y‖<‖x‖) : x≠y := by
    intro he
    rw [he] at hx
    exact (not_lt_of_ge (le_max_right R ‖y‖)) hx
  have hdiff : ∀ x : Space,max R ‖y‖<‖x‖ →
      ContDiffAt ℝ (⊤ : ℕ∞) (fun z => electric y j z i-DyadicKernel.dyadic 1 (z-y) i j) x :=
    fun x hx => (h.1 x ((le_max_left _ _).trans_lt hx)).sub
      (PointDyadicHelmholtz.translated_smooth y x (hxy x hx) i j)
  have hzero := ScalarExteriorRellich.zero_of_surface_mass (max R ‖y‖)
    (le_trans (by linarith : 0≤R) (le_max_left _ _)) 1 (by norm_num)
    (fun x => electric y j x i-DyadicKernel.dyadic 1 (x-y) i j)
    (fun x hx => (hdiff x hx).contDiffWithinAt)
    (fun x hx => by
      rw [DebyeCalculus.laplacian_sub _ _ x (h.1 x ((le_max_left _ _).trans_lt hx))
        (PointDyadicHelmholtz.translated_smooth y x (hxy x hx) i j)]
      have hE := h.2 x ((le_max_left _ _).trans_lt hx)
      have hD := PointDyadicHelmholtz.translated_helmholtz y x (hxy x hx) i j
      simp only [Complex.ofReal_one,one_pow,one_mul]
      linear_combination hE-hD)
    (PointDyadicAngularLimit.difference_surface_mass_zero b B R hb hB hscale hR hBR y hy i j)
  intro x hx
  exact sub_eq_zero.mp (hzero x hx)

end OQ14.OutgoingFreeDyadic
#print axioms OQ14.OutgoingFreeDyadic.partial_sum_uniform
#print axioms OQ14.OutgoingFreeDyadic.actual_helmholtz
#print axioms OQ14.OutgoingFreeDyadic.actual_free_dyadic
