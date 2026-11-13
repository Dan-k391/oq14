import Packet06AnnularLowerBound
import ConicalSeparatedRetention
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06StrictAnnulus
open MeasureTheory Metric Set Filter
open scoped Topology

theorem choose_test (t K M α b R₀ : ℝ) (ht : 0 < t) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hα : 0 < α) (hb : 0 < b) (hR₀ : 0 < R₀)
    (f : ℝ → ℂ) (hf : Continuous f) (A : ℂ) (hA : A ≠ 0)
    (hclose : ∀ r : ℝ, |r| < R₀ → ‖f r-A‖ < ‖A‖/2) :
    ∃ (ζ : ℝ → ℝ) (_hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (_hc : HasCompactSupport ζ),
      tsupport ζ ⊆ Ioo (0 : ℝ) b ∧
      K*M*(∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r|) <
        ‖(t : ℂ)*∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*f r‖ := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have htarget : 0 < t*‖A‖/2 := by positivity
  have hlim : Tendsto (fun r : ℝ => K*M*r^α) (𝓝 0) (𝓝 0) := by
    have hh := ((Real.continuous_rpow_const hα.le).continuousAt (x := (0 : ℝ)).tendsto).const_mul (K*M)
    simpa [Real.zero_rpow hα.ne'] using hh
  have hevent := (tendsto_order.mp hlim).2 (t*‖A‖/2) htarget
  obtain ⟨δ,hδ,hδbound⟩ := Metric.eventually_nhds_iff.mp hevent
  let R := min (min b R₀) δ / 2
  have hR : 0 < R := by dsimp [R]; positivity
  have hRb : R < b := by dsimp [R]; have := min_le_left (min b R₀) δ; have := min_le_left b R₀; linarith
  have hRR : R < R₀ := by dsimp [R]; have := min_le_left (min b R₀) δ; have := min_le_right b R₀; linarith
  have hRδ : R < δ := by dsimp [R]; have := min_le_right (min b R₀) δ; linarith
  have hsmall : K*M*R^α < t*‖A‖/2 := hδbound (by simpa [Real.dist_eq,abs_of_pos hR] using hRδ)
  let ζ : ℝ → ℝ := ConicalSeparatedRetention.annularBump R hR
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := (ConicalSeparatedRetention.annularBump R hR).contDiff
  have hc : HasCompactSupport ζ := (ConicalSeparatedRetention.annularBump R hR).hasCompactSupport
  have hs : tsupport ζ ⊆ Ioo (0 : ℝ) R := ConicalSeparatedRetention.annularBump_support R hR
  have hn : ∀ r, 0 ≤ ζ r := fun r => (ConicalSeparatedRetention.annularBump R hR).nonneg
  let w : ℝ → ℝ := fun r => r^2*ζ r
  have hw : Continuous w := (continuous_id.pow 2).mul hζ.continuous
  have hwc : HasCompactSupport w := hc.mul_left
  have hnon : ∀ r, 0 ≤ w r := fun r => mul_nonneg (sq_nonneg _) (hn r)
  have hwpos : w (R/2) ≠ 0 := by
    have hv : ζ (R/2)=1 := (ConicalSeparatedRetention.annularBump R hR).one_of_mem_closedBall (by
      simp only [mem_closedBall,dist_self]; exact (ConicalSeparatedRetention.annularBump R hR).rIn_pos.le)
    dsimp [w]
    rw [hv,mul_one]
    exact (sq_pos_of_pos (by linarith : 0 < R/2)).ne'
  have hIpos : 0 < ∫ r, w r := hw.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hwc hnon hwpos
  have hzero (r : ℝ) (hr : r ∉ Ioi (0 : ℝ)) : ζ r = 0 :=
    image_eq_zero_of_nmem_tsupport (fun hh => hr (hs hh).1)
  have hIeq : (∫ r in Ioi (0 : ℝ), r^2*ζ r) = ∫ r, w r := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    simp [hzero r hr]
  have hclose' : ∀ r, w r ≠ 0 → ‖f r-A‖ ≤ ‖A‖/2 := by
    intro r hr
    have hz : ζ r ≠ 0 := by intro hz; apply hr; simp [w,hz]
    have hrr := hs (subset_tsupport ζ hz)
    exact (hclose r (by rw [abs_of_pos hrr.1]; exact hrr.2.trans hRR)).le
  have hlower := Packet06AnnularLowerBound.lower w hw hwc hnon f hf A hclose'
  have hprod : (∫ r, (w r : ℂ)*f r) =
      ∫ r in Ioi (0 : ℝ), (r^2 : ℂ)*(ζ r : ℂ)*f r := by
    have heq : (fun r : ℝ => (w r : ℂ)*f r) = fun r : ℝ => (r^2 : ℂ)*(ζ r : ℂ)*f r := by
      funext r
      simp only [w,Complex.ofReal_mul,Complex.ofReal_pow]
    rw [heq]
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro r hr
    simp [hzero r hr]
  have hweight := Packet06AnnularLowerBound.relative_weight ζ hζ.continuous hc R hs hR.le α hα.le
  have hweight' : (∫ r in Ioi (0 : ℝ), r^(2+α)*|ζ r|) ≤ R^α*(∫ r, w r) := by
    simpa only [abs_of_nonneg (hn _),hIeq] using hweight
  refine ⟨ζ,hζ,hc,hs.trans (Ioo_subset_Ioo_right hRb.le),?_⟩
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  have hlt : K*M*(R^α*(∫ r, w r)) < (t*‖A‖/2)*(∫ r, w r) :=
    by simpa only [mul_assoc] using mul_lt_mul_of_pos_right hsmall hIpos
  have hweight'' := mul_le_mul_of_nonneg_left hweight' (mul_nonneg hK hM)
  rw [hprod] at hlower
  nlinarith
#print axioms OQ14.Packet06StrictAnnulus.choose_test
end OQ14.Packet06StrictAnnulus
