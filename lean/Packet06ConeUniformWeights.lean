import Packet06ConeHolderMoments
import Packet06ConeProfileBounds
import Packet06ConeTangentL2
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeUniformWeights
open Set OQ14.Maxwell OQ14.AngularPower OQ14.ConicalMomentWeights OQ14.SphereCapH1

theorem uniform_weights (t D : ℝ) (ht : 0 < t) (ht1 : t < 1) (hD : 0 ≤ D) :
    ∃ C ≥ (0 : ℝ), ∀ a ∈ Icc (0 : ℝ) 2, ∀ d ∈ Icc (0 : ℝ) D,
      ∀ (i : Fin 3) (n : Sphere), ‖radial a d t i n‖ ≤ C ∧ ‖tangent a d t i n‖ ≤ C := by
  obtain ⟨K,hK,hb⟩ := Packet06ConeProfileBounds.profile_slope_uniform t ht ht1
  refine ⟨(1+D)*K, mul_nonneg (by linarith) hK, ?_⟩
  intro a ha d hd i n
  have hc : ‖CapSturmLiouville.coefficient d t ((n : Space) 2)‖ ≤ 1+D := by
    unfold CapSturmLiouville.coefficient
    split_ifs <;> simp only [Real.norm_eq_abs,abs_of_nonneg (by linarith [hd.1] : 0 ≤ (1 : ℝ)),
      abs_of_nonneg (by linarith [hd.1] : 0 ≤ 1+d)] <;> linarith [hd.2]
  have hp : ‖field a t n‖ ≤ K := by
    simpa [field,Real.norm_eq_abs] using (hb a ha ((n : Space) 2) (SphereCapWeak.coordinate_range n)).1
  have hs : ‖CapSturmLiouville.slope a t ((n : Space) 2)‖ ≤ K := by
    simpa [Real.norm_eq_abs] using (hb a ha ((n : Space) 2) (SphereCapWeak.coordinate_range n)).2
  have hn : ‖(n : Space) i‖ ≤ 1 := (PiLp.norm_apply_le _ i).trans_eq (sphere_norm n)
  have hg : ‖gradient a t n i‖ ≤ K := by
    have htangent := SphereCapH1.tangent_norm_le n
    calc
      _ ≤ ‖gradient a t n‖ := PiLp.norm_apply_le _ i
      _ = ‖CapSturmLiouville.slope a t ((n : Space) 2)‖ * ‖basis 2-((n : Space) 2) • (n : Space)‖ := by
        rw [SphereCapH1.gradient,norm_smul]
      _ ≤ K*1 := mul_le_mul hs htangent (norm_nonneg _) hK
      _ = K := by ring
  constructor
  · simp only [radial,scalar,ConicalRadialDivergence.angularWeight,Complex.ofReal_mul,norm_mul,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul hc hp (norm_nonneg _) (by linarith)) (norm_nonneg _)).trans
      (by nlinarith [mul_nonneg (show 0 ≤ 1+D by linarith) hK])
  · simp only [tangent,Complex.norm_real,norm_mul]
    exact mul_le_mul hc hg (norm_nonneg _) (by linarith)
#print axioms OQ14.Packet06ConeUniformWeights.uniform_weights
end OQ14.Packet06ConeUniformWeights
