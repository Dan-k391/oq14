import Packet06ConeZeroRoot
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace OQ14.Packet06ConeRootLimit
open Filter Set OQ14.CapLegendreSeries OQ14.CapAngularShooting
open scoped Topology

theorem eigenvalue_tendsto_two (η ell : ℕ → ℝ) (t : ℝ)
    (ht0 : (1/2 : ℝ) ≤ t) (ht1 : t < 1)
    (hη : Tendsto η atTop (𝓝 0)) (hell : ∀ j, ell j ∈ Icc (0 : ℝ) 2)
    (hroot : ∀ j, determinant (η j) t (ell j) = 0) : Tendsto ell atTop (𝓝 2) := by
  have ht : 0 < t := by linarith
  have hp : |(1-t)/2| < 1 := by rw [abs_of_pos (by linarith)]; linarith
  have ho : |t| < 1 := by rw [abs_of_pos ht]; exact ht1
  have hD : ContinuousOn (fun a => determinant 0 t a) (Icc (0 : ℝ) 2) := determinant_continuousOn 0 t ht ht1
  have hP : ContinuousOn (fun a => poleD a t * odd a t) (Icc (0 : ℝ) 2) :=
    (poleD_parameter_continuousOn t hp).mul (odd_parameter_continuousOn t ho)
  apply isCompact_Icc.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hell)
  intro a ha hcluster
  obtain ⟨sub,hsub,hlim⟩ := TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster
  have hsubtop : Tendsto sub atTop atTop := hsub.tendsto_atTop
  have hηsub := hη.comp hsubtop
  have hwithin : Tendsto (ell ∘ sub) atTop (𝓝[Icc (0 : ℝ) 2] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim,Filter.Eventually.of_forall (fun j => hell (sub j))⟩
  have hDlim := (hD a ha).tendsto.comp hwithin
  have hPlim := (hP a ha).tendsto.comp hwithin
  have hfull := hDlim.add (hηsub.mul hPlim)
  have hfull' : Tendsto (fun j => determinant (η (sub j)) t (ell (sub j))) atTop
      (𝓝 (determinant 0 t a)) := by
    convert hfull using 1
    · funext j
      simp only [Function.comp_apply,determinant]
      ring
    · simp
  have hzero : determinant 0 t a = 0 := by
    apply tendsto_nhds_unique hfull'
    simpa only [hroot] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact Packet06ConeZeroRoot.zero_contrast_root_unique a t ha ht0 ht1 hzero
#print axioms OQ14.Packet06ConeRootLimit.eigenvalue_tendsto_two
end OQ14.Packet06ConeRootLimit
